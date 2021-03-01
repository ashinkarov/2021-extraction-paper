open import Data.Nat as N using (ℕ; zero; suc; _<_; _≤_; _>_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties as N
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Vec.Properties as V
open import Data.Fin as F using (Fin; zero; suc)
import      Data.Fin.Properties as F
open import Data.List as L using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Nat.Properties
import      Data.Nat.DivMod as N
open import Data.Bool using (Bool; true; false)
open import Data.Product renaming (_×_ to _⊗_)

open import Relation.Binary.PropositionalEquality -- using (≡-Reasoning; _≡_; refl; cong; sym; subst; subst₂) -- (Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import Function
open import Reflection
open import Level using () renaming (zero to ℓ0; suc to lsuc)

open import Array.Base
open import Array.Properties

open import Agda.Builtin.Float


data dy-args : ∀ m n → Vec ℕ m → Vec ℕ n → Set where
  n-n : ∀ {n s} → dy-args n n s  s
  n-0 : ∀ {n s} → dy-args n 0 s  []
  0-n : ∀ {n s} → dy-args 0 n [] s

dy-args-dim : ∀ {m n sx sy} → dy-args m n sx sy → ℕ
dy-args-dim {m}    n-n = m
dy-args-dim {m}    n-0 = m
dy-args-dim {m}{n} 0-n = n

dy-args-shp : ∀ {m n sx sy} → (dy : dy-args m n sx sy) → Vec ℕ (dy-args-dim dy)
dy-args-shp {m}{n}{sx}     n-n = sx
dy-args-shp {m}{n}{sx}     n-0 = sx
dy-args-shp {m}{n}{sx}{sy} 0-n = sy

dy-args-ok? : Term → TC ⊤
dy-args-ok? hole = do
  goal ← inferType hole
  def (quote dy-args) (vArg m ∷ vArg n ∷ vArg sx ∷ vArg sy ∷ []) ← reduce goal
    where _ → typeError (strErr "expected dy-args expression in goal, found:" ∷ termErr goal ∷ [])
  reduce m >>= λ where
    (lit (nat 0)) → unify hole (con (quote 0-n) [])
    (meta id _) → blockOnMeta id
    m → reduce n >>= λ where
      (lit (nat 0)) → unify hole (con (quote n-0) [])
      (meta id _) → blockOnMeta id
      n → do
        catchTC
          (unify m n)
          (typeError (strErr "no valid dy-args found for goal: " ∷ termErr goal ∷ []))
        -- XXX we could further check that sx and sy unify as well, however, this would
        --     fail later if they don't.
        unify hole (con (quote n-n) [])

dy-type : ∀ a → Set a → Set a
dy-type a X = ∀ {m n sx sy} {@(tactic dy-args-ok?) args : dy-args m n sx sy}
              → Ar X m sx → Ar X n sy → Ar X _ (dy-args-shp args)

lift′ : ∀ {a}{X : Set a} → (_⊕_ : X → X → X) → dy-type a X
lift′ _⊕_ {args = n-n} (imap a) (imap b) = imap λ iv → a iv ⊕ b iv
lift′ _⊕_ {args = n-0} (imap a) (imap b) = imap λ iv → a iv ⊕ b []
lift′ _⊕_ {args = 0-n} (imap a) (imap b) = imap λ iv → a [] ⊕ b iv


Scal : ∀ {a} → Set a → Set a
Scal X = Ar X 0 []

--scal : ∀ {a}{X : Set a} → X → Scal X
--scal = cst

--unscal : ∀ {a}{X : Set a} → Scal X → X
--unscal (imap f) = f []


--module reduce-split where
--  split-thm : ∀ m n → (m N.⊓ n) N.+ (n N.∸ m) ≡ n
--  split-thm zero    n       = refl
--  split-thm (suc m) zero    = refl
--  split-thm (suc m) (suc n) = cong suc (split-thm m n)
--
--  {-# REWRITE split-thm #-}
--
--  split : ∀ {X : Set}{n} → (m : ℕ) → (xy : Vec X n)
--        → ∃₂ λ (x : Vec X (m N.⊓ n)) (y : Vec X (n N.∸ m)) → x V.++ y ≡ xy
--  split zero xy = [] , xy , refl
--  split {n = zero}  (suc m) xy = [] , xy , refl
--  split {X = X}{n = suc n} (suc m) (x ∷ xy) with split m xy
--  ... | xs , ys , refl = x ∷ xs , ys , refl
--
--  split-axis : ∀ m → (k : Fin m) → ∃₂ λ l r → l N.+ 1 N.+ r ≡ m
--  split-axis zero ()
--  split-axis (suc m) zero    = 0 , m , refl
--  split-axis (suc m) (suc k) with split-axis m k
--  ... | l' , r' , refl = suc l' , r' , refl
--
--
--  split-vec : ∀ {l r}{X : Set} → (xyz : Vec X (l N.+ 1 N.+ r))
--            → Σ[ x ∈ Vec X l ] Σ[ y ∈ Vec X 1 ] Σ[ z ∈ Vec X r ] ((x V.++ y) V.++ z ≡ xyz)
--  split-vec {zero}  {r} (h ∷ t) = [] , (h ∷ []) , t , refl
--  split-vec {suc l} {r} (h ∷ t) with split-vec {l = l} t
--  ... | l' , m' , r' , refl = h ∷ l' , m' , r' , refl



data SVup (X : Set) : Set → (d : ℕ) → (sh : Vec ℕ d) → Set where
  instance
    scal : SVup X X 0 []
    vect : ∀ {n} → SVup X (Vec X n) 1 (n ∷ [])
    arry : ∀ {d s} → SVup X (Ar X d s) d s
    -- XXX do we need the id case for arrays themselves?

infixr 30 ▴_
▴_ : ∀ {X A d s}{{t : SVup X A d s}} → A → Ar X d s
▴_ ⦃ t = scal ⦄ a = cst a --imap λ _ → a
▴_ ⦃ t = vect ⦄ a = imap λ iv → V.lookup a $ ix-lookup iv zero --imap λ where (i ∷ []) → V.lookup a i
▴_ ⦃ t = arry ⦄ a = a

{-
data SVdown (X : Set) : (d : ℕ) → (sh : Vec ℕ d) → Set → Set where
  instance
    scal : SVdown X 0 [] X
    vect : ∀ {n} → SVdown X 1 (n ∷ []) (Vec X n)
    -- XXX do we need the id case for arrays themselves?
-}

infixr 30 ▾_
▾_ : ∀ {X A d s}{{t : SVup X A d s}} → Ar X d s → A
▾_ ⦃ t = scal ⦄ (imap a) = a []
▾_ ⦃ t = vect ⦄ (imap a) = V.tabulate λ i → a $ i ∷ []
▾_ ⦃ t = arry ⦄ a = a

-- FIXME These cases are missing
-- Ar X 1 [n] + Vec X 0
-- Ar X 1 [n] + Vec X 1
-- Ar X 1 [n] + Vec X n

-- FIXME we should allow for different types of lhs and rhs and result,
--       e.g. replicate : ℕ → Char → String (not critical, but would be nice).
-- FIXME we can add the cases when indices are added with scalars/arrays/vectors.
--
-- Simplify handling concatenation of `Prog`s and `String`s
data DyScalVec (X : Set) : Set → Set → (d : ℕ) → (sh : Vec ℕ d) → Set where
  instance
    s-s :           DyScalVec X X X 0 []
    s-v : ∀ {n} →   DyScalVec X X (Vec X n) 1 (n ∷ [])
    s-a : ∀ {d s} → DyScalVec X X (Ar X d s) d s
    v-s : ∀ {n} →   DyScalVec X (Vec X n) X 1 (n ∷ [])
    v-v : ∀ {n} →   DyScalVec X (Vec X n) (Vec X n) 1 (n ∷ [])
    -- v-a : X (Ar X 1 (n ∷ [])) (Vec X n) 1 (n ∷ [])
    a-s : ∀ {d s} → DyScalVec X (Ar X d s) X d s
    -- a-v : X (Vec X n) (Ar X 1 (n ∷ [])) 1 (n ∷ [])
    a-a : ∀ {m n sx sy}{@(tactic dy-args-ok?) args : dy-args m n sx sy} → DyScalVec X (Ar X m sx) (Ar X n sy) (dy-args-dim args) (dy-args-shp args)


▴ₗ : ∀ {X A B d s} {{t : DyScalVec X A B d s}} → A → Ar X d s
▴ₗ {{s-s}} a = cst a
▴ₗ {{s-v}} a = cst a
▴ₗ {{s-a}} a = cst a
▴ₗ {{v-s}} a = ▴ a
▴ₗ {{v-v}} a = ▴ a
▴ₗ {{a-s}} a = a
▴ₗ ⦃ t = a-a {args = n-n} ⦄ a = a
▴ₗ ⦃ t = a-a {args = n-0} ⦄ a = a
▴ₗ ⦃ t = a-a {args = 0-n} ⦄ a = cst (sel a [])


▴ᵣ : ∀ {X A B d s} {{t : DyScalVec X A B d s}} → B → Ar X d s
▴ᵣ {{s-s}} b = cst b
▴ᵣ {{s-v}} b = ▴ b
▴ᵣ {{s-a}} b = b
▴ᵣ {{v-s}} b = cst b
▴ᵣ {{v-v}} b = ▴ b
▴ᵣ {{a-s}} b = cst b
▴ᵣ ⦃ t = a-a {args = n-n} ⦄ b = b
▴ᵣ ⦃ t = a-a {args = n-0} ⦄ b = cst (sel b [])
▴ᵣ ⦃ t = a-a {args = 0-n} ⦄ b = b


--infixr 20 _-′_
--_-′_ = lift′ N._∸_


_-safe-_ : (a : ℕ) → (b : ℕ) .{≥ : a N.≥ b} → ℕ
a -safe- b = a N.∸ b

{-
infixr 20 _-ₙ_
_-ₙ_ : ∀ {n}{s}
     → (a : Ar ℕ n s) → (b : Ar ℕ n s)
     → .{≥ : a ≥a b}
     → Ar ℕ n s
(imap f -ₙ imap g) {≥} = imap λ iv → (f iv -safe- g iv) {≥ = ≥ iv}
-}


---- FIXME: I guess we can eliminate _-′_ and lift′ entirely by inlining definitions.
--infixr 20 _-_
--_-_ : ∀ {A B d s}{{t : DyScalVec ℕ A B d s}} → (a : A) → (b : B) → .{≥ : ▴ₗ a ≥a ▴ᵣ b} → Ar ℕ d s
--_-_ ⦃ t = s-s ⦄ a b {a≥b} = imap λ iv → (a -safe- b) {a≥b iv}
--_-_ ⦃ t = s-v ⦄ a b {a≥b} = imap λ iv → (a -safe- sel (▴ b) iv) {a≥b iv}
--_-_ ⦃ t = s-a ⦄ a b {a≥b} = imap λ iv → (a -safe- sel b iv) {a≥b iv} --= ▴ a -′ b
--_-_ ⦃ t = v-s ⦄ a b {a≥b} = imap λ iv → (sel (▴ a) iv -safe- b) {a≥b iv} -- = ▴ a -′ ▴ b
--_-_ ⦃ t = v-v ⦄ a b {a≥b} = imap λ iv → (sel (▴ a) iv -safe- sel (▴ b) iv) {a≥b iv} --= ▴ a -′ ▴ b
--_-_ ⦃ t = a-s ⦄ a b {a≥b} = imap λ iv → (sel a iv -safe- b) {a≥b iv} --= a -′ ▴ b
--_-_ ⦃ t = a-a {args = n-n} ⦄ a b {a≥b} = imap λ iv → (sel a iv -safe- sel b iv) {a≥b iv}
--_-_ ⦃ t = a-a {args = n-0} ⦄ a b {a≥b} = imap λ iv → (sel a iv -safe- sel b []) {a≥b iv}
--_-_ ⦃ t = a-a {args = 0-n} ⦄ a b {a≥b} = imap λ iv → (sel a [] -safe- sel b iv) {a≥b iv}


infixr 20 _-_
_-_ : ∀ {A B d s}{{t : DyScalVec ℕ A B d s}} → (a : A) → (b : B) → .{≥ : ▴ₗ a ≥a ▴ᵣ b} → Ar ℕ d s
_-_ ⦃ t = s-s ⦄ a b  = imap λ iv → (a N.∸ b) 
_-_ ⦃ t = s-v ⦄ a b  = imap λ iv → (a N.∸ sel (▴ b) iv)
_-_ ⦃ t = s-a ⦄ a b  = imap λ iv → (a N.∸ sel b iv)
_-_ ⦃ t = v-s ⦄ a b  = imap λ iv → (sel (▴ a) iv N.∸ b)
_-_ ⦃ t = v-v ⦄ a b  = imap λ iv → (sel (▴ a) iv N.∸ sel (▴ b) iv)
_-_ ⦃ t = a-s ⦄ a b  = imap λ iv → (sel a iv N.∸ b)
_-_ ⦃ t = a-a {args = n-n} ⦄ a b  = imap λ iv → (sel a iv N.∸ sel b iv) 
_-_ ⦃ t = a-a {args = n-0} ⦄ a b  = imap λ iv → (sel a iv N.∸ sel b []) 
_-_ ⦃ t = a-a {args = 0-n} ⦄ a b  = imap λ iv → (sel a [] N.∸ sel b iv) 
-- _-′_ {args = args} a b


lift : ∀ {X A B d s}{{t : DyScalVec X A B d s}} → A → B → (_⊕_ : X → X → X) → Ar X d s
lift ⦃ t ⦄ a b _⊕_ = imap λ iv → sel (▴ₗ a) iv ⊕ sel (▴ᵣ b) iv

-- ℕ operations
infixr 20 _+_ _×_
_+_ _×_  : ∀ {A B d s}{{t : DyScalVec ℕ A B d s}} → A → B → Ar ℕ d s
a + b = lift a b N._+_
a × b = lift a b N._*_


-- Float operations
infixr 20 _+ᵣ_ _-ᵣ_ _×ᵣ_ _÷ᵣ_
_+ᵣ_ _-ᵣ_ _×ᵣ_ _÷ᵣ_ : ∀ {A B d s}{{t : DyScalVec Float A B d s}} → A → B → Ar Float d s
a +ᵣ b = lift a b primFloatPlus
a -ᵣ b = lift a b primFloatMinus
a ×ᵣ b = lift a b primFloatTimes
-- XXX we can request the proof that the right argument is not zero.
-- However, the current primFloatDiv has the type Float → Float → Float, so...
a ÷ᵣ b = lift a b primFloatDiv


lift-unary : ∀ {X A d s}{{t : SVup X A d s}} → (X → X) → A → Ar X d s
lift-unary ⦃ t = scal ⦄ f a = cst $ f a
lift-unary ⦃ t = vect ⦄ f a = imap λ iv → f $ V.lookup a $ ix-lookup iv zero
lift-unary ⦃ t = arry ⦄ f (imap a) = imap λ iv → f $ a iv


infixr 20 -ᵣ_ ÷ᵣ_ *ᵣ_
-ᵣ_ ÷ᵣ_ *ᵣ_ : ∀ {A d s}{{t : SVup Float A d s}} → A → Ar Float d s

*ᵣ_ = lift-unary primFloatExp
-ᵣ_ = lift-unary primFloatNegate
÷ᵣ_ = lift-unary (primFloatDiv 1.0)



module reduce-custom where
  drop-last : ∀ {m}{X : Set} → Vec X m → Vec X (m N.∸ 1)
  drop-last {0}  x = x
  drop-last {1}  x = []
  drop-last {suc (suc m)} (x ∷ xs) = x ∷ drop-last xs

  gz : ℕ → ℕ
  gz 0 = 0
  gz _ = 1

  take-last : ∀ {m}{X : Set} → Vec X m → Vec X (gz m)
  take-last {0}     x = x
  take-last {1}     x = x
  take-last {suc (suc m)} (x ∷ xs) = take-last xs

  _tldl++_ : ∀ {d s} → Ix (d N.∸ 1) (drop-last s) → Ix (gz d) (take-last s) → Ix d s
  _tldl++_ {0}  {s} iv jv = iv
  _tldl++_ {1}  {s} iv jv = jv
  _tldl++_ {suc (suc d)} {s ∷ ss} (i ∷ iv) jv = i ∷ (iv tldl++ jv)

  reduce-1d : ∀ {X Y : Set}{s} → (X → Y → Y) → Y → Ar X 1 s → Y
  reduce-1d {s = 0 ∷ []}     _⊕_ ε a = ε
  reduce-1d {s = suc x ∷ []} _⊕_ ε (imap a) = a (zero ∷ []) ⊕ reduce-1d {s = x ∷ []} _⊕_ ε (imap λ where (i ∷ []) → a (suc i ∷ []))

  infixr 20 _/′_
  _/′_ : ∀ {X Y : Set}{d s} → (X → Y → Y) → Ar X d s → {ε : Y} → Ar Y _ (drop-last s)
  _/′_ {d = 0}     f (imap a) {ε} =  imap λ iv → ε
  _/′_ {d = suc d} f (imap a) {ε} = imap λ iv → reduce-1d f ε (imap λ jv → a (iv tldl++ jv))

  data reduce-neut : {X Y : Set} → (X → Y → Y) → Y → Set where
    instance
      plus-nat : reduce-neut N._+_ 0
      mult-nat : reduce-neut N._*_ 1
      plus-flo : reduce-neut primFloatPlus 0.0
      gplus-float : reduce-neut (_+ᵣ_ {{t = a-a {sx = []}{sy = []}{args = n-n} }}) (cst 0.0)

  infixr 20 _/_
  _/_ : ∀ {X Y : Set}{n s ε}
        → (_⊕_ : X → Y → Y) → {{c : reduce-neut _⊕_ ε}}
        → Ar X n s → Ar Y _ (drop-last s)
  _/_ {ε = ε} f a = (f /′ a){ε}

  infixr 20 _//_
  _//_ : ∀ {X Y : Set}{n s ε}
        → (_⊕_ : Scal X → Scal Y → Scal Y) → {{c : reduce-neut _⊕_ ε}}
        → Ar X n s → Ar Y _ (drop-last s)
  _//_ {ε = ε} f a = imap λ jv → ▾ (sel ((f /′ (imap λ iv → ▴ (sel a iv))){ε}) jv)

  -- replication, not reduction
  infixr 20 _/ᵣ_
  _/ᵣ_ : ∀ {X : Set}{d}{s}{m} → (n : ℕ) → Ar X (d N.+ 1) (s V.++ (m ∷ [])) → Ar X (d N.+ 1) (s V.++ (n N.* m ∷ []))
  _/ᵣ_ {d = d} {s = s} 0       a = imap λ iv → magic-fin (ix-lookup (take-ix-r s _ iv) zero)
  _/ᵣ_ {d = d} {s = s} (suc n) a = imap λ iv → let i   = ix-lookup (take-ix-r s _ iv) zero
                                                   l   = take-ix-l s _ iv
                                                   i/n = F.fromℕ< $ /-mono-f {b = suc n} (F.toℕ<n i) _
                                               in sel a $ l ix++ (i/n ∷ [])

  infixr 20 _⌿ᵣ_
  _⌿ᵣ_ : ∀ {X : Set}{d s m} → (n : ℕ) → Ar X (1 N.+ d) ((m ∷ []) V.++ s) → Ar X (1 N.+ d) ((n N.* m ∷ []) V.++ s)
  _⌿ᵣ_ {d = d} {s = s} 0       a = imap λ iv → magic-fin (ix-lookup iv zero)
  _⌿ᵣ_ {d = d} {s = s} (suc n) a = imap λ iv → let i   = ix-lookup iv zero
                                                   r   = take-ix-r _ s iv
                                                   i/n = F.fromℕ< $ /-mono-f {b = suc n} (F.toℕ<n i) _
                                               in sel a $ (i/n ∷ []) ix++ r

open reduce-custom public

-- shape and flatten
infixr 20 ρ_
ρ_ : ∀ {ℓ}{X : Set ℓ}{d s} → Ar X d s → Ar ℕ 1 (d ∷ [])
ρ_ {s = s} _ = s→a s

infixr 20 ,_
,_ : ∀ {a}{X : Set a}{n s} → Ar X n s → Ar X 1 (prod s ∷ [])
,_ {s = s} p = imap λ iv → sel p (off→idx s iv)


-- Note that two dots in an upper register combined with
-- the underscore form the _̈  symbol.  When the symbol is
-- used on its own, it looks like ̈ which is the correct
-- "spelling".
infixr 20 _̈_
_̈_ : ∀ {a}{X Y : Set a}{n s}
    → (X → Y)
    → Ar X n s
    → Ar Y n s
f ̈ imap p = imap $ f ∘ p

module _ where
  data iota-type : (d : ℕ) → (n : ℕ) → (Vec ℕ d) → Set where
    instance
      iota-scal : iota-type 0 1 []
      iota-vec  : ∀ {n} → iota-type 1 n (n ∷ [])


  iota-res-t : ∀ {d n s} → iota-type d n s → (sh : Ar ℕ d s) → Set

  iota-res-t {n = n} iota-scal sh = Ar (Σ ℕ λ x → x N.< ▾ sh)
                                      1 (▾ sh ∷ [])

  iota-res-t {n = n} iota-vec  sh = Ar (Σ (Ar ℕ 1 (n ∷ []))
                                        λ v → v <a sh)
                                      n (a→s sh)

  data iota-t : Set → (n : ℕ) → Set where
    instance
      iota-scal : iota-t ℕ 0
      iota-vect : ∀ {n} → iota-t (Vec ℕ n) n
      iota-arrs : iota-t (Ar ℕ 0 []) 1
      iota-arrv : ∀ {n} → iota-t (Ar ℕ 1 (n ∷ [])) n

  iota-ty : ∀ {X n} → iota-t X n → X → Set
  iota-ty {n = n} iota-scal x = Ar (Ix 1 (x ∷ [])) 1 (x ∷ [])
  iota-ty {n = n} iota-vect x = Ar (Ix n x) n x
  iota-ty {n = n} iota-arrs x = Ar (Ix n (▾ x ∷ [])) n (▾ x ∷ [])
  iota-ty {n = n} iota-arrv x = Ar (Ix n (▾ x)) n (▾ x)

  iota_ : ∀ {X n}{{t : iota-t X n}} → (x : X) → iota-ty t x
  iota_ ⦃ t = iota-scal ⦄ x = imap id
  iota_ ⦃ t = iota-vect ⦄ x = imap id
  iota_ ⦃ t = iota-arrs ⦄ x = imap id
  iota_ ⦃ t = iota-arrv ⦄ x = imap id




{-
  iota-t : ∀ {A d s} → SVup ℕ A d s → Ar ℕ d s → Set
  iota-t {d = d}{s}      scal a = Ar (Ix 1 (▾ a ∷ [])) 1 (▾ a ∷ [])
  iota-t {d = d}{n ∷ []} vect a = Ar (Ix n (▾ a))      n (▾ a)
  iota-t {d = d}{n ∷ []} arry a = Ar (Ix n (▾ a))      n (▾ a)

  iota_ : ∀ {A d s}{{t : SVup ℕ A d s}} → (a : Ar ℕ d s) → iota-t t a
  iota_ {d = d}{s}⦃ t = scal ⦄ a = imap id
  iota_ {d = d}{s}⦃ t = vect ⦄ a = imap id
  iota_ {d = d}{s}⦃ t = arry ⦄ a = {!!} --imap id
-}

  a<b⇒b≡c⇒a<c : ∀ {a b c} → a N.< b → b ≡ c → a N.< c
  a<b⇒b≡c⇒a<c a<b refl = a<b
  
  infixr 20 ι_
  ι_ : ∀ {d n s}{{c : iota-type d n s}}
    → (sh : Ar ℕ d s)
    → iota-res-t c sh
  ι_ ⦃ c = iota-scal ⦄ s = (imap λ iv → (F.toℕ $ ix-lookup iv zero) , F.toℕ<n (ix-lookup iv zero))
  ι_ {n = n} {s = s ∷ []} ⦃ c = iota-vec ⦄ (imap sh) = imap cast-ix→a
    where
      cast-ix→a : _
      cast-ix→a iv = let
                      ix , pf = ix→a iv
                    in ix , λ jv → a<b⇒b≡c⇒a<c (pf jv) (s→a∘a→s (imap sh) jv)








module cnn where
  open reduce-custom

  -- blog←{⍺×⍵×1-⍵}
  -- NOTE: We use + instead of - in the last example, as we are not in ℝ, and N.∸ needs a proof.
  blog : ∀ {n s} → Ar ℕ n s → Ar ℕ n s → Ar ℕ n s
  blog α ω = α × ω × 1 + ω

  conv : ∀ {n wₛ aₛ}
        → Ar ℕ n wₛ
        → Ar ℕ n aₛ
        → {≥ : ▴ aₛ ≥a ▴ wₛ}
        → Ar ℕ n $ ▾ (1 + (aₛ - wₛ){≥})
  conv _ _ = cst 1
  -- backbias←{+/,⍵}
  backbias : ∀ {n s} → Ar ℕ n s → Ar ℕ _ []
  backbias ω = N._+_ / , ω

  -- meansqerr←{÷∘2+/,(⍺-⍵)*2}
  meansqerr : ∀ {n s} → Ar ℕ n s → Ar ℕ n s → Ar ℕ _ []
  meansqerr α ω = _+ 2 $ N._+_ / , (α + ω) × (α + ω)
                  -- this is intentional, as we don't really have ÷ in ℕ

  -- backavgpool←{2⌿2/⍵÷4}⍤2
  backavgpool : ∀ {s} → Ar ℕ 2 s → Ar ℕ 2 $ ▾ (2 × s)
  backavgpool {s = _ ∷ _ ∷ []} ω = 2 /ᵣ′ 2 ⌿ᵣ ω × 4
    where
      infixr 20 _/ᵣ′_
      _/ᵣ′_ = _/ᵣ_ {s = _ ∷ []}

  -- Something that could go in Stdlib.
  ≡⇒≤ : ∀ {a b} → a ≡ b → a N.≤ b
  ≡⇒≤ refl = ≤-refl

  -- This should be perfectly generaliseable --- instead of 2
  -- we can use any m>0
  a<b⇒k<2⇒a*2+k<b*2 : ∀ {a b k} → a N.< b → k N.< 2 → a N.* 2 N.+ k N.< b N.* 2
  a<b⇒k<2⇒a*2+k<b*2 {a} {b} {zero} a<b k<2
                    rewrite (+-identityʳ (a N.* 2))
                          | (*-comm a 2)
                          | (*-comm b 2) = *-monoʳ-< 1 a<b
  a<b⇒k<2⇒a*2+k<b*2 {a} {b} {suc zero} a<b k<2 = ≤-trans (N.s≤s (≡⇒≤ (+-comm _ 1)))
                                                          (*-monoˡ-≤ 2 a<b) 
  a<b⇒k<2⇒a*2+k<b*2 {a} {b} {suc (suc k)} a<b (N.s≤s (N.s≤s ()))

  A<B⇒K<2⇒A*2+K<B*2 : ∀ {n s}{a b k : Ar ℕ n s} → a <a b → k <a (cst 2) → ((a × 2) + k) <a (b × 2)
  A<B⇒K<2⇒A*2+K<B*2 {a = imap a} {imap b} {imap k} a<b k<2 = λ iv → a<b⇒k<2⇒a*2+k<b*2 (a<b iv) (k<2 iv)


  ---
  a<n⇒b<n⇒a+b<m+n : ∀ {m n} a b → a N.< m → b N.< n → a N.+ b N.< m N.+ n
  a<n⇒b<n⇒a+b<m+n {m}     zero b a<m b<n            = ≤-stepsˡ m b<n
  a<n⇒b<n⇒a+b<m+n {suc m} (suc a) b (N.s≤s a<m) b<n = N.s≤s (a<n⇒b<n⇒a+b<m+n a b a<m b<n)

  a<n⇒b<n⇒a+b<m+n-1 : ∀ {m n} a b → a N.< m → b N.< n → a N.+ b N.< m N.+ n N.∸ 1
  a<n⇒b<n⇒a+b<m+n-1 {suc m} {suc n} zero b a<m b<n            = ≤-stepsˡ m b<n
  a<n⇒b<n⇒a+b<m+n-1 {suc m} {suc n} (suc a) b (N.s≤s a<m) b<n rewrite +-suc m n =
      N.s≤s $ begin
       suc (a N.+ b)       ≤⟨ a<n⇒b<n⇒a+b<m+n-1 a b a<m b<n ⟩
       m N.+ suc n N.∸ 1   ≡⟨ cong₂ N._∸_ (+-suc m n) refl ⟩
       suc (m N.+ n) N.∸ 1 ≡⟨⟩
       m N.+ n
      ∎
      where open N.≤-Reasoning

  _+ff_ : ∀ {m n} → Fin m → Fin n → Fin (m N.+ n N.∸ 1)
  a +ff b = F.fromℕ< (a<n⇒b<n⇒a+b<m+n-1 _ _ (F.toℕ<n a) (F.toℕ<n b))
  
  _+f_ : ∀ {m n} → Fin m → Fin n → Fin (m N.+ n)
  a +f b = F.fromℕ< (a<n⇒b<n⇒a+b<m+n _ _ (F.toℕ<n a) (F.toℕ<n b))

  _*lf_ : ∀ {n} → (m : ℕ) → Fin n → .{m N.> 0} → Fin (suc (m N.* n N.∸ m))
  _*lf_ {n} m (b) {m>0} = let
                            m*sb≤m*n    = *-monoʳ-≤ m $ F.toℕ<n b
                            m+m*b≤m*n   = subst₂ N._≤_ (*-suc m _)   refl m*sb≤m*n
                            m+m*b-m≤m*n = ∸-monoˡ-≤  m m+m*b≤m*n
                            m*b≤m*n-m   = subst₂ N._≤_ (m+n∸m≡n m _) refl m+m*b-m≤m*n
                          in F.fromℕ< (N.s≤s m*b≤m*n-m)

  --_i+_ : ∀ {n s s'} → Ix n s → Ix n s' → Ix n (▾ ((s + s') -′ ▴ 1))
  --iv i+ jv = ix-tabulate λ i → subst Fin (sym (V.lookup∘tabulate _ i)) $ ix-lookup iv i +ff ix-lookup jv i



  -- Note that we explicitly use _-′_ instead of _-_ to avoid the proof.
  -- It is ok if m ≥ s×m as this means that s=0, and therefore there is no
  -- such index (element of Fin 0 at some position in s).
  --_il×_ : ∀ {n s} → (m : ℕ) → Ix n s → .{≥ : m N.> 0} → let s = 1 + (m × s) -′ ▴ m in Ix n (▾ s)
  --(a il× ix) {m>0} = ix-tabulate λ i → subst Fin (sym (V.lookup∘tabulate _ i)) $ (a *lf ix-lookup ix i){m>0}

{-
  avgpool' : ∀ {s}
          → Ar Float 2 $ ▾ (2 × s)
          → Ar Float 2 s
  avgpool' {s} (imap p) = imap body
    where
          m>0⇒k≤k*m : ∀ {m} → m N.> 0 → ∀ k → k N.≤ k N.* m
          m>0⇒k≤k*m m>0 zero = N.z≤n
          m>0⇒k≤k*m m>0 (suc k) = +-mono-≤ m>0 (m>0⇒k≤k*m m>0 k)

          --a≤a*b

          thm : ∀ {d s} → Ix d s → ∀ i → d N.+ (d N.* V.lookup s i N.∸ d) ≡ d N.* V.lookup s i
          thm {d}{s} ix i with V.lookup s i | ix-lookup ix i
          ... | zero  | ()
          ... | suc m | _ = m+[n∸m]≡n (m>0⇒k≤k*m {m = suc m} (N.s≤s N.z≤n) d)

          thmx : ∀ {d s} → Ix d s → ∀ i → V.lookup (▾ (d + (d × s) -′ ▴ d)) i ≡ V.lookup (▾ (d × s)) i
          thmx {d}{s} ix i with V.lookup s i | inspect (V.lookup s) i  | ix-lookup ix i
          ... | zero  | _      | ()
          ... | suc m | [ pf ] | _ = begin
             V.lookup (V.tabulate (λ z → d N.+ (d N.* V.lookup s z N.∸ d))) i ≡⟨ lookup∘tabulate _ i ⟩
             d N.+ (d N.* V.lookup s i N.∸ d) ≡⟨ cong (d N.+_) (cong (N._∸ d) (cong (d N.*_) pf)) ⟩
             d N.+ (d N.* suc m N.∸ d)        ≡⟨ m+[n∸m]≡n (m>0⇒k≤k*m {m = suc m} (N.s≤s N.z≤n) d) ⟩
             d N.* suc m                      ≡⟨ cong (d N.*_) (sym pf) ⟩
             d N.* V.lookup s i               ≡⟨ sym (lookup∘tabulate _ i) ⟩
             V.lookup (V.tabulate (λ z → d N.* V.lookup s z)) i
             ∎
             where open ≡-Reasoning


          body : _ → _
          body iv = let
                    ixs = iota (2 ∷ 2 ∷ [])
                    ix = (2 il× iv) {N.s≤s N.z≤n}
                    f iv = p $ subst-ix {!!} $ iv i+ ix
                    xx = primFloatPlus / , f ̈ ixs
                    in {!!}

-}

  avgpool : ∀ {s}
          → Ar ℕ 2 $ ▾ (s × 2)
          → Ar ℕ 2 s
  avgpool {s} (imap p) = imap body
    where body : _ → _
          body iv = let
               sh = s × 2
               ix , ix<s = ix→a iv
               bx = ix × 2
               ixs = ι (cst {s = 2 ∷ []} 2)
               use-ixs = λ where
                 (i , pf) → p $ a→ix (bx + i) sh $ A<B⇒K<2⇒A*2+K<B*2 ix<s pf
               in ▾ (_× 4 $ N._+_ / , use-ixs ̈ ixs)

--test : ∀ {s : Vec ℕ 2} → ℕ
--test {s} = {! s × 2!}



-- Take and Drop
ax+sh<s : ∀ {n}
        → (ax sh s : Ar ℕ 1 (n ∷ []))
        → (s≥sh : s ≥a sh)
        → (ax <a (s - sh) {≥ = s≥sh})
        → (ax + sh) <a s
ax+sh<s (imap ax) (imap sh) (imap s) s≥sh ax<s-sh iv =
    let
      ax+sh<s-sh+sh = +-monoˡ-< (sh iv) (ax<s-sh iv)
      s-sh+sh≡s     = m∸n+n≡m (s≥sh iv)
    in a<b⇒b≡c⇒a<c ax+sh<s-sh+sh s-sh+sh≡s
{-
_↑_ : ∀ {a}{X : Set a}{n s}
    → (sh : Ar ℕ 1 (n ∷ []))
    → (a : Ar X n s)
    → {pf : s→a s ≥a sh}
    → Ar X n $ a→s sh
_↑_ {s = s} sh       (imap f) {pf}   with (prod $ a→s sh) N.≟ 0
_↑_ {s = s} sh       (imap f) {pf} | yes Πsh≡0 = imap λ iv → magic-fin $ Πs≡0⇒Fin0 _ iv Πsh≡0 --mkempty _ Πsh≡0
_↑_ {s = s} (imap q) (imap f) {pf} | no  Πsh≢0 = imap λ iv → {- mtake
  where
    mtake : _
    mtake iv = -} let
                  ai , ai< = ix→a iv
                  ix<q jv = a<b⇒b≡c⇒a<c (ai< jv) (s→a∘a→s (imap q) jv)
                  ix = a→ix ai (s→a s) λ jv → ≤-trans (ix<q jv) (pf jv)
               in f (subst-ix (a→s∘s→a s) ix)
-}
{- -}
_↑_ : ∀ {a}{X : Set a}{n s}
    → (sh : Ar ℕ 1 (n ∷ []))
    → (a : Ar X n s)
    → {pf : s→a s ≥a sh}
    → Ar X n $ a→s sh
_↑_ {s = s} sh       (imap f) {pf} = case (prod $ a→s sh) N.≟ 0 of λ where
        (yes Πsh≡0) → imap λ iv → magic-fin $ Πs≡0⇒Fin0 _ iv Πsh≡0
        (no  Πsh≢0) → imap λ iv → let
                  ai , ai< = ix→a iv
                  ix<q jv = a<b⇒b≡c⇒a<c (ai< jv) (s→a∘a→s sh jv)
                  ix = a→ix ai (s→a s) λ jv → ≤-trans (ix<q jv) (pf jv)
               in f (subst-ix (a→s∘s→a s) ix)
{- -}


_↓_ : ∀ {a}{X : Set a}{n s}
    → (sh : Ar ℕ 1 (n ∷ []))
    → (a : Ar X n s)
    → {pf : (s→a s) ≥a sh}
    → Ar X n $ a→s $ (s→a s - sh) {≥ = pf}
_↓_ {s = s} sh (imap x) {pf} with
                             let p = prod $ a→s $ (s→a s - sh) {≥ = pf}
                             in  p N.≟ 0
_↓_ {s = s} sh       (imap f) {pf} | yes Π≡0 = mkempty _ Π≡0
_↓_ {s = s} (imap q) (imap f) {pf} | no  Π≢0 = imap mkdrop
  where
    mkdrop : _
    mkdrop iv = let
                  ai , ai< = ix→a iv
                  ax = ai + (imap q)
                  thmx = ax+sh<s
                           ai (imap q) (s→a s) pf
                           λ jv → a<b⇒b≡c⇒a<c (ai< jv)
                                  (s→a∘a→s ((s→a s - (imap q)) {≥ = pf}) jv)
                  ix = a→ix ax (s→a s) thmx
                in f (subst-ix (a→s∘s→a s) ix)



∸-monoˡ-< : ∀ {m n o} → m < n → o ≤ m → m ∸ o < n ∸ o
∸-monoˡ-< {o = zero}  m<n o≤m = m<n
∸-monoˡ-< {suc m} {o = suc o} (s≤s m<n) (s≤s o≤m) = ∸-monoˡ-< m<n o≤m

a+b-a≡a : ∀ {n} {s₁ : Vec ℕ n} {s : Ix 1 (n ∷ []) → ℕ}
             {jv : Ix 1 (n ∷ [])} →
           V.lookup (V.tabulate (λ i → s (i ∷ []) N.+ V.lookup s₁ i))
           (ix-lookup jv zero)
           ∸ s jv
           ≡ V.lookup s₁ (ix-lookup jv zero)
a+b-a≡a {zero} {[]} {s} {x ∷ []} = magic-fin x
a+b-a≡a {suc n} {x ∷ s₁} {s} {zero ∷ []} = m+n∸m≡n (s (zero ∷ [])) x
a+b-a≡a {suc n} {x ∷ s₁} {s} {suc j ∷ []} = a+b-a≡a {s₁ = s₁} {s = λ { (j ∷ []) → s (suc j ∷ [])}} {jv = j ∷ []}

pre-pad : ∀ {a}{X : Set a}{n}{s₁ : Vec ℕ n}
        → (sh : Ar ℕ 1 (n ∷ []))
        → X
        → (a : Ar X n s₁)
        → Ar X n (a→s $ sh + ρ a)
pre-pad {s₁ = s₁} (imap s) e (imap f) = imap body
  where
    body : _
    body iv = let ix , ix<s = ix→a iv
              in case ix ≥a? (imap s) of λ where
                   (yes p) → let
                      fx = (ix - (imap s)) {≥ = p}
                      fv = a→ix fx (s→a s₁)
                                λ jv → a<b⇒b≡c⇒a<c
                                          (∸-monoˡ-< (ix<s jv) (p jv))
                                          (a+b-a≡a {s₁ = s₁} {s = s} {jv = jv})
                      in f (subst-ix (λ i → lookup∘tabulate _ i) fv)
                   (no ¬p) → e



b≤a⇒c<b⇒a-b+c<a : ∀ {a b c} → b ≤ a → c < b → a ∸ b N.+ c < a
b≤a⇒c<b⇒a-b+c<a {suc a} {suc b} {zero}  b≤a c<b rewrite +-identityʳ (a ∸ b) = s≤s (m∸n≤m a b)
b≤a⇒c<b⇒a-b+c<a {suc a} {suc b} {suc c} (s≤s b≤a) (s≤s c<b) = let q = b≤a⇒c<b⇒a-b+c<a b≤a c<b
                                                              in subst₂ _<_ (sym $ +-suc (a ∸ b) c) refl $ +-monoʳ-< 1 q


[a+b≥c]⇒b<c⇒a+b-c<a : ∀ {a b c} → a N.+ b N.≥ c → b < c → a N.+ b ∸ c < a
[a+b≥c]⇒b<c⇒a+b-c<a {a}{b}{c} a+b≥c b<c = let a+b<a+c = +-monoʳ-< a b<c
                                          in subst₂ _<_ refl (m+n∸n≡m _ c) $ ∸-monoˡ-< a+b<a+c a+b≥c

{-
_-↑⟨_⟩_ : ∀ {a}{X : Set a}{n}{s₁ : Vec ℕ n}
        → (sh : Ar ℕ 1 (n ∷ []))
        → X
        → (a : Ar X n s₁)
        → Ar X n (▾ sh)
_-↑⟨_⟩_ {s₁ = s₁} s e a = imap λ iv → let
                  ix , ix<s = ix→a iv
                  in case ((ρ a) + ix) ≥a? s of λ where
                             (yes p) → let
                                 ov = (((ρ a) + ix) - s){p}
                                 oi = a→ix ov (ρ a) λ { jv@(i ∷ []) → [a+b≥c]⇒b<c⇒a+b-c<a (p jv) (subst₂ _<_ refl (V.lookup∘tabulate _ i) $ ix<s jv) }
                                in sel a (subst-ix (λ i → lookup∘tabulate _ i) oi)
                             (no _) → e
-}

_-↑⟨_⟩_ : ∀ {a}{X : Set a}{n}{s₁ : Vec ℕ n}
        → (sh : Ar ℕ 1 (n ∷ []))
        → X
        → (a : Ar X n s₁)
        → Ar X n (▾ sh)
_-↑⟨_⟩_ {s₁ = s₁} s e a = imap body
  where
    body : _
    body iv with ix→a iv
    ... | ix , ix<s with ((ρ a) + ix) ≥a? s
    ... | (yes p) = let
                      ov = (((ρ a) + ix) - s){p}
                      oi = a→ix ov (ρ a) λ { jv@(i ∷ []) → [a+b≥c]⇒b<c⇒a+b-c<a (p jv) (subst₂ _<_ refl (V.lookup∘tabulate _ i) $ ix<s jv) }
                    in sel a (subst-ix (λ i → lookup∘tabulate _ i) oi)
    ... | _  = e

{-
_↑⟨_⟩_ : ∀ {a}{X : Set a}{n}{s : Vec ℕ n}
      → (sh : Ar ℕ 1 (n ∷ []))
      → X
      → (a : Ar X n s)
      → Ar X n (▾ sh)
_↑⟨_⟩_ {s = s} (imap sh) e (imap a) = imap body
  where
    body : _
    body iv = let ix , ix<s = ix→a iv
              in case ix <a? (ρ imap a) of λ where
                (yes p) → let
                            av = a→ix ix (ρ imap a) p
                          in a (subst-ix (λ i → lookup∘tabulate _ i) av)
                (no ¬p) → e
-}

_↑⟨_⟩_ : ∀ {a}{X : Set a}{n}{s : Vec ℕ n}
      → (sh : Ar ℕ 1 (n ∷ []))
      → X
      → (a : Ar X n s)
      → Ar X n (▾ sh)
_↑⟨_⟩_ {s = s} (imap sh) e (imap a) = imap body
  where
    body : _
    body iv with ix→a iv
    ... | ix , ix<s with ix <a? (ρ imap a)
    ... | (yes p) = let
                      av = a→ix ix (ρ imap a) p
                    in a (subst-ix (λ i → lookup∘tabulate _ i) av)
    ... | (no ¬p) = e





_̈⟨_⟩_ : ∀ {a}{X Y Z : Set a}{n s}
     → Ar X n s
     → (X → Y → Z)
     → Ar Y n s → Ar Z n s
(imap p) ̈⟨ f ⟩ (imap p₁) = imap λ iv → f (p iv) (p₁ iv)
--p ̈⟨ f ⟩ p₁ = imap λ iv → f (sel p iv) (sel p₁ iv)


module test where
  s : Vec ℕ 3
  s = 1 ∷ 2 ∷ 3 ∷ []
  a : Ar ℕ 3 s
  a = cst 10

  b : Ar ℕ 0 []
  b = cst 20

  test/ : _
  test/ = reduce-custom._/_ N._+_ a

  -- These tests work, which is nice.
  test₁ : Ar ℕ 3 s
  test₁ = a + b

  test₂ : Ar ℕ 3 s
  test₂ = b + a

  test₃ : Ar ℕ 3 s
  test₃ = a + a

  test₄ : Ar ℕ 0 []
  test₄ = b + b

  -- This looks much better.
  test-nn : ∀ {n s} → (a b : Ar ℕ n s) → Ar ℕ n s
  test-nn {n}{s} x y = x + y

  test-n0 : ∀ {n s} →  Ar ℕ n s → Ar ℕ n s
  test-n0 x = x + b

  test-0n : ∀ {n s} →  Ar ℕ n s → Ar ℕ n s
  test-0n x = b + x

  -- This definition should fail, as sx ≠ sy (not necessarily)
  --test-fail : ∀ {n sx sy} → Ar ℕ n sx → Ar ℕ n sy → Ar ℕ n sy
  --test-fail x y = x + y


