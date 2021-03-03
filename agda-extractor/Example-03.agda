open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat as N using (ℕ; zero; suc; _≤_; _≥_; _<_; s≤s; z≤n)
import      Data.Nat.DivMod as N
open import Data.Nat.Properties as N
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
import      Data.Vec.Properties as V
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Product as Prod using (Σ; _,_; curry; uncurry) renaming (_×_ to _⊗_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import Function

open import Array.Base
open import Array.Properties

open import APL2

open import Agda.Builtin.Float

v→a : ∀ {a}{X : Set a}{n} → Vec X n → Ar X 1 (n ∷ [])
v→a s = imap (λ iv → V.lookup s $ ix-lookup iv zero )

a→v : ∀ {a}{X : Set a}{s} → Ar X 1 (s ∷ []) → Vec X s
a→v (imap x) = V.tabulate λ i → x (i ∷ [])

-- blog←{⍺×⍵×1-⍵}
blog : ∀ {n s} → Ar Float n s → Ar Float n s → Ar Float n s
blog α ω = α ×ᵣ ω ×ᵣ 1.0 -ᵣ ω

test-blog = a→v $ blog (v→a $ 3.0 ∷ 4.0 ∷ []) (v→a $ 5.0 ∷ 6.0 ∷ [])

kblog = kompile blog [] []
test₃₆ : kblog ≡ ok _
test₃₆ = refl



-- backbias←{+/,⍵}
backbias : ∀ {n s} → Ar Float n s → Scal Float
backbias ω = _+ᵣ′_ / , ω
  where
    _+ᵣ′_ = primFloatPlus

kbackbias = kompile backbias (quote prod ∷ []) (quote prod ∷ quote off→idx ∷ quote reduce-custom.reduce-1d ∷ [])


-- logistic←{÷1+*-⍵}
logistic : ∀ {n s} → Ar Float n s → Ar Float n s
logistic ω = ÷ᵣ 1.0 +ᵣ *ᵣ -ᵣ ω

klogistic = kompile logistic [] []
test₃₈ : klogistic ≡ ok _
test₃₈ = refl

-- meansqerr←{÷∘2+/,(⍺-⍵)*2}
meansqerr : ∀ {n s} → Ar Float n s → Ar Float n s → Scal Float
meansqerr α ω = _÷ᵣ 2.0 $ _+ᵣ′_ / , (α -ᵣ ω) ×ᵣ (α -ᵣ ω)
  where
    _+ᵣ′_ = primFloatPlus

kmeansqerr = kompile meansqerr (quote prod ∷ []) (quote prod ∷ quote off→idx ∷ quote reduce-custom.reduce-1d ∷ [])
test₃₉ : klogistic ≡ ok _
test₃₉ = refl

-- backavgpool←{2⌿2/⍵÷4}⍤2
backavgpool : ∀ {s} → Ar Float 2 s → Ar Float 2 $ ▾ (2 × s)
backavgpool {s = _ ∷ _ ∷ []} ω = 2 ⌿ᵣ 2 /ᵣ′ ω ÷ᵣ 4.0
  where
    infixr 20 _/ᵣ′_
    _/ᵣ′_ = _/ᵣ_ {s = _ ∷ []}

kbackavgpool = kompile backavgpool [] []
test₄₀ : kbackavgpool ≡ ok _
test₄₀ = refl


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


-- avg ← { (+/÷≢),⍵ }
-- avgpool ← { (x y) ← ⍴⍵ ⋄ avg⍤2 ⊢ 0 2 1 3⍉(x÷2) 2 (y÷2) 2⍴ ⍵ }
avgpool : ∀ {s}
        → Ar Float 2 $ ▾ (s × 2)
        → Ar Float 2 s
avgpool {s} (imap p) = imap body
  where
    body : _ → _
    body iv = ▾ (_÷ᵣ 4.0 $ _+ᵣ′_ / , f ̈ ι [2,2])
      where
         [2,2] = cst {s = 2 ∷ []} 2
         f : _ → _
         f (i , pf) = let ix , ix<s = ix→a iv in
                      p $ a→ix ((ix × 2) + i) (s × 2) $ A<B⇒K<2⇒A*2+K<B*2 ix<s pf
         _+ᵣ′_ = primFloatPlus

kavgpool = kompile avgpool [] []


avgpool' : ∀ {s} → Ar Float 2 $ ▾ (s × 2) → Ar Float 2 s
avgpool' {s} (imap p) = imap $ λ iv →
  let ix , ix<s = ix→a iv
      f = λ (i , pf) → p $ a→ix ((ix × 2) + i) (s × 2) (A<B⇒K<2⇒A*2+K<B*2 ix<s pf)
      [2,2] = cst {s = 2 ∷ []} 2
  in ▾ (_÷ᵣ 4.0 $ _+ᵣ′_ / , f ̈ ι [2,2])
  where
    _+ᵣ′_ = primFloatPlus

kavgpool' = kompile avgpool' [] []

