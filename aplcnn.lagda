\begin{code}[hide]
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Nat
open import Data.Unit
open import Data.Fin using (Fin; zero; suc)
open import Data.List
open import Function
open import Reflection
module _ where
  data Ix : (d : ℕ) → (s : Vec ℕ d) → Set where
    []   : Ix 0 []
    _∷_  : ∀ {d s x} → Fin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)

  record Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
    constructor imap
    field sel : Ix d s → X
\end{code}
\section{\label{sec:apl}APL and CNN}

The overall story of this chapter is that if you are trying to
embed an untyped language, you might hit some expressibility
limits of Agda that you'd have to work around.

The main problem is overloaded operators, and the story is:

\begin{code}
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

  -- Check if any dimension of the two arrays are zeroes
  -- and pick the first one that matches.
  dy-args-ok? : Term → TC ⊤
\end{code}
\begin{code}[hide]
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
          unify hole (con (quote n-n) [])
\end{code}
\begin{code}
  dy-type : ∀ a → Set a → Set a
  dy-type a X = ∀ {m n sx sy} {@(tactic dy-args-ok?) args : dy-args m n sx sy}
                → Ar X m sx → Ar X n sy → Ar X _ (dy-args-shp args)

  lift′ : ∀ {a}{X : Set a} → (_⊕_ : X → X → X) → dy-type a X
  lift′ _⊕_ {args = n-n} (imap a) (imap b) = imap λ iv → a iv ⊕ b iv
  lift′ _⊕_ {args = n-0} (imap a) (imap b) = imap λ iv → a iv ⊕ b []
  lift′ _⊕_ {args = 0-n} (imap a) (imap b) = imap λ iv → a [] ⊕ b iv

  data SVup (X : Set) : Set → (d : ℕ) → (sh : Vec ℕ d) → Set where
    instance
      scal : SVup X X 0 []
      vect : ∀ {n} → SVup X (Vec X n) 1 (n ∷ [])
      arry : ∀ {d s} → SVup X (Ar X d s) d s

  cst : ∀ {a}{X : Set a}{d s} → X → Ar X d s
  cst x = imap λ _ → x

  infixr 30 ▴_
  ▴_ : ∀ {X A d s}{{t : SVup X A d s}} → A → Ar X d s
  ▴_ {{ t = scal }} a = cst a --imap λ _ → a
  ▴_ {{ t = vect }} a = imap λ where (i ∷ []) → V.lookup a i
  ▴_ {{ t = arry }} a = a

  infixr 30 ▾_
  ▾_ : ∀ {X A d s}{{t : SVup X A d s}} → Ar X d s → A
  ▾_ {{ t = scal }} (imap a) = a []
  ▾_ {{ t = vect }} (imap a) = V.tabulate λ i → a $ i ∷ []
  ▾_ {{ t = arry }} a = a

  data DyScalVec (X : Set) : Set → Set → (d : ℕ) → (sh : Vec ℕ d) → Set where
    instance
      s-s :           DyScalVec X X X 0 []
      s-v : ∀ {n} →   DyScalVec X X (Vec X n) 1 (n ∷ [])
      s-a : ∀ {d s} → DyScalVec X X (Ar X d s) d s
      v-s : ∀ {n} →   DyScalVec X (Vec X n) X 1 (n ∷ [])
      v-v : ∀ {n} →   DyScalVec X (Vec X n) (Vec X n) 1 (n ∷ [])
      a-s : ∀ {d s} → DyScalVec X (Ar X d s) X d s
      a-a : ∀ {m n sx sy}{@(tactic dy-args-ok?) args :
        dy-args m n sx sy} → DyScalVec X (Ar X m sx) (Ar X n sy) (dy-args-dim args) (dy-args-shp args)

  ▴ₗ : ∀ {X A B d s} {{t : DyScalVec X A B d s}} → A → Ar X d s
  ▴ₗ {{s-s}} a = cst a
  ▴ₗ {{s-v}} a = cst a
  ▴ₗ {{s-a}} a = cst a
  ▴ₗ {{v-s}} a = ▴ a
  ▴ₗ {{v-v}} a = ▴ a
  ▴ₗ {{a-s}} a = a
  ▴ₗ {{ t = a-a {args = n-n} }} a = a
  ▴ₗ {{ t = a-a {args = n-0} }} a = a
  ▴ₗ {{ t = a-a {args = 0-n} }} a = cst (Ar.sel a [])

  ▴ᵣ : ∀ {X A B d s} {{t : DyScalVec X A B d s}} → B → Ar X d s
  ▴ᵣ {{s-s}} b = cst b
  ▴ᵣ {{s-v}} b = ▴ b
  ▴ᵣ {{s-a}} b = b
  ▴ᵣ {{v-s}} b = cst b
  ▴ᵣ {{v-v}} b = ▴ b
  ▴ᵣ {{a-s}} b = cst b
  ▴ᵣ {{ t = a-a {args = n-n} }} b = b
  ▴ᵣ {{ t = a-a {args = n-0} }} b = cst (Ar.sel b [])
  ▴ᵣ {{ t = a-a {args = 0-n} }} b = b
  
  lift : ∀ {X A B d s}{{t : DyScalVec X A B d s}} → A → B → (_⊕_ : X → X → X) → Ar X d s
  lift {{ t }} a b _⊕_ = imap λ iv → Ar.sel (▴ₗ a) iv ⊕ Ar.sel (▴ᵣ b) iv

\end{code}

Extraction challenges.

