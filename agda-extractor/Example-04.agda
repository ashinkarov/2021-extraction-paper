--{-# OPTIONS --verbose 10 #-}
open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat as N using (ℕ; zero; suc; _≤_; _≥_; _<_; s≤s; z≤n)
import      Data.Nat.DivMod as N
open import Data.Nat.Properties as N
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
import      Data.Vec.Properties as V
open import Data.Fin as F using (Fin; zero; suc; #_)
import      Data.Fin.Properties as F
open import Data.Product as Prod using (Σ; _,_; curry; uncurry) renaming (_×_ to _⊗_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import Function
open import ReflHelper

open import Array.Base
open import Array.Properties

open import APL2

open import Agda.Builtin.Float

-- Verbose facts about transitivity of <, ≤, and ≡
a≤b⇒b≡c⇒a≤c : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
a≤b⇒b≡c⇒a≤c a≤b refl = a≤b

a≤b⇒a≡c⇒b≡d⇒c≤d : ∀ {a b c d} → a ≤ b → a ≡ c → b ≡ d → c ≤ d
a≤b⇒a≡c⇒b≡d⇒c≤d a≤b refl refl = a≤b

a<b⇒0<b : ∀ {a b} → a < b → zero < b
a<b⇒0<b {a} a<b = ≤-trans (s≤s z≤n) a<b

a<b⇒c≤a⇒c<b : ∀ {a b c} → a < b → c ≤ a → c < b
a<b⇒c≤a⇒c<b a<b z≤n = a<b⇒0<b a<b
a<b⇒c≤a⇒c<b (s≤s a<b) (s≤s c≤a) = s≤s (a<b⇒c≤a⇒c<b a<b c≤a)

a≤b⇒c≤a⇒c≤b : ∀ {a b c} → a ≤ b → c ≤ a → c ≤ b
a≤b⇒c≤a⇒c≤b {a} {b} {c} a≤b c≤a = ≤-trans c≤a a≤b

A<B⇒B≤C⇒A≤C : ∀ {n}{ix s s₁ : Ar ℕ 1 (n ∷ [])}
             → ix <a s → s₁ ≥a s → s₁ ≥a ix
A<B⇒B≤C⇒A≤C {ix = imap x} {imap x₁} {imap x₂} ix<s ix≤s₁ iv = ≤-trans (<⇒≤ $ ix<s iv) (ix≤s₁ iv)

A≥B⇒A≡C⇒C≥B : ∀ {d s}{A B C : Ar ℕ d s}
             → A ≥a B → A =a C → C ≥a B
A≥B⇒A≡C⇒C≥B {A = imap x} {imap x₁} {imap x₂} A≥B A≡C iv rewrite (sym $ A≡C iv) = A≥B iv

-- Something that could go in Stdlib.

a≤a*b : ∀ {a b} → a ≤ a N.* suc b
a≤a*b {a} {b = zero} rewrite (*-identityʳ a) = ≤-refl
a≤a*b {a} {b = suc b} = ≤-trans a≤a*b (*-monoʳ-≤ a (≤-step ≤-refl))


a-s[b]+1≡a-b : ∀ {a b} → b < a →  a N.∸ suc b N.+ 1 ≡ a N.∸ b
a-s[b]+1≡a-b {a} {b} pf = begin
                     a N.∸ suc (b) N.+ 1  ≡⟨ sym $ N.+-∸-comm 1 pf ⟩
                     a N.+ 1 N.∸ suc b    ≡⟨ cong₂ N._∸_ (N.+-comm a 1) (refl {x = suc b}) ⟩
                     a N.∸ b
                   ∎
                   where open ≡-Reasoning

conv-ix-inb : ∀ {n}{ix s s₁ : Ar ℕ 1 (n ∷ [])}
            → (ix<s : ix <a s)
            → (s₁≥s : s₁ ≥a s)
            → (s₁ - ix) {≥ = A<B⇒B≤C⇒A≤C {s₁ = s₁} ix<s s₁≥s}
               ≥a ((s₁ - s) {≥ = s₁≥s} + ( 1))
conv-ix-inb {ix = imap ix} {imap s} {imap s₁} ix<s s₁≥s iv =
       let
         s₁-[1+ix]≥s₁-s = ∸-monoʳ-≤ (s₁ iv) (ix<s iv)
         s₁-[1+ix]+1≥s₁-s+1 = +-monoˡ-≤ 1 s₁-[1+ix]≥s₁-s
       in a≤b⇒b≡c⇒a≤c s₁-[1+ix]+1≥s₁-s+1 (a-s[b]+1≡a-b {a = s₁ iv} {b = ix iv} (≤-trans (ix<s iv) (s₁≥s iv)))


undo-lkptab : ∀ {n s₁}{ix : Ar ℕ 1 (n ∷ [])} (iv : Ix 1 (n ∷ [])) →
      V.lookup s₁ (ix-lookup iv zero) N.∸ sel ix iv ≡
      V.lookup (V.tabulate (λ i → V.lookup s₁ i N.∸ sel ix (i ∷ [])))
      (ix-lookup iv zero)
undo-lkptab {s₁ = s₁}{ix} (i ∷ []) = sym (V.lookup∘tabulate _ i)


-- conv ← {a←⍵ ⋄ w←⍺ ⋄ ⊃+/,w×{(1+(⍴a)-⍴w)↑⍵↓a}¨⍳⍴w}
infixr 20 _conv_
_conv_ : ∀ {n wₛ aₛ}
      → Ar Float n wₛ
      → Ar Float n aₛ
      → {≥ : ▴ aₛ ≥a ▴ wₛ}
      → Ar Float n $ ▾ ((aₛ - wₛ){≥} + 1)
_conv_ {n = n} {wₛ = s} {aₛ = s₁} w a {s₁≥s} = let
               sr = (s₁ - s) {≥ = s₁≥s} + 1
               idxs = ι ρ w

               rots ix ix<s = let
                  ~ix≥ρa = A<B⇒B≤C⇒A≤C ix<s s₁≥s
                  ix↓a = (ix ↓ a) {pf = ~ix≥ρa}
                  ~ix-inb = conv-ix-inb {s₁ = s→a s₁} ix<s s₁≥s
                  ~ρix↓a≥sr = A≥B⇒A≡C⇒C≥B ~ix-inb (undo-lkptab {s₁ = s₁}{ix = ix})
                  in
                  (sr ↑ ix↓a) {pf = ~ρix↓a≥sr }

               r = (uncurry rots) ̈ idxs
               mul = w ̈⟨ _×ᵣ_ ⟩ (subst-ar (a→s∘s→a s) r)
               res = reduce-1d _+ᵣ_ (cst 0.0) (, mul)
              in res

--kconv = kompile _conv_ (quote _≥a_ ∷ quote reduce-1d ∷ quote _↑_ ∷ quote _↓_ ∷ []) [] -- (quote reduce-1d ∷ [])


-- multiconv←{(a ws bs)←⍵⋄bs{⍺+⍵ conv a}⍤(0,(⍴⍴a))⊢ws}
multiconv : ∀ {n m s sw so} → (a : Ar Float n s)
          →  (ws : Ar (Ar Float n sw) m so)
          →  (bs : Ar Float m so)
          →  {≥ : ▴ s ≥a ▴ sw}
          →  Ar (Ar Float n $ ▾ ((s - sw){≥} + 1)) m so
multiconv a ws bs {≥} = bs ̈⟨ (λ α ω → α +ᵣ (ω conv a){≥}) ⟩ ws


--kmconv = kompile multiconv (quote _≥a_ ∷ quote reduce-1d ∷ quote _↑_ ∷ quote _↓_ ∷ []) [] -- (quote reduce-1d ∷ [])

