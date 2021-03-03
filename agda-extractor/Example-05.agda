open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat as N using (ℕ; zero; suc; _≤_; _≥_; _<_; _>_; s≤s; z≤n; _∸_)
import      Data.Nat.DivMod as N
open import Data.Nat.Properties as N
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
import      Data.Vec.Properties as V
open import Data.Fin as F using (Fin; zero; suc; #_)
import      Data.Fin.Properties as F
open import Data.Product as Prod using (Σ; _,_; curry; uncurry) renaming (_×_ to _×ₜ_)
open import Data.String

open import Relation.Binary.PropositionalEquality

open import Structures
open import Function

open import Array.Base
open import Array.Properties

open import APL2
open import Agda.Builtin.Float

open import Reflection
open import ReflHelper


pattern I0 = (zero ∷ [])
pattern I1 = (suc zero ∷ [])
pattern I2 = (suc (suc zero) ∷ [])
pattern I3 = (suc (suc (suc zero)) ∷ [])


-- backin←{(d w in)←⍵⋄⊃+/,w{(⍴in)↑(-⍵+⍴d)↑⍺×d}¨⍳⍴w}
backin : ∀ {n s s₁} → (inp : Ar Float n s)
                     → (w : Ar Float n s₁)
                     → {≥ : ▴ s ≥a ▴ s₁}
                     → (d : Ar Float n $ ▾ ((s - s₁){≥} + 1))
                     → Ar Float n s
backin {n}{s}{s₁} inp w d = let
      ixs = ι ρ w
      use-ixs i,pf = let
        i , pf = i,pf
        iv = a→ix i (ρ w) pf
        wᵢ = sel w (subst-ix (λ i → V.lookup∘tabulate _ i) iv)
        x = (i + ρ d) -↑⟨ 0.0 ⟩ (d ×ᵣ wᵢ)
        y = (ρ inp) ↑⟨ 0.0 ⟩ x
        in y
      s = reduce-1d _+ᵣ_ (cst 0.0) (, use-ixs ̈ ixs)
  in subst-ar (λ i → V.lookup∘tabulate _ i) s


kbin = kompile backin (quote _≥a_ ∷ quote reduce-1d ∷ quote _↑⟨_⟩_ ∷ quote _-↑⟨_⟩_ ∷ quote a→ix ∷ []) []


s-w+1≤s : ∀ {s w} → s ≥ w → s > 0 → w > 0 → s N.∸ w N.+ 1 ≤ s
s-w+1≤s {suc s} {suc w} (s≤s s≥w) s>0 w>0 rewrite (+-comm (s ∸ w) 1) = s≤s (m∸n≤m s w)
helper : ∀ {n} {sI sw : Vec ℕ n}
       → s→a sI ≥a s→a sw
       → (cst 0) <a s→a sI
       → (cst 0) <a s→a sw
       → (iv : Ix 1 (n ∷ []))
       → V.lookup sI (ix-lookup iv zero) ≥
         V.lookup (V.tabulate (λ i → V.lookup sI i ∸ V.lookup sw i N.+ 1))
         (ix-lookup iv zero)
helper {sI = sI} {sw} sI≥sw sI>0 sw>0 (x ∷ [])
       rewrite (V.lookup∘tabulate (λ i → V.lookup sI i ∸ V.lookup sw i N.+ 1) x) =
       s-w+1≤s (sI≥sw (x ∷ [])) (sI>0 (x ∷ [])) (sw>0 (x ∷ [])) 


a≤b⇒b≡c⇒a≤c : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
a≤b⇒b≡c⇒a≤c a≤b refl = a≤b
-- sI - (sI - sw + 1) + 1 = sw
shape-same : ∀ {n} {sI sw : Vec ℕ n}
           → s→a sI ≥a s→a sw
           → (cst 0) <a s→a sI
           → (cst 0) <a s→a sw
           → (i : Fin n)
           → V.lookup
             (V.tabulate
              (λ i₁ →
                 V.lookup sI i₁ ∸
                 V.lookup (V.tabulate (λ i₂ → V.lookup sI i₂ ∸ V.lookup sw i₂ N.+ 1)) i₁
                 N.+ 1))
             i
             ≡ V.lookup sw i
shape-same {suc n} {x ∷ sI} {y ∷ sw} I≥w I>0 w>0 zero =
  begin
    x ∸ (x ∸ y N.+ 1) N.+ 1 ≡⟨ sym $ +-∸-comm  {m = x} 1 {o = (x ∸ y N.+ 1)}  (s-w+1≤s (I≥w I0) (I>0 I0) (w>0 I0)) ⟩
    x N.+ 1 ∸ (x ∸ y N.+ 1) ≡⟨ cong (x N.+ 1 ∸_) (sym $ +-∸-comm {m = x} 1 {o = y} (I≥w I0)) ⟩
    x N.+ 1 ∸ (x N.+ 1 ∸ y) ≡⟨ m∸[m∸n]≡n {m = x N.+ 1} {n = y} (a≤b⇒b≡c⇒a≤c (≤-step $ I≥w I0) (+-comm 1 x)) ⟩
    y
  ∎
  where open ≡-Reasoning
shape-same {suc n} {x ∷ sI} {x₁ ∷ sw} I≥w I>0 w>0 (suc i) =
  shape-same {sI = sI} {sw = sw} (λ { (i ∷ []) → I≥w (suc i ∷ []) })
                                 (λ { (i ∷ []) → I>0 (suc i ∷ []) })
                                 (λ { (i ∷ []) → w>0 (suc i ∷ []) }) i



{-backmulticonv ← {
  (d_out weights in bias) ← ⍵
  d_in ← +⌿d_out {backin ⍺ ⍵ in} ⍤((⍴⍴in), (⍴⍴in)) ⊢ weights
  d_w ← {⍵ conv in} ⍤(⍴⍴in) ⊢ d_out
  d_bias ← backbias ⍤(⍴⍴in) ⊢ d_out
  d_in d_w d_bias
}-}
backmulticonv : ∀ {n m}{sI sw so}
              → (W : Ar (Ar Float n sw) m so)
              → (I : Ar Float n sI)
              → (B : Ar Float m so)
                -- We can get rid of these two expressions if we rewrite
                -- the convolution to accept s+1 ≥ w, and not s ≥ w.
              → {>I : (cst 0) <a s→a sI}
              → {>w : (cst 0) <a s→a sw}
              → {≥ : s→a sI ≥a s→a sw}
              → (δo : Ar (Ar Float n (a→s $ (s→a sI - s→a sw) {≥} + 1)) m so)
              → (typeOf W) ×ₜ (typeOf I) ×ₜ (typeOf B)
backmulticonv {n} {sI = sI} {sw} {so} W I B {sI>0} {sw>0} {sI≥sw} δo = let
    δI = reduce-1d _+ᵣ_ (cst 0.0) (, (W ̈⟨ (λ x y → backin I x {sI≥sw} y) ⟩ δo))
    δW = (λ x → (x conv I) {≥ = λ { iv@(i ∷ []) → subst₂ _≤_ (sym $ V.lookup∘tabulate _ i) refl
                                                  $ s-w+1≤s (sI≥sw iv) (sI>0 iv) (sw>0 iv) } }) ̈ δo
    δB = backbias ̈ δo
  in (imap (λ iv → subst-ar (shape-same {sI = sI} {sw = sw} sI≥sw sI>0 sw>0) (sel δW iv)) ,
     δI ,
     imap (λ iv → ▾ (sel δB iv)))
  where open import Example-04
        open import Example-03



conv-fns : List (String ×ₜ Name)
conv-fns = ("blog" , quote blog)
         ∷ ("backbias" , quote backbias)
         ∷ ("logistic" , quote logistic)
         ∷ ("meansqerr" , quote meansqerr)
         ∷ ("backavgpool" , quote backavgpool)
         ∷ ("avgpool" , quote avgpool)
         ∷ ("conv" , quote _conv_)
         ∷ ("multiconv" , quote multiconv)
         ∷ ("backin", quote backin)
         ∷ ("backmulticonv" , quote backmulticonv)
         ∷ []
  where open import Example-03
        open import Example-04

