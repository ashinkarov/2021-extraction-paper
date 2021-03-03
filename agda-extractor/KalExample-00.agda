open import Kaleid as K
open import Extract (K.kompile-funp) using (kompile)
open import ReflHelper

open import Data.Nat
open import Data.Nat.Properties
open import Data.List as L using (List; []; _∷_)

open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Reflection hiding (_≟_; _>>=_; return)

open import Structures
open import Function


test1-f : ℕ → ℕ
test1-f x = 1 + x

test₁ : kompile test1-f [] [] ≡ ok _
test₁ = refl


test2-f : ℕ → ℕ → ℕ
test2-f (suc x) (suc y) = suc $ test2-f x y
test2-f _ _ = 0

test₂ : kompile test2-f [] [] ≡ ok _
test₂ = refl


test3-f : (a b : ℕ) → a ≡ b → ℕ
test3-f a b _ = a ∸ b

test₃ : kompile test3-f [] [] ≡ ok _
test₃ = refl

test4-f : (x : ℕ) → x ≡ 0 → (y : ℕ) → x ≡ y → ℕ
test4-f x () (suc y) refl
test4-f x x=0 zero x=y = 5


test₄ : kompile test4-f [] [] ≡ ok _
test₄ = refl

-- _>_ is not (yet) supported, so no test₅ for now.
test5-f : (x y : ℕ) → x > y → ℕ
test5-f 0 0 ()
test5-f 0 x@(suc _) _ = x
test5-f (suc x) y _ = x + y


test6-f : (x y : ℕ) → ℕ
test6-f x y with x ≟ y
... | yes pf = 1
... | _ = 2

test₆ = kompile test6-f (quote _≟_ ∷ []) []

test7-f : (n : ℕ) → Fin (suc (n * n))
test7-f n = fromℕ< ≤-refl


test8-f : ℕ → ℕ
test8-f x = let a = x * x + 3 * x + 5 in a + a


test-args : (a b c d : ℕ) → ℕ
test-args a b c d = a + b + c + d

test-args2 : (a b : ℕ) → ℕ
test-args2 a b = test-args a b a b

ackermann : ℕ → ℕ → ℕ
ackermann (suc m) 0       = ackermann m 1
ackermann (suc m) (suc n) = ackermann m $ ackermann (suc m) n
ackermann 0       n       = n + 1

assert-suc : Fin 2 → ℕ → ℕ
assert-suc (suc (suc ())) a
assert-suc zero a = a
assert-suc (suc zero) a = a + a

test9-f : ∀ n → Fin n → ℕ → ℕ
test9-f 0 () (suc x)
test9-f n@(suc x) i k = n + k


open import Data.Nat.DivMod
x<m⇒sx/2<m : ∀ x m → x < m → suc x / 2 < m
x<m⇒sx/2<m x m x<m = ≤-trans (m/n<m (suc x) 2 (s≤s z≤n) ≤-refl) x<m

log₂′ : ∀ {m} → (n : ℕ) → (n < m) → ℕ
log₂′ {m}     0         _     = 0
log₂′ {m}     1         _     = 0
log₂′ {suc m} n@(suc x) (n<m) = 1 + log₂′ {m = m} (n / 2) (x<m⇒sx/2<m x m $ ≤-pred n<m)

log₂ : ℕ → ℕ
log₂ x = log₂′ x ≤-refl

