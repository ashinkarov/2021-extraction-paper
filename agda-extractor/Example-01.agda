open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat
open import Data.Nat.Properties
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import Function


test-13f : ∀ {n} → Vec ℕ n → Vec ℕ (n + n * n) → ℕ
test-13f [] _      = 0
test-13f (x ∷ a) b = x
test₁₃ : kompile test-13f [] [] ≡ ok _
test₁₃ = refl


test-14f : ∀ {n} → Vec ℕ n → Vec ℕ (n) → Vec ℕ n
test-14f [] _ = []
test-14f (x ∷ a) (y ∷ b) = x + y ∷ test-14f a b
test₁₄ : kompile test-14f [] [] ≡ ok _
test₁₄ = refl


-- Note that rewrite helper function would generate
-- the equality type amongst its arguments.
test-15f : ∀ {a b} → Fin (a + b) → Fin (b + a)
test-15f {a}{b} x rewrite (+-comm a b) = x

test₁₅ : let fs = L.[ quote +-comm ] in
         kompile test-15f fs fs  ≡ ok _
test₁₅ = refl


module absurd-patterns where
  test-16f : ∀ {n} → Fin n → Fin n
  test-16f {0}     ()
  test-16f {suc n} i  = i

  test₁₆ : kompile test-16f [] []  ≡ ok _
  test₁₆ = refl

  -- Ugh, when we found an absurd pattern, the rest of the
  -- patterns may or may not be present (which seem to make no sense).
  -- If they are present, then other (missing) constructors are inserted
  -- automatically.  Therefore, extracted code for the function below
  -- would look rather scary.
  test-17f : ∀ {n} → Fin (n ∸ 1) → ℕ → ℕ → Fin n
  test-17f {0}       () (suc (suc k))
  test-17f {1}       ()
  test-17f {suc (suc n)} i m mm = zero

  test₁₇ : kompile test-17f [] []  ≡ ok _
  test₁₇ = refl

  -- These are tests from kaleidoscope that
  -- we also want to work in SaC
  test9-f : ∀ n → Fin n → ℕ → ℕ
  test9-f 0 () (suc x)
  test9-f n@(suc x) i k = n + k

  test4-f : (x : ℕ) → x ≡ 0 → (y : ℕ) → x ≡ y → ℕ
  test4-f x () (suc y) refl
  test4-f x x=0 zero x=y = 5


module divtest where
  open import Data.Nat.DivMod
  test-div : ℕ → ℕ
  test-div x = (3 + x) / 3
  ktestdiv : kompile test-div [] [] ≡ ok _
  ktestdiv = refl


-- Dot patterns
test-18f : ∀ m n → m ≡ n → Fin (suc m)
test-18f zero    .zero    refl = zero
test-18f (suc m) .(suc m) refl = suc (test-18f m m refl)

test₁₈ : kompile test-18f [] []  ≡ ok _
test₁₈ = refl

-- Increment the first column of the 2-d array expressed in vectors
test-19f : ∀ {m n} → Vec (Vec ℕ n) m → Vec (Vec ℕ n) m
test-19f []               = []
test-19f ([] ∷ xss)       = [] ∷ test-19f xss
test-19f ((x ∷ xs) ∷ xss) = (x + 1 ∷ xs) ∷ test-19f xss

test₁₉ : kompile test-19f [] []  ≡ ok _
test₁₉ = refl

