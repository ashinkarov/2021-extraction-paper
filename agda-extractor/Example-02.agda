open import ExtractSac as ES using ()
open import Extract (ES.kompile-fun)

open import Data.Nat
open import Data.List as L using (List; []; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)

open import Relation.Binary.PropositionalEquality

open import Reflection

open import Structures
open import ReflHelper
open import Function

open import Array.Base


-- Check that Vec² and List ∘ Vec are treated correctly.
-- Here we transpose a 2d array using Vec operations.
-- Note that we are using local where-defined functions.

test-20f : ∀ m n → Vec (Vec ℕ n) m → Vec (Vec ℕ m) n
test-20f 0       n []       = repl []
  where
    repl : ∀ {k} → Vec ℕ 0 → Vec _ k
    repl {0} x     = []
    repl {suc _} x = x ∷ repl x
test-20f (suc _) n (x ∷ xs) = xzip x (test-20f _ n xs)
  where
    xzip : ∀ {n} → Vec _ n → Vec _ n → Vec _ n
    xzip []       []       = []
    xzip (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ xzip xs ys

test₂₀ : kompile test-20f [] [] ≡ ok _
test₂₀ = refl

-- simplified version of the test20 for debugging purposes.
test-20f′ : ∀ n → Vec ℕ n → Vec (Vec ℕ 1) n → Vec (Vec ℕ 2) n
test-20f′ n xs ys = xzip xs ys
  where
    xzip : ∀ {n} → Vec _ n → Vec _ n → Vec _ n
    xzip []       []       = []
    xzip (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ xzip xs ys

test₂₀′ : kompile test-20f′ [] [] ≡ ok _
test₂₀′ = refl


-- Make sure that we can handle lists of hom. objects
test-21f : ∀ n → List (Vec ℕ n)
test-21f n = []

test₂₁ : kompile test-21f [] [] ≡ ok _
test₂₁ = refl



-- Test that cons and friends work on a simple example
test-22f : ∀ n → Vec (Vec ℕ n) 1
test-22f n = repl 0 ∷ []
 where
    repl : ∀ {m} → ℕ → Vec ℕ m
    repl {0} x     = []
    repl {suc _} x = x ∷ repl x

test₂₂ : kompile test-22f [] [] ≡ ok _
test₂₂ = refl

-- Test that polymorphic functions are failing with a reasonable error
test-23f : ∀ {X : Set} → X → X
test-23f x = x

test₂₃ : _≡_ {A = Prog} (kompile test-23f [] []) $ error _
test₂₃ = refl


-- FIXME: This gives a buggy assertion on the argument (that is not present)
test-24f : Vec ℕ (1 + 2)
test-24f = 1 ∷ 2 ∷ 3 ∷ []

test₂₄ : kompile test-24f [] [] ≡ ok _
test₂₄ = refl

-- Array stuff
test-25f : ℕ → Ar ℕ 1 V.[ 5 ]
test-25f n = cst n

test₂₅ : kompile test-25f [] [] ≡ ok _
test₂₅ = refl

-- Element-wise addition.
test-26f : ∀ {d s} → (a b : Ar ℕ d s) → Ar ℕ d s
test-26f a b = imap λ iv → sel a iv + sel b iv

test₂₆ : kompile test-26f [] [] ≡ ok _
test₂₆ = refl


test-27f : ∀ {d s} → (a b : Ar ℕ d s) → Ar ℕ d s
test-27f (imap a) (imap b) = imap λ iv → a iv + b iv

test₂₇ : kompile test-27f [] [] ≡ ok _
test₂₇ = refl

test-28f : ∀ {d s} → (a b : Ar ℕ d s) → Ar ℕ d s
test-28f (imap _) (imap a) = imap λ iv → a iv + 1

test₂₈ : kompile test-28f [] [] ≡ ok _
test₂₈ = refl


-- Testing for dot and absurd arguments of the imap.
test-29f : ∀ {d s} → (a b : Ar ℕ d s) → a ≡ b → Ar ℕ d s
test-29f (imap .a) (imap a) refl = imap λ iv → a iv + 1

test₂₉ : kompile test-29f [] [] ≡ ok _
test₂₉ = refl

-- We cannot write this:
--
-- open import Data.Empty
-- test-30f : Ar ⊥ 1 V.[ 1 ] → ⊥
-- test-30f (imap ())
--
-- even though `f` in imap has type Ix 1 [1] → ⊥, which doesn't exist.

-- If non-lambda is found as an argument of the imap.
test-31f : Ar ℕ 1 V.[ 10 ] → Ar ℕ 1 V.[ 10 ]
test-31f (imap f) = imap f

test₃₁ : kompile test-31f [] [] ≡ ok _
test₃₁ = refl

-- Index types
test-32f : Ix 2 (3 ∷ 4 ∷ []) → Fin 3
test-32f ix = ix-lookup ix (# 0)

test₃₂ : kompile test-32f [] [] ≡ ok _
test₃₂ = refl

module mat-mul where
  postulate
    asum : ∀ {n} → Ar ℕ 1 (n ∷ []) → ℕ


  mm : ∀ {m n k} → let Mat a b = Ar ℕ 2 (a ∷ b ∷ []) in
                  Mat m n → Mat n k → Mat m k
  mm (imap a) (imap b) = imap λ iv →
                                    let i = ix-lookup iv (# 0)
                                        j = ix-lookup iv (# 1)
                                    in asum (imap λ kv → let k = ix-lookup kv (# 0)
                                                         in a (i ∷ k ∷ []) * b (k ∷ j ∷ []))

  mm-kompiled = kompile mm [] (quote asum ∷ [])
  test₃₃ : mm-kompiled ≡ ok _
  test₃₃ = refl

-- This test ensurest that even if bound variables appear in
-- different order than in the telescope, we can still use them.
test-34f : ∀ {d s} → Ix (suc d) s → ℕ
test-34f {_}{x ∷ s} (_∷_ i ix) =  x

test-34t = kompile test-34f [] []
test₃₄ : test-34t ≡ ok ("\n\n// Function Example-02.test-34f\n"
                      ++ "int\nExample_02_test_34f(int x_1, int[.] x_2, int[.] x_4) {\n"
                      ++ "/* assert (dim (x_4) == (1 + x_1)) */\n/* assert (x_4 < x_2) */\n"
                      ++ "/* assert (shape (x_2)[[0]] == (1 + x_1)) */"
                      ++ "int __ret;\nd = x_1;\nx = hd (x_2);\ns = tl (x_2);\n"
                      ++ "i = hd (x_4);\nix = tl (x_4);\n__ret = x;\n"
                      ++ "return __ret;\n}\n\n")
test₃₄ = refl



test-35f : ∀ {d s} → Ix (suc d) s → ℕ
test-35f {_} (_∷_ {d}{s}{x} i ix) =  x

test₃₅ : kompile test-35f [] [] ≡ ok ("\n\n// Function Example-02.test-35f\n"
                                   ++ "int\nExample_02_test_35f(int x_1, int[.] x_2, int[.] x_4) {\n"
                                   ++ "/* assert (dim (x_4) == (1 + x_1)) */\n/* assert (x_4 < x_2) */\n"
                                   ++ "/* assert (shape (x_2)[[0]] == (1 + x_1)) */"
                                   ++ "int __ret;\nd = x_1;\nx = hd (x_2);\ns = tl (x_2);\n"
                                   ++ "i = hd (x_4);\nix = tl (x_4);\n__ret = x;\n"
                                   ++ "return __ret;\n}\n\n")
test₃₅ = refl




test-fold1 : ∀ {n} → Ar ℕ 1 V.[ n ] → Ar ℕ 1 V.[ n ]
test-fold1 a = imap λ iv → sel a iv + 5

test-fold : ∀ {n} → Ar ℕ 1 V.[ n ] → Ar ℕ 1 V.[ n ]
test-fold a = imap λ iv → sel (test-fold1 a) iv + 6
