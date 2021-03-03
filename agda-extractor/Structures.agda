{-# OPTIONS --safe #-}
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Fin as F using (Fin; zero; suc)

open import Reflection using (TC)
open import Reflection.Name using (Names)
import Reflection.TypeChecking.Monad.Categorical as RCat

open import Category.Monad.State using (State; StateT; StateMonad; StateTMonad)
open import Category.Monad using (RawMonad)

--open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
import      Relation.Unary as UR
open import Relation.Nullary.Negation using (contradiction)

open import Function


-- This is a `Maybe`-like data type except that nothing
-- is extended with a string argument, to carry around the error.
data Err {a} (A : Set a) : Set a where
  error : String → Err A
  ok : A → Err A

-- Our representation for programs: it is either a string containing
-- textual representation of the extracted program or an error that
-- happened during extraction.
Prog = Err String

-- Simply for convenience
Strings = List String

-- We define a custom RawMonoid to add `_++/_` (list join)
-- an its overloadings.
record RawMonoid {a}(A : Set a) : Set a where
  field
    _++_ : A → A → A
    ε : A
  _++/_ : (delim : A) → List A → A
  d ++/ [] = ε
  d ++/ (x ∷ []) = x
  d ++/ (x ∷ xs) = x ++ d ++ d ++/ xs

  infixr 5 _++_

open RawMonoid {{...}} public


instance
  monoidLst : ∀ {a}{A : Set a} → RawMonoid (List A)
  monoidLst {A = A} = record {
    _++_ = λ a b → (Data.List._++_ $! a) $! b ;
    ε = []
    }

  monoidStr : RawMonoid String
  monoidStr = record {
    _++_ = λ a b → (Data.String._++_ $! a) $! b;
    ε = ""
    }

  monoidErrStr : RawMonoid (Err String)
  monoidErrStr = record {
    _++_ =  λ where
      (error s) _ → error s
      _ (error s) → error s
      (ok s₁) (ok s₂) → ok (s₁ ++ s₂)
    ;
    ε = ok ""
    }

-- Simplify handling concatenation of `Prog`s and `String`s
data Err++Ty : Set → Set → Set where
  instance
    s-s : Err++Ty String String
    e-s : Err++Ty Prog String
    s-e : Err++Ty String Prog
    e-e : Err++Ty Prog Prog

infixr 5 _⊕_
_⊕_ : ∀ {A B}{{t : Err++Ty A B}} → A → B → Prog
_⊕_ {{t = s-s}} a         b = ok $! (a ++ b)
_⊕_ {{t = e-s}} (error x) b = error $! x
_⊕_ {{t = e-s}} (ok x)    b = ok $! (x ++ b)
_⊕_ {{t = s-e}} a (error x) = error $! x
_⊕_ {{t = s-e}} a    (ok x) = ok $! (a ++ x)
_⊕_ {{t = e-e}} a         b = id $! (a ++ b)


-- The state used at the top-most and term-level compilation.
record KS : Set where
  constructor ks
  field funs : Names   -- Functions to compile
        base : Names   -- Atomic functions that we do not traverse into.
        done : Names   -- Functions that we have processed.
        defs : Prog    -- Definitions such as lifted functions, function declarations, etc.
        cnt  : ℕ       -- Source of fresh variables

defaultKS = ks [] [] [] ε 1

SKS = State KS
TCS = StateT KS TC

instance
  monadTC = RCat.monad

  monadTCS : RawMonad TCS
  monadTCS = StateTMonad KS monadTC

  monadSKS : ∀ {S : Set} → RawMonad (State S)
  monadSKS {S} = StateMonad S

  monadErr : ∀ {f} → RawMonad {f} Err
  monadErr = record {
    return = ok ;
    _>>=_ = λ { (error s) f → error s ; (ok a) f → f a }
    }

lift-state : ∀ {f}{M}{RM : RawMonad {f} M}{A}{S} → M A → StateT S M A
lift-state {RM = RM} x = λ s → return (_, s) ⊛ x
          where open RawMonad RM


lift-mstate : ∀ {f}{M}{RM : RawMonad {f} M}{A}{S} → State S A → StateT S M A
lift-mstate {RM = RM}{S = S} sa = λ s → return (sa s)
                          where open RawMonad RM

-- Modify error message in Prog, in case Prog is error.
err-modify : Prog → (String → String) → Prog
err-modify (error s) f = error (f s)
err-modify p _ = p

-- Check if there exists an element in the list that satisfies the predicate P.
list-has-el : ∀ {a b}{A : Set a}{P : UR.Pred A b} → UR.Decidable P → List A → Bool
list-has-el P? [] = false
list-has-el P? (x ∷ xs) with P? x
... | yes _ = true
... | no  _ = list-has-el P? xs

-- Check if there exists an element in the list that satisfies the predicate P.
list-find-el : ∀ {a b}{A : Set a}{P : UR.Pred A b} → UR.Decidable P → List A → Maybe A
list-find-el P? [] = nothing
list-find-el P? (x ∷ xs) with P? x
... | yes _ = just x
... | no  _ = list-find-el P? xs

list-update-fst : ∀ {a b}{A : Set a}{P : UR.Pred A b} → UR.Decidable P → List A → (A → A) → List A
list-update-fst P? [] f = []
list-update-fst P? (x ∷ xs) f with P? x
... | yes _ = f x ∷ xs
... | no  _ = x ∷ list-update-fst P? xs f


list-filter : ∀ {a b}{A : Set a}{P : UR.Pred A b} → UR.Decidable P → List A → List A
list-filter P? [] = []
list-filter P? (x ∷ xs) with P? x
... | yes _ = x ∷ list-filter P? xs
... | no  _ = list-filter P? xs


dec-neg :  ∀ {a b}{A : Set a}{P : UR.Pred A b} → UR.Decidable P → UR.Decidable (UR._∉ P)
dec-neg P? x with P? x
... | yes p = no λ ¬p → contradiction p ¬p
... | no ¬p = yes ¬p


vec-find-el-idx : ∀ {a b}{A : Set a}{n}{P : UR.Pred A b} → UR.Decidable P → Vec A n → Maybe (Fin n × A)
vec-find-el-idx P? [] = nothing
vec-find-el-idx P? (x ∷ xs) with P? x
... | yes _ = just (zero , x)
... | no  _ with vec-find-el-idx P? xs
... | just (i , x′) = just (suc i , x′)
... | nothing = nothing
