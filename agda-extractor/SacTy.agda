open import Structures
open import Data.String using (String)
open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.List as L using (List; []; _∷_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function using (_$_)


data Nesting : Set where
  hom : Nesting
  nes : Nesting

data SacTy : Set where
  unit  : SacTy
  int   : SacTy
  float : SacTy
  bool  : SacTy
  char  : SacTy
          -- Nested `n`-dimensional array is isomorphic to Listⁿ
          -- Homogeneous `n`-dimensional array is isomorphic to Vecⁿ
          -- The first argument does not tell whether the entire array needs
          -- to be implemented as nested or not (just an annotation), e.g:
          --    akd hom (akd nest nat 3)
          --    akd nes nat 2
          --    akd nes (akd nes nat 1)
          -- and so on.  In actual sac (with no support for nested arrays)
          -- it all collapses to three cases, but it is convenient to keep
          -- this distinction in the model.
  aud   : Nesting → SacTy → (sh : Prog) → SacTy
  akd   : Nesting → SacTy → (sh : Prog) → ℕ → SacTy
  aks   : Nesting → SacTy → (sh : Prog) → (n : ℕ) → Vec ℕ n → SacTy

data SacBase : SacTy → Set where
  unit  : SacBase unit
  int   : SacBase int
  float : SacBase float
  bool  : SacBase bool
  char  : SacBase char

data SacArray : SacTy → Set where
  aud : ∀ {n? τ es} → SacArray (aud n? τ es)
  akd : ∀ {n? τ es n} → SacArray (akd n? τ es n)
  aks : ∀ {n? τ es n s} → SacArray (aks n? τ es n s)


array-or-base : ∀ τ → SacBase τ ⊎ SacArray τ
array-or-base unit = inj₁ unit
array-or-base int = inj₁ int
array-or-base float = inj₁ float
array-or-base bool = inj₁ bool
array-or-base char = inj₁ char
array-or-base (aud x τ es) = inj₂ aud
array-or-base (akd x τ es x₁) = inj₂ akd
array-or-base (aks x τ es n x₁) = inj₂ aks


is-base : ∀ τ → Dec (SacBase τ)
is-base τ with array-or-base τ
... | inj₁ bt = yes bt
... | inj₂ aud = no λ ()
... | inj₂ akd = no λ ()
... | inj₂ aks = no λ ()

is-array : ∀ τ → Dec (SacArray τ)
is-array τ with array-or-base τ
... | inj₂ ar = yes ar
... | inj₁ unit = no λ ()
... | inj₁ int = no λ ()
... | inj₁ float = no λ ()
... | inj₁ bool = no λ ()
... | inj₁ char = no λ ()

-- Is it the case that the entire array can be implemented
-- as a flattened homogeneous (multi-dimensional) array.
nested? : SacTy → Nesting
nested? unit = hom
nested? int = hom
nested? float = hom
nested? bool = hom
nested? char = hom
nested? (aud hom τ _) = nested? τ
nested? (aud nes _ _) = nes
nested? (akd hom τ _ _) = nested? τ
nested? (akd nes _ _ _) = nes
nested? (aks hom τ _ _ _) = nested? τ
nested? (aks nes _ _ _ _) = nes


get-base : SacTy → Σ[ τ ∈ SacTy ] SacBase τ
get-base unit = unit , unit
get-base int = int , int
get-base float = float , float
get-base bool = bool , bool
get-base char = char , char
get-base (aud x τ es) = get-base τ
get-base (akd x τ es x₁) = get-base τ
get-base (aks x τ es n x₁) = get-base τ


bt-tostring : ∀ {τ} → SacBase τ → String
bt-tostring unit = "unit"
bt-tostring int = "int"
bt-tostring float = "float"
bt-tostring bool = "bool"
bt-tostring char = "char"

postfix-aud = "[*]"

postfix-akd : ℕ → String
postfix-akd n = "[" ++ ("," ++/ L.replicate n ".") ++ "]"

postfix-aks : (n : ℕ) → Vec ℕ n → String
postfix-aks n s = "[" ++ ("," ++/ L.map showNat (V.toList s)) ++ "]"

bt : SacTy → String
bt τ = bt-tostring (proj₂ $ get-base τ)

sacty-to-string : SacTy → String
sacty-to-string σ with array-or-base σ
sacty-to-string σ | inj₁ bt = bt-tostring bt
sacty-to-string σ | inj₂ (aud {nes} {τ}) = sacty-to-string τ ++ postfix-aud
sacty-to-string σ | inj₂ (aud {hom} {τ}) with nested? τ
... | hom = bt τ  ++ postfix-aud
... | nes = sacty-to-string τ ++ postfix-aud

sacty-to-string σ | inj₂ (akd {nes} {τ} {_} {n}) = sacty-to-string τ ++ postfix-akd n
sacty-to-string σ | inj₂ (akd {hom} {τ} {_} {n}) with nested? τ
... | nes = sacty-to-string τ ++ postfix-akd n
... | hom with array-or-base τ
... | inj₁ bt =
           bt-tostring bt ++ postfix-akd n
... | inj₂ aud =
           --(τ[*])[.,.,.]   → τ([.,.,.] ++ [*])   = τ[*]
           bt τ ++ postfix-aud
... | inj₂ (akd {n = m}) =
           --(τ[.,.])[.,.,.] → τ([.,.,.] ++ [.,.]) = τ[.,.,., .,.]
           bt τ ++ postfix-akd (n + m)
... | inj₂ (aks {n = m}) =
           --(τ[5,6])[.,.,.] → τ([.,.,.] ++ [5,6]) = τ[.,.,., .,.]
           bt τ ++ postfix-akd (n + m)

sacty-to-string σ | inj₂ (aks {nes} {τ} {_} {n} {s}) = sacty-to-string τ ++ postfix-aks n s
sacty-to-string σ | inj₂ (aks {hom} {τ} {_} {n} {s}) with nested? τ
... | nes = sacty-to-string τ ++ postfix-aks n s
... | hom with array-or-base τ
... | inj₁ bt =
           bt-tostring bt ++ postfix-aks n s
... | inj₂ aud =
           -- (τ[*])[5,6]  → τ([5,6] ++ [*]) = τ[*]
           bt τ ++ postfix-aud
... | inj₂ (akd {n = m}) =
           --(τ[.,.])[5,6] → τ([5,6] ++ [.,.]) = τ[.,.,.,.]
           bt τ ++ postfix-akd (n + m)
... | inj₂ (aks {s = s′}) =
           --(τ[7,8])[5,6] → τ([5,6] ++ [7,8]) = τ[5,6,7,8]
           bt τ ++ postfix-aks _ (s V.++ s′)


-- For some rare cases we can eliminate nesting
-- Note that this function does not recurse, as:
--    a: List (hom X)         ~  Vec (hom X) (length a)
-- but
--    a: List (List (hom X))  ≁  Vec (Vec X _) _
sacty-normalise : SacTy → SacTy
sacty-normalise τ with array-or-base τ
sacty-normalise τ | inj₁ bt  = τ
sacty-normalise τ | inj₂ aud = τ
sacty-normalise τ | inj₂ (akd {hom}) = τ
sacty-normalise τ | inj₂ (akd {nes} {σ} {es} {0}) = -- There is no need to nest a 0-dimensional array
                                               akd hom σ es 0
sacty-normalise τ | inj₂ (akd {nes} {σ} {es} {1}) = -- Nested array of depth 1 of homogeneous elements
                                               -- is the same as homogeneous of dimension 1.
                                               akd hom σ es 1
sacty-normalise τ | inj₂ (akd {nes} {_} {_}) = τ
sacty-normalise τ | inj₂ (aks {hom}) = τ
sacty-normalise τ | inj₂ (aks {nes} {σ} {es} {n} {s}) = aks hom σ es n s


sacty-shape : SacTy → Prog
sacty-shape τ with array-or-base τ
... | inj₁ bt = ok $ "[]"
... | inj₂ (aud {hom} {σ} {s}) = s ⊕ " ++ "  ⊕ sacty-shape σ
... | inj₂ (aud {nes} {σ} {s}) = error $ "sacty-shape: nested-array `" ++ sacty-to-string τ ++ "`"
... | inj₂ (akd {hom} {σ} {s}) = s ⊕ " ++ "  ⊕ sacty-shape σ
... | inj₂ (akd {nes} {σ} {s}) = error $ "sacty-shape: nested-array `" ++ sacty-to-string τ ++ "`"
... | inj₂ (aks {hom} {σ} {s}) = s ⊕ " ++ "  ⊕ sacty-shape σ
... | inj₂ (aks {nes} {σ} {s}) = error $ "sacty-shape: nested-array `" ++ sacty-to-string τ ++ "`"
