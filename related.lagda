\section{\label{sec:related}Related Work}

In a dependently-typed language such restrictions can be achieved by
constructing a universe.  The strength of restrictions presents us an
entire spectrum ranging from weak to strong.  Let us demonstrate a
universe that restricts function types.
\begin{code}[hide]
module _ where
module Univ where
  --open Problem
  open import Data.Nat
  open import Data.Fin using (Fin; zero; suc)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Nat.DivMod
  open import Data.Nat.Show renaming (show to showNat)
  open import Data.String using (length)
  open import Data.Bool hiding (_<_)
  open import Function

  postulate
    ⋯ : ∀ {a}{A : Set a} → A
\end{code}
\begin{mathpar}
\codeblock{%
\begin{code}
  data Ty : Set ; ⟦_⟧ : Ty → Set
  data Ty where
    nat   : Ty
    fin   : ⟦ nat ⟧ → Ty
    eq lt : (a b : ⟦ nat ⟧) → Ty

  ⟦ nat ⟧    = ℕ
  ⟦ fin x ⟧  = Fin x
  ⟦ eq a b ⟧ = a ≡ b
  ⟦ lt a b ⟧ = a < b
\end{code}
}
\and
\codeblock{%
\begin{code}
  data n-σ : Set where
    ⟨_⟩   : Ty → n-σ
    _▹_ : (τ : Ty) → (⟦ τ ⟧ → n-σ) → n-σ

  I : n-σ → Set
  I ⟨ τ ⟩   = ⟦ τ ⟧
  I (τ ▹ P) = (t : ⟦ τ ⟧) → I (P t)

  ex₁ : I $ nat ▹ λ m → nat ▹ λ n → lt m n ▹ λ m<n → ⟨ fin n ⟩
\end{code}
}
\end{mathpar}
\begin{code}[hide]
  ex₁ = ⋯
\end{code}
We first define a universe of base types \AD{Ty} and its interpretation
\AD{⟦\_⟧}.  Then we define a universe of $n$-fold dependent tuples of
\AD{Ty}s, (a tuple where elements on the right may depend on all the
previous elements) and its interpretation \AF{I} into dependent function
space.

Given that \AD{n-σ} contains only interpretations of valid types, it
might seem that functions of type \AD{I e} guarantee correct extraction.
Unfortunately it does not.  We still have the problem demonstrated in \AF{ex}
example --- the terms are not restricted enough.  More importantly,
as types may depend on terms we can write:
\begin{code}
  ex₂ : I $ nat ▹ λ n → ⟨ fin $ length $ showNat n ⟩ ; ex₂ = ⋯
  ex₃ : I $ nat ▹ λ n → if n % 2 ≡ᵇ 0 then ⟨ nat ⟩ else ⟨ lt n 42 ⟩ ; ex₃ = ⋯
\end{code}
The argument to \AC{fin} is an unrestricted term, therefore we can write
\AC{fin} \AF{ex} \AB{n} in \AF{ex₂}. The \AC{\_▹\_} constructor of \AD{n-σ} uses
unrestricted lambdas to bind variables, therefore \AF{ex₃}.

Many approaches show~\cite{} how further restrictions can be added to the
terms, which essentially brings forces us to define deep embedding.  The
problem with these approaches is that the encoding becomes very non-trivial
to use.  The essence of the problem is that in order to solve \AD{ex₃} problem
we need to handle variables explicitly.  This means that we have to parametrise
our types and terms by contexts.  Approaches such as~\cite{} require explicit
weakening, substitution and type equality as a part of the embedded language
encoding.  McBride's work on Kipling~\cite{} shows how one could avoid some
of these artefacts, but the resulting embedding is still very non-trivial to
use.  Most importantly, in both cases, any existing Agda code
such as properties about data types that we can find in the standard library
will have to be internalised in the embedding.
