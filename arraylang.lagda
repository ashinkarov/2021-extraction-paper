\section{\label{sec:array}Array Language}
\subsection{Functional Arrays}
\begin{code}[hide]
module _ where
  open import Data.Vec using (Vec; []; _∷_)
  open import Data.Nat
  open import Data.Fin
  open import Function
  infixr 5 _∷_
\end{code}

We encode arrays as follows.
\begin{code}
  data Ix : (d : ℕ) → (s : Vec ℕ d) → Set where
    []   : Ix 0 []
    _∷_  : ∀ {d s x} → Fin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)

  record Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
    constructor imap
    field sel : Ix d s → X
\end{code}

Consider a simple example:

\begin{code}[hide]
  open Ar public
  postulate
    sum : ∀ {n} → Ar ℕ 1 (n ∷ []) → ℕ
\end{code}
\begin{code}
  mm : ∀ {a b c} → let Mat x y = Ar ℕ 2 (x ∷ y ∷ []) in Mat a b → Mat b c → Mat a c
  mm (imap a) (imap b) = imap body where
     body : _
     body (i ∷ j ∷ []) = sum $ imap λ where (k ∷ []) → a (i ∷ k ∷ []) * b (k ∷ j ∷ [])
\end{code}

\subsection{Target Language}
Our target language is SaC.
\todo[inline]{Steal the language introduction from one of the papers.}
