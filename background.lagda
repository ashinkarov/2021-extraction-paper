\begin{code}[hide]
open import Data.List
open import Data.Nat
module _ where
\end{code}
\section{Background}
\subsection{Agda Basics}
\todo[inline]{Amongst other things we need to explain with-clauses
and pattern-matching functions.  Maybe records and their eta-equality.}


\subsection{Dependent types}
\subsection{Reflection and Internal Syntax}
Reflection is the ability to tern an arbitrary Agda expression
into some represenation and back.  A very similar idea to Lisp's
metaprogramming, except in a dependently-typed setting.  Consider
an example:
\begin{code}[hide]
module FunExample where
  open import Reflection
  open import Data.Unit
  open import Data.Product
\end{code}
\begin{code}
  foo : ℕ → ℕ
  foo x = x + x

  `foo = function
         (Clause.clause
          (("x" , vArg (def (quote ℕ) [])) ∷ [])
           (vArg (Pattern.var 0) ∷ [])
           (def (quote _+_) (vArg (var 0 []) ∷ vArg (var 0 []) ∷ []))
         ∷ []) 
\end{code}


\begin{code}[hide]
module TermLang where
  postulate
    Sort   : Set
    Clause : Set
    Name : Set
    Visibility : Set
    Literal : Set
    Meta : Set
  data Arg {a} (A : Set a) : Set a where
  data Abs {a} (A : Set a) : Set a where
  data Term : Set
  Type = Term
\end{code}

The actual innternal data representation is very compact:
\begin{code}
  data Term where
    var       : (x : ℕ) (args : List (Arg Term)) → Term
    con       : (c : Name) (args : List (Arg Term)) → Term
    def       : (f : Name) (args : List (Arg Term)) → Term
    lam       : (v : Visibility) (t : Abs Term) → Term
    pat-lam   : (cs : List Clause) (as : List (Arg Term)) → Term
    pi        : (a : Arg Type) (b : Abs Type) → Term
    agda-sort : (s : Sort) → Term
    lit       : (l : Literal) → Term
    meta      : (x : Meta) → List (Arg Term) → Term
    unknown   : Term

  data Definition : Set where
    function    : (cs : List Clause) → Definition
    data-type   : (pars : ℕ) (cs : List Name) → Definition
    record-type : (c : Name) (fs : List (Arg Name)) → Definition
    data-cons   : (d : Name) → Definition
    axiom       : Definition
    prim-fun    : Definition
\end{code}
