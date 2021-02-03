\begin{code}[hide]
open import Data.Nat
open import Data.String
open import Data.List
open import Data.Unit
open import Function
open import Reflection
module _ where
postulate
  ⋯ : ∀ {a}{A : Set a} → A
\end{code}
\section{Extraction Framework}

On a very high level, extraction process translates reflected
Agda term into the backend language of interest.  However, when
considering actual details, the process becomes much more challenging.
We have challenges of embedding:
\begin{enumerate}
  \item how much do we want to mimic the original syntax? See
  Sections~\ref{sec:array} and~\ref{sec:apl} for more details.
  \item how do we make sure that our embedding is normalisation-friendly,
  so that trivial optimisations are performed prior the extraction.
\end{enumerate}
We have challenges related to Agda's choice of internal representation:
sometimes we do not have the necessary information, or we cannot control
what information is being reflected.  In such cases we had to modify
Agda to accommodate our needs.
Finally, we have reflection challenges that have to do with the actual
translation: matching embedded encoding against the actual language or
dealing with type difference in type systems.

In this section we start with the general overview of the framework
and mainly focus on language-independent parts of the extraction.
To facilitate with examples we are going to use a very simple language
called Kaleidoscope~\cite{}.

\paragraph{Overview of the framework}
The entry point of the extraction is the following parametrised module:
\begin{code}
data Err {ℓ} (A : Set ℓ) : Set ℓ where
  error : String → Err A
  ok    : A → Err A
Prog = Err String

-- State Monad with some commonly pre-defined fields
SKS : Set → Set
SKS = ⋯

module Extract (kompile-fun : Type → Term → Name → SKS Prog) where
  macro
    kompile : Name → Names → Names → (Term → TC ⊤)
    kompile n base skip hole = ⋯
\end{code}
The parameter \AF{kompile-fun} is the actual language-specific
function that would do the extraction.  The interface function
\AF{kompile} obtains the definition of the Agda function named
\AB{n} and all the function that are found on the call
graph of \AB{n} using \AF{kompile-fun}.  It returns
a concatenation of all the extracted functions, given that all of
them succeeded, or returns an error.  The latter is taken care by
the combination of the state monad \AF{SKS} and the \AF{Prog}
type.


The second and the third parameters of \AF{kompile} are lists of
names that control function inlining in the extracted terms and
traversal into the definitions found in the call graph.  We explain
these two properties at examples momentarily after we introduce
the first embedded language Kaleidoscope.

\subsection{Kaleidoscope}
We borrow the notion of Kaleidoskope from the tutorial~\cite{} on
building frontends to LLVM~\cite{}.  This is a minimalist first order
language where natural numbers is the only data type\footnote{Original
tutorial used floats, but in the context of Agda it is easier to use to
use natural numbers as we can prove more properties with them.}.
We support arithmetic operations and comparisons.  Boolean values
follow C convention where zero means false, and any other number means
true.  Function calls and conditionals operate as usual, let constructs
make it possible
to bind immutable variables to values.  We add a one-argument \AF{assert}
operator that terminates computation if its value evaluates to zero.
Finally, a function is given by name, list of arguments and the body
expression.  A declaration of external function is given by name and
arguments.  A possible encoding of Kaleidoskope's AST follow:

\begin{code}
  Id = String

  data Op : Set where
    Plus Minus Times Divide Eq Neq And Gt Lt : Op

  data Expr : Set where
    Nat      : ℕ → Expr
    BinOp    : Op → Expr → Expr → Expr
    Var      : String → Expr
    Call     : Id → List Expr → Expr
    Function : Id → List Id → Expr → Expr
    Extern   : Id → List Id → Expr
    Let      : Id → Expr → Expr → Expr
    Assert   : Expr → Expr
    If       : Expr → Expr → Expr → Expr
\end{code}

A recursive Fibonacci function is given as:
\begin{code}
  fib = Function "fib" ("n" ∷ []) $
        If (BinOp Lt (Var "n") (Nat 2))
           (Nat 1)
           (BinOp Plus (Call "fib" [ BinOp Minus (Var "n") (Nat 2) ])
                       (Call "fib" [ BinOp Minus (Var "n") (Nat 1) ]))
\end{code}

\subsection{Normalisation and Inlining}
\todo[inline]{Here we explain what is the meaning of the arguments
to kompile, and that we had to extend Agda in order to make this happen}

\subsection{Mapping Agda Types}
\todo[inline]{Here we mainly talk about what do we do with dependent types
and how do we collect constraints, and the role of assertions that we
generate --- they may be used as hints for target compiler optimisations.}

\subsection{Pattern Matching}
\todo[inline]{Explain how do we turn a pattern-matching function definition
into a single definition with a conditional inside.  We have to make sure
that we explained the telescopes (or explain them here), and we can
reiterate absurd patterns here.}

\subsection{Monadic Workaround for Lets}
\todo[inline]{Explain that we can workaround the lack of lets in the internal
syntax by introducing a fake monad; give an example.}


\subsection{Rewriting}
\todo[inline]{Explain how rewriting rules could be used as additional
optimisation steps prior extraction.  Mention that the availability of
telescopes (that Jesper added to Agda) facilitates pushing rewriting
under the function clauses, which used to be a nightmare.}

