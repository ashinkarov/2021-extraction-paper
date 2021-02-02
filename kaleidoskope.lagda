\begin{code}[hide]
open import Data.Nat
open import Data.String
open import Data.List
module _ where
\end{code}
\section{Kaleidoskope}
\subsection{Structure of the Language}
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

\subsection{Basic Extraction}
The basic points are:
\begin{enumerate}
   \item Overall interface of the framework
   \item Mapping Agda types to target language, including dependent types
   \item Computing a single conditional out of pattern-matching function clauses
   \item Controlling reduction/inlining and suppressing traversal into chosen definitons
   \item Monadic workaround on lets
   \item Rewriting
\end{enumerate}
