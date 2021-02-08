\begin{code}[hide]
open import Data.Nat as ℕ
open import Data.String using (String; length)
open import Data.List as 𝕃 hiding (length)
open import Data.Unit
open import Data.Bool as 𝔹 hiding (_<_)
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

\subsection{What does shallow embedding actually mean?}
Now that we know our target language, let us explore what subset of the
host language forms the embedding.  Let us start with the types.  Natural
numbers \AD{ℕ} is the main data type of the target language.  In order to
describe invariants we would also support bounded (by \AD{n}) natural
numbers \AD{Fin n}, equality \AD{\_≡\_} and comparison \AD{\_<\_}.  As the
latter is decidable for natural numbers, we would allow proof-relevant
booleans \AD{Dec (a ≡ b)} and \AD{Dec (a < b)}.  They carry the boolean
value and the proof that the relation holds for the chosen arguments.
We would map true to 1 and false to 0, ignoring the proof.  First order
functions of the above types would be mapped to the target language functions.

While it is temping to say that any Agda term of the above types could
be translated into Kaleidoscope, this is not true.  For example, consider
a function:
\begin{code}
module Problem where
  open import Data.Nat.Show renaming (show to showNat)
  ex : ℕ → ℕ
  ex x = length (showNat x)
\end{code}
where \AF{showNat} is a function that returns a string that represents
the given number.  This suggests that we have to add some restrictions to
our terms.  The question is what is the best way to do this?  More
generally: is there a way to internalise the notion of shallowly embedded
language in the host language, and how difficult would it be to work with?

In a dependently-typed language such restrictions can be achieved by
constructing a universe.  The strength of restrictions presents us an
entire spectrum ranging from weak to strong.  Let us demonstrate a
universe that restricts function types.
\begin{code}
module Univ where
  open Problem
  open import Data.Fin using (Fin; zero; suc)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Nat.DivMod
  data Ty : Set ; ⟦_⟧ : Ty → Set
  data Ty where
    nat   : Ty
    fin   : ⟦ nat ⟧ → Ty
    eq lt : (a b : ⟦ nat ⟧) → Ty

  ⟦ nat ⟧    = ℕ
  ⟦ fin x ⟧  = Fin x
  ⟦ eq a b ⟧ = a ≡ b
  ⟦ lt a b ⟧ = a ℕ.< b

  data n-σ : Set where
    ⟨_⟩   : Ty → n-σ
    _▹_ : (τ : Ty) → (⟦ τ ⟧ → n-σ) → n-σ

  I : n-σ → Set
  I ⟨ τ ⟩   = ⟦ τ ⟧
  I (τ ▹ P) = (t : ⟦ τ ⟧) → I (P t)

  ex₁ : I $ nat ▹ λ m → nat ▹ λ n → lt m n ▹ λ m<n → ⟨ fin n ⟩ ; ex₁ = ⋯
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
  ex₂ : I $ nat ▹ λ n → ⟨ fin $ ex n ⟩ ; ex₂ = ⋯
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

While these are hard and interesting problems in itself, this paper takes a
radically different approach.  Instead of trying to restrict types and terms
prior to extraction, we simply allow our extractor to fail.  Extractors
would have to take care of error reporting, but we would be able to use
any Agda terms as valid extraction candidates.


\subsection{Normalisation}
Unrestricted terms give us another important benefit: we may use any host
language constructs that are not present in the embedding as long as we
eliminate them prior extraction.  For example, the target language may not
have the notion of polymorphic or higher functions, yet we could write
programs such as:
\begin{code}
  ex₄ : (n : ℕ) → n < length "999" → ℕ ; ex₄ = ⋯
  fib : (k m n : ℕ) → ℕ
  fib 0       m n = m
  fib (suc k) m n = let m' , n' = n , m + n in fib k m' n'
\end{code}
While \AF{length} is a function from \AD{String} to \AD{ℕ}, it is applied
to a constant string.  In the second clause of \AF{fib} we create a tuple
and immediately destruct it via pattern matching. Note that \AC{\_,\_}
is a polymorphic dependently-typed function
\begin{code}[inline]
  _,″_ : ∀ {A : Set} → {B : A → Set} → (a : A) → B a → Σ A B ; _,″_ = _,_
\end{code}
Therefore, neither \AF{length} nor \AF{\_,\_} could be literally extracted
into Kaleidoscope.  The same holds for the universe of types, which we
could still use as a convention:
\begin{code}
  saturated-add : I $ nat ▹ λ max → fin max ▹ λ a → fin max ▹ λ b → ⟨ fin max ⟩ ; saturated-add = ⋯
\end{code}
Extractors do not have to know anything about strings, pairs or universes,
given that we simplify the terms.

Such a simplification can be conveniently achieved by a standard procedure
called normalisation~\cite{} which applies reduction rules to terms until
they turns into values or neutral terms.  The normalisation procedure is
exposed as a part of reflection API, and the first step of extraction is
to normalise the term and its type.  As extraction operates at the level
of function definitions, technically we normalise the type and the body
of the given function and each pattern-matching clause of its definition.
The latter has to do with propagating rewrite rules which we describe in
Section~\ref{sec:rewriting}, including our modifications to Agda.

\subsection{Controlling Reduction}





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


\subsection{\label{sec:rewriting}Rewriting}
\todo[inline]{Explain how rewriting rules could be used as additional
optimisation steps prior extraction.  Mention that the availability of
telescopes (that Jesper added to Agda) facilitates pushing rewriting
under the function clauses, which used to be a nightmare.}

