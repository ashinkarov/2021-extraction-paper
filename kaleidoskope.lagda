\begin{code}[hide]
open import Data.Nat as ℕ
open import Data.String using (String; length)
open import Data.List as 𝕃 hiding (length)
open import Data.Unit hiding (_≟_)
open import Data.Bool as 𝔹 hiding (_<_; _≟_)
open import Function
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

module Hide where
  open import Reflection
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
module Kaleid where
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
they turn into values or neutral terms.  The normalisation procedure is
exposed as a part of reflection API, and the first step of extraction is
to normalise the term and its type.  As extraction operates at the level
of function definitions, technically we normalise the type and the body
of the given function and each pattern-matching clause of its definition.
The latter has to do with propagating rewrite rules which we describe in
Section~\ref{sec:rewriting}, including our modifications to Agda.

\subsection{Controlling Reduction}

The manual run of normalisation suggests that sometimes it would be
convenient to leave function applications as they are.  For example,
consider the following program:
\begin{code}
  open import Relation.Nullary
  
  ex₅ : ℕ → ℕ
  ex₅ x with x ≟ 42
  ... | yes _ = 10
  ... | no  _ = 20
\end{code}
The definition of \AF{\_≟\_} in the standard library is quite complex:
\begin{code}[hide]
  open import Relation.Binary
  postulate
    ≡ᵇ⇒≡ : ∀ m n → T (m ≡ᵇ n) → m ≡ n
    ≡⇒≡ᵇ : ∀ m n → m ≡ n → T (m ≡ᵇ n)
    T? : ∀ x → Dec (T x)
  _≟″_ : Decidable {A = ℕ} _≡_
\end{code}
\begin{code}
  map′ : ∀ {P Q : Set} → (P → Q) → (Q → P) → Dec P → Dec Q ; map′ = ⋯
  m ≟″ n = map′ (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n) (T? (m ≡ᵇ n))
\end{code}
(we only give a part of it here as the actual details are not that important).
These four functions in the body (\eg{} \AF{map′}, \AF{≡ᵇ⇒≡}, \etc{}) are not
representable in Kaleidoscope, but comparison of natural numbers is.  Generally,
this is a common pattern when we might represent some target language
definitions in Agda in a radically different way than in the target language.
Typically this has to do with proof relevance, like in the above case, but could be also general
invariant that we attach to objects.  In such cases, we might decide
to hard-code the mapping of the Agda function into the target language function.
For example, in this case we map \AF{\_≟\_} into \AC{Eq}.

In order to do this, we have to make sure that normalisation does not expand
certain definitions.  This is what the second argument (base) to our interface
function \AF{kompile} is used for --- to specify the list of functions that
must not reduce during normalisation.

This functionality was not previously available in Agda, so we added two new primitives
to the reflection API --- \AF{dontReduceDefs} and \AF{onlyReduceDefs} with pull
request \url{https://github.com/agda/agda/pull/4978}.  The functions have the following
types:
\begin{code}
module Funs where
  open import Reflection using (Name; TC)
  onlyReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A ; onlyReduceDefs = ⋯
  dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A ; dontReduceDefs = ⋯
\end{code}
and they give us an environment in which any call to \AF{reduce} or \AD{normalise}
would respect the list of function names given in the first argument.  In case of
\AF{onlyReduceDefs} function application would reduce only if the function is
found in the list.  In case of \AF{dontReduceDefs}, function application would
reduce only if the function is not on the list.  When we normalise the code prior
extraction we call \AF{dontReduceDefs} \AB{base} \AF{\$} \AF{normalise} \AB{t},
where \AB{t} is either the type or the term.

% \todo[inline]{Here we explain what is the meaning of the arguments
% to kompile, and that we had to extend Agda in order to make this happen}

\subsection{Mapping Agda Types}

The next step after normalisation is to translate the type signature of Agda
function into the target language.  In case of Kaleidoscope, we do not have
actual type annotations in the language, but we still need to verify whether
the argument (and return) types are from the right universe.  Including the
check that the function is first-order.

We achieve this using the \AF{kompile-ty} function that has the following
structure:
\begin{code}[hide]
module KompTy where
  open import Reflection hiding (TC; return; _>>=_; _>>_)
  open import Reflection.Term
  open import Data.Fin
  open Kaleid

  SPS : Set → Set ; SPS = ⋯
  sps-kompile-term : Term → SPS $ Err Expr ; sps-kompile-term = ⋯

  record PS : Set where
    field cur : String

  record Assrt : Set
  infixl 4 _<$>_
  _<$>_ : ∀{A B : Set} → (A → B) → SPS A → SPS B ; _<$>_ = ⋯
  get : SPS PS ; get = ⋯
  modify : ∀ {i : ⊤} → (PS → PS) → SPS ⊤ ; modify = ⋯
  ke : ∀ {X} → String → SPS (Err X) ; ke = ⋯
  return : ∀ {X} → X → SPS X ; return = ⋯
  _>>=_ : ∀ {X Y} → SPS X → (X → SPS Y) → SPS Y ; _>>=_ = ⋯
  _>>_ : ∀ {X Y} → SPS X → SPS Y → SPS Y ; x >> y = x >>= const y
\end{code}
\begin{code}
  record Assrt where
    constructor mk
    field v : Id ; a : Expr

  _p+=a_ : PS → Assrt → PS ; _p+=a_ = ⋯

  kompile-ty : Type → (pi-ok : Bool) → SPS (Err ⊤)
  kompile-ty (def (quote ℕ) args) _ = return $ ok tt
  kompile-ty (def (quote Fin) (arg _ x ∷ [])) _ = do
    ok p ← sps-kompile-term x where error x → ke x
    v ← PS.cur <$> get
    modify $ _p+=a (mk v (BinOp Lt (Var v) p))
    return $ ok tt
  kompile-ty _ _ = ⋯
\end{code}
It operates within the state monad \AD{SPS} where the state is given
by the type \AD{PS} (pi-type state).  As we traverse the type signature
of a function (the pi type) we collect some information.  For non-dependent
types such as \AD{ℕ}, we simply verify whether the type is supported.
In the above example the first clause of the pattern-matching function
says that \AD{ℕ} is good, and we add such patterns for all the other
non-dependent types.  For dependent types we have to do a bit more work.

One of the important features of extraction is the ability to propagate
invariants from Agda down to the target language.  Recall that our original
goal was to ensure that the function behaves according to the specification.
This is ensured by the fact that our function typechecks in Agda.  Each
dependent type in the function signature can be thought of as a (n-fold)
relation that encodes some facts about its arguments.  This knowledge
can be very useful to the target language.  For example this can be
used in optimisations to generate a better performing code.  Therefore,
we turn such relations into assertions in the target language.

Apart from using those in optimisations, these assertions may be useful
in case of partial program extraction.  For example, assume that function
\begin{code}[inline]
  f : (x : ℕ) → x > 0 → ℕ
\end{code}
\begin{code}[hide]
  f = ⋯
\end{code}
takes a non-zero argument.  This property would be respected in any
uses of \AF{f} within Agda.  However, in the extracted code, the relation
between the first and the second argument will be lost.  Therefore, one
might call extracted \AF{f} with 0 as a first argument.  Assertion would
help to maintain the right interface, turning a static check into a
dynamic one.

When generating assertions from the relation we typically have the following
two options: we can find an encoding for the witness and a way to verify
that arguments are related by the witness.  The other common case is that
our predicate is decidable, and within the function we do not use its
structure.  In this case, the encoding of the predicate is the unit type,
and we can use the decision procedure in the assertion.

In case of \AF{Fin} we are using the first approach.  Recall that \AF{Fin}
is a predicate on \AF{ℕ} and the structure of its witness is given by two
constructors: \AC{zero} and \AC{suc}.  Therefore, we are encoding the witness
using the natural number, and the procedure on verifying that the predicate
holds is comparison that this number is less than the argument to \AF{Fin}.
This is exactly what \AF{kompile-ty} does in \AF{Fin} case.  We extract the
argument \AB{x} (obtaining a Kaleidoscope expression), ensuring that it
succeeds.  Then we get the name of the
function argument referring to \AR{PS.cur} field of our state.  Finally,
we modify the state by adding a constraint on the corresponding function
argument.

As \AD{\_≡\_} and \AD{\_<\_} are both decidable for natural numbers,
we always witnesses of these types with the unit value (natural number 1).
In the assertion we use the decision procedure, that returns a \AD{Dec} type.
Which we interpret as a boolean value: 1 for \AC{yes} and 0 for \AC{no}.
Pattern matching on the value of \AD{\_≡\_} is straight-forward as there
is only one constructor.  On the other hand, constructors of the \AD{\_<\_}
type encodes essentially the difference between the arguments, which we
have chosen to ignore in the encoding.  Therefore we do not support pattern
matching on the values of the \AD{\_<\_}, as otherwise we were to lose
information, e.g. consider the following function:
\begin{code}
  ex₆ : ∀ {a b} → a ℕ.< b → ℕ
  ex₆ (s≤s z≤n) = 1
  ex₆ (s≤s (s≤s a<b)) = 1 ℕ.+ ex₆ (s≤s a<b)
\end{code}
Therefore we are only allowed to pass the inequality around, but not
``look inside''.  This choice could be surely revised, however as we
will see later, we mostly use inequalities as a static assertion rather
than a runtime value.

Finally, the return type of the function also generates an assertion
using the same rules and attaches it prior function return.  For example,
the following function:
\begin{code}[hide]
module ExFin where
  open import Data.Fin using (Fin; fromℕ<)
  open import Data.Nat.Properties
\end{code}
\begin{code}
  ex₇ : (n : ℕ) → Fin (1 + n * n)
  ex₇ n = fromℕ< $ n<1+n (n * n)
\end{code}
Extracts into the following Kaleidoscope code:
\begin{verbatim}
def ex7 (x_1):
  let n = x_1
  let __ret = (n) * (n)
  let __ret_assrt = assert ((__ret) < ((1) + ((x_1) * (x_1))))
  __ret
\end{verbatim}

Let us walk through this example.  First, notice that we have generated
assertion for the return value, which is coming from the type signature
of \AF{ex₇}.  How did we manage to turn the body of the function into
multiplication?  Let us recall the types of both standard library functions:
\begin{code}
module Signatures where
  open import Data.Fin using (Fin)
  fromℕ< : ∀ {m n} → m ℕ.< n → Fin n ; fromℕ< = ⋯
  n<1+n : ∀ n → n ℕ.< 1 + n ; n<1+n = ⋯
\end{code}
The \AF{fromℕ<} function turns a proof of \AB{m} \AF{<} \AB{n} into
\AF{Fin} \AB{n} type.  As we are encoding \AF{Fin}s as natural numbers,
we could take a shortcut in the extractor and specialcase \AF{fromℕ<}
just to return the left hand side of the \AF{\_<\_} argument.  Luckily,
with dependent types we are always going to have access to the arguments
of the relation.  In this particular case, the first hidden argument \AB{m}
is the value that we are after.  Therefore, with the chosen encoding,
extraction of the \AF{fromℕ<} returns the first argument and ignores all
the other arguments.  Note that by doing so we are not loosing any information,
as the proof here is merely asserting that \AB{m} fits the specification.
This happy coincidence allowing us to ignore runtime-irrelevant relations
is very insightful, as it helps to avoid a lot of unnecessary work and
keep the extracted code more efficient.




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

