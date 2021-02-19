\begin{code}[hide]
{-# OPTIONS --rewriting #-}

open import Data.Nat as ℕ
open import Data.String using (String) --; length)
open import Data.List as 𝕃 using (List; []; _∷_; [_])
open import Data.Unit hiding (_≟_)
open import Data.Bool as 𝔹 hiding (_<_; _≟_)
open import Function
module _ where
postulate
  ⋯ : ∀ {a}{A : Set a} → A
\end{code}
\section{Extraction Framework}

On a high level, extraction translates reflected
Agda terms into corresponding terms in the target language,
but the devil is hidden in the details.  Design of embedding
is a difficult balance between mimicing the structure of the
target language, ease of proving facts about embedded programs,
and normalisation friendliness --- can we make the host language
to optimise our code prior extraction?  Sometimes we find that the
existing reflection interface of Agda is missing desirable
functionality.  In those case we extend Agda to accommodate our
needs. Finally, we have reflection challenges that have to do with the actual
translation: matching embedded encoding against the actual language or
dealing with type difference in type systems.

In this section we start with a general overview of the framework
focusing on language-independent parts of extraction.  In order
to keep examples simple, we use a minimalist language called Kaleidoscope~\cite{}.

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
\end{code}
\begin{code}[hide]
module Hide where
  open import Reflection
\end{code}
\begin{code}
  module Extract (kompile-fun : Type → Term → Name → SKS Prog) where
    macro
      kompile : Name → Names → Names → (Term → TC ⊤)
      kompile n base skip hole = ⋯
\end{code}
The \AF{kompile-fun} parameter is a language-specific function that
is doing all the major work.  It extracts a reflected function with
given type, body and name and returns its textual representation,
in case extraction succeeded.  It operates in the \AF{SKS} state
monad.  The entry function \AF{kompile} is language-agnostic, as
it delegates all the work to \AF{kompile-fun}.  Given the
function named \AB{n} it obtains normalised type and body, runs
the extraction and recurses into functions that are found on the
call graph of \AB{n}.  It is assumed that \AF{kompile-fun} adds
a dependency into the state and \AF{kompile} keeps track of the
visited function to avoid repeated extraction.  Finally, all the
extracted functions are concatenated together given that all the
extractions succeeded.

The second and the third parameters of \AF{kompile} are lists of
names that control function inlining in the extracted terms and
traversal into the definitions found in the call graph.  We explain
these arguments after introducing our first embedded language.

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
  open import Data.String using (length)
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
  open import Data.String using (length)
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

\subsection{\label{sec:maptypes}Mapping Agda Types}

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
Many target languages do not support function
definitions in a pattern-matching style, whereas in Agda it is very
common.  Most of data structures are inductive, and pattern-matching
is a very natural way of traversing them. It also helps the termination
checker to identify whether recursive calls are structurally
decreasing~\cite{}.  As a result, turning a list of pattern-matching
clauses into a single conditional is a common task in extractors.


This problem splits naturally into two parts: compute a condition from
the given clause, and join all such conditions in a single conditional.
Let us start with the second part.  We define the \AF{kompile-cls} function
with the following type:
% TODO we also call kompile-term in this function!
\begin{code}[hide]
module Cls where
  open import Reflection
  Strings = List String
  open Kaleid
\end{code}
\begin{code}
  kompile-cls : (cls : Clauses) → (vars : Strings) → (ret : String) → SKS (Err Expr)
  kompile-cls = ⋯
\end{code}
where the first argument is the list of clauses, the second argument is the
list of variable names, and the last argument is the name of the variable
we assign the return value to.  The function operates in the \AD{SKS}
monad as we are extracting the body of each clause, so we need to keep
the extraction state.  The function traverses clauses in order they appear
in the definition and combines them in a nested if-then-else chain as
follows:
\begin{code}
  ack : ℕ → ℕ → ℕ                                  -- def ack (x1, x2):
  ack 0       n       = 1 + n                      --   if x1 == 0: 1 + x2
  ack (suc m) 0       = ack m 1                    --   else if x1 > 0 && x2 == 0: ack (x1-1) 1
  ack (suc m) (suc n) = ack m (ack (suc m) n)      --   else: ack (x1-1) (ack x1 (x2-1))
\end{code}
While the definition of the function is straight-forward, there are two important
aspects to notice.  Firstly, notice that in the second predicate we have explicit
\AB{x1} \AF{>} \AS{0} check, that could have been omitted.  However, if the first
and the second clauses were swapped, such a comparison with zero must be
present.  Our current implementation takes minimalist approach and generates
predicates in the simplest possible form, without optimising extra comparisons
as above.  Many target languages may perform such an optimisation themselves.
Also, and more importantly, one of the internal representations of Agda has the
form, where all the patterns are folded.  Currently it is not exposed via the
reflection API, but as it works universally for any term, it might be simpler
to extend the API rather than reimplementing pattern folding.

Secondly, absurd patterns have to be treated with care.  For example, consider
the following function:
\begin{code}
module Ex9 where
  open import Relation.Binary.PropositionalEquality
  open import Data.Fin using (Fin; zero; suc)

  ex₉ : (x : ℕ) → x ≡ 0 → (y : ℕ) → x ≡ y → ℕ   -- def ex9(x_1, x_2, x_3, x_4):
  ex₉ x ()  (suc y) refl                        --   if (x_3) > (0): assert (0)
  ex₉ x x=0 y       x=y  = y                    --   else: x_3
\end{code}
We have several design options on how to treat absurd cases.  If we assume that
each dependent type such as \AB{x} \AF{≡} \AS{0} generates a runtime assertion
as we described in Section~\ref{sec:maptypes}, absurd cases may be simply
eliminated.  In the presence of assertions the combination of such argument
values is impossible, as guaranteed by Agda's coverage checker~\cite{}.
However, absurd cases carry information that we might want to pass
to the target language.  Consider the following example:
\begin{code}
  P : _ → _
  P x = x * x + 2 ∸ 3 * x
  ex₁₀ : ∀ x → 0 < P x → ℕ
  ex₁₀ 1 ()
  ex₁₀ 2 ()
  ex₁₀ x pf = ⋯
\end{code}
We can generate an assertion that \AB{x} is greater than \AF{P} \AB{x}, and
after eliminating first two cases, the body of the function would reduce to a single
statement over variables \AB{x} and \AB{pf}.  However, deducing that
\AB{x} not equals to \AS{1} and \AS{2} is not straight forward (undecidable in
general).  By preserving this information, the target language might make a
good use of it, \eg{} for better optimisations.

To preserve the absurd patters target languages must provide the way to terminate
computation on the given conditional.  Currently, we are using the
\AF{assert} (\AS{0}) construction to abort the computation.  Note that such an
abort construction is needed irrespectively of whether we preserve absurd patterns
or not, as we need a constructor that expresses the case when the function has
a single absurd clause \eg{}:
\begin{code}
  ex₁₁ : ∀ n → n < 0 → ℕ      -- def ex11 (x1, x2):
  ex₁₁ n ()                   --   assert (0)
\end{code}
The problem here is that per semantics of our target language we need to return
some value.  The function from above does not provide any value, as it has shown
that no arguments can possibly satisfy the type signature, and ex falso quodlibet
(or the principle of explosion) states that anything is deducible from falsehood.
For example, a natural number, but it does not tell us which one!  While inventing
a natural number is easy, generally, inventing a value of the given type is
undecidable.

The actual translation between pattern lists and predicates is implemented in
with the following function:

\begin{code}[hide]
module ClPats where
  open import Reflection hiding (_>>=_; return; _>>_)
  open import Reflection.Term using (Telescope; con)
  open import Data.Fin as F using (Fin; zero; suc)
  open import Data.Product
  open import Data.List using (_++_)
  open Kaleid
  record PatSt : Set where
    field conds : List Expr

  infixl 10 _+=c_
  _+=c_ : PatSt → Expr → PatSt
  p +=c c = record p { conds = PatSt.conds p ++ [ c ] }
  pst-fresh : PatSt → String → Err $ String × PatSt
  pst-fresh = ⋯
  _>>=_ : ∀ {X Y : Set} → Err X → (X → Err Y) → Err Y
  _>>=_ = ⋯
  return : ∀ {X : Set} → X → Err X
  return = ⋯
\end{code}
\begin{code}
  {-# TERMINATING #-}
  kompile-clpats : Telescope → (pats : List $ Arg Pattern) → (exprs : List Expr) → PatSt → Err PatSt
  kompile-clpats tel (arg i (con (quote F.zero) ps) ∷ l) (e ∷ ctx) pst =
    kompile-clpats tel l ctx $ pst +=c (BinOp Eq e (Nat 0))
  kompile-clpats tel (arg i (con (quote F.suc) ps@(_ ∷ _ ∷ [])) ∷ l) (e ∷ ctx) pst = do
    (ub , pst) ← pst-fresh pst "ub_"
    kompile-clpats tel (ps ++ l) (Var ub ∷ (BinOp Minus e (Nat 1)) ∷ ctx)
                   $ pst +=c (BinOp Gt e (Nat 0))
  kompile-clpats tel ps ctx pst = ⋯
\end{code}
We are considering only two clauses of the functions that matches \AF{Fin}
constructors \AC{zero} and \AC{suc}.  The function take four arguments:
the telescope mapping variables used in the pattern list to their names
and types (see Section~\ref{sec:rewriting} for details on telescopes);
the list of patterns; the list of expressions that are being matched
by the patterns; and the state record \AD{PatSt}.  The state record
contains things like the counter for fresh variables, the list of conditions
accumulated so far, local assignments, and so on.  At the beginning of each
clause, the list of expressions is initialised with function arguments.
For each constructor-pattern (like \AF{zero} or \AF{suc}) we have to
produce a condition that holds only when the encoded value in the
target language represents the value that was built using the given
constructor.  For example, as we represent \AF{Fin} with natural numbers,
the \AC{zero} constructor yields the \AB{e} \AF{==} \AS{0} condition.
Correspondingly, the \AC{suc} \AB{ub} \AB{x} yields two conditions:
\AB{e} \AF{>} \AS{0} and (\AB{e}\AF{-}\AS{1}) \AF{>} \AS{0}.
In the above code snippet we make a small optimisation and skip
generation of the last condition for the upper bound of the \AC{suc}
constructor. This is valid under assumption that we have asserted
that the argument is less than the argument of \AF{Fin} type.
The \AF{pst-fresh} function generates a variable with the unique
(within the clause) name, and \AF{\_+=c\_} adds new condition into
the state.

Notice that we marked this function as terminating.  We had to do
so as termination checker cannot prove that the call in the second
clause is valid.
Specifically, the \AB{ps} \AF{++} \AB{l} argument is problematic.
Indeed, if we keep increasing the list of the patterns recursively,
then the function might not terminate.  While this particular function
is actually safe, we can prove this formally, demonstrating the power
of Agda when building extractors.

The function is terminating because the \AF{Pattern} type is well-founded,
and all the objects of that type are finite.  Therefore, if we find a
metric that would witness this and decrease at each \AF{kompile-clpats} call,
our recursion would become structural.  Here is one way to do this:
\begin{code}
  sz : List $ Arg Pattern → ℕ
  sz [] = 0
  sz (arg i (con c ps) ∷ l) = 1 + sz ps + sz l
  sz (arg i _ ∷ l) = 1 + sz l

  ps++l<m : ∀ {m} ps l → suc (sz ps + sz l) ℕ.< suc m → sz (ps ++ l) ℕ.< m
  sz[l]<m : ∀ {m} ps l → suc (sz ps + sz l) ℕ.< suc m → sz l ℕ.< m

  kompile-clpats′ : ∀ {m} → Telescope → (pats : List $ Arg Pattern) → .(sz<m : sz pats ℕ.< m)
                 → (exprs : List Expr) → PatSt → Err PatSt

  kompile-clpats′ {suc m} tel (arg i (con (quote F.zero) ps) ∷ l) sz<m (v ∷ ctx) pst =
    kompile-clpats′ tel l (sz[l]<m ps l sz<m) ctx $ pst +=c BinOp Eq v (Nat 0)
  kompile-clpats′ {suc m} tel (arg i (con (quote F.suc) ps@(_ ∷ _ ∷ [])) ∷ l) sz<m (v ∷ ctx) pst = do
    (ub , pst) ← pst-fresh pst "ub_"
    kompile-clpats′ tel (ps ++ l) (ps++l<m ps l sz<m) (Var ub ∷ (BinOp Minus v (Nat 1)) ∷ ctx)
                    $ pst +=c BinOp Gt v (Nat 0)
  kompile-clpats′ tel l sz<m ctx ps = ⋯
\end{code}
We define the \AF{sz} function that computes how many non-constructors are
in the given list of patterns: if the pattern is a constructor, its size
is 1 plus the size of its arguments; otherwise the size is one.  After that
we prove two lemmas: \AF{ps++l<m} for the case when the recursive call gets
the concatenation of the arguments and the remainder of the pattern list; and
\AF{sz[l]<m} when the recursive call happens only on the remainder of the
pattern list.  Then we extend \AF{kompile-clpats} with two extra arguments:
\AB{m} which is the bound of the size of pattern list; and \AB{sz<m} which
is the proof that the size of the pattern list is less than the chosen bound.
Note that we can mark the latter as irrelevant argument (by putting dot in the
type) which means that it would be erased at runtime and that it is used as a
static assertion rather than data.  Now we have to modify each recursive call
by providing suitable upper bounds and proofs.  The latter is mainly achieved
by using the \AF{ps++l<m} and \AF{sz[l]<m} lemmas.  Finally we can wrap this
function so that the original type is matched as follows:
\begin{code}[hide]
  ps++l<m {m} ps l sz<m = ⋯
  sz[l]<m {m} ps l sz<m = ⋯
module Wrapper where
  open import Reflection hiding (_>>=_; return; _>>_)
  open import Reflection.Term using (Telescope; con)
  open import Data.Nat.Properties as ℕ
  open Kaleid
  record PatSt : Set where
  sz : List $ Arg Pattern → ℕ ; sz = ⋯
  kompile-clpats′ : ∀ {m} → Telescope → (pats : List $ Arg Pattern) → .(sz<m : sz pats ℕ.< m)
                 → (exprs : List Expr) → PatSt → Err PatSt
  kompile-clpats′ = ⋯
  kompile-clpats : Telescope → (pats : List $ Arg Pattern) → (exprs : List Expr) → PatSt → Err PatSt
\end{code}
\begin{code}
  kompile-clpats tel pats ctx pst = kompile-clpats′ {m = suc (sz pats)} tel pats ℕ.≤-refl ctx pst
\end{code}
For a given pattern list we chose an upper bound that is one greater than the
actual size of the pattern list.  The proof that the upper bound holds is
straight-forward and is witnessed by a standard library function \AF{≤-refl}.

\todo[inline]{Do we want to say anything about the overall idea of folding
  pattern-matching cases into a conditional, and reverse mappings of the
  encoding back into constructors that we are dealing with?}

% \todo[inline]{Explain how do we turn a pattern-matching function definition
% into a single definition with a conditional inside.  We have to make sure
% that we explained the telescopes (or explain them here), and we can
% reiterate absurd patterns here.}

\subsection{Translating terms}
The actual translation of Agda terms into Kaleidoscope terms a very
mechanical process.  However, as the translation may fail, the use of
monads and \AK{do}-notation for managing errors helps us to keep the
code clean:
\begin{code}[hide]
module KompTerm where
  open import Reflection hiding (_>>=_; return; _>>_)
  open import Reflection.Term
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong)
  open import Relation.Nullary
  open Kaleid
  open import Data.Fin as F using ()
  open import Data.List using (length; _++_)
  record KS : Set where
    field funs : List Name

  --SKSE = SKS ∘ Err
  _>>=_ : ∀ {X Y : Set} → SKS X → (X → SKS Y) → SKS Y
  _>>=_ = ⋯
  return : ∀ {X : Set} → X → SKS X
  return = ⋯
  _>>_ : ∀ {A B : Set} → SKS A → SKS B → SKS B ; _>>_ = ⋯
  infixl 4 _<$>_ _⊛_
  _<$>_ : ∀{A B : Set} → (A → B) → Err A → Err B ; _<$>_ = ⋯
  _⊛_ : ∀ {A B : Set} → Err (A → B) → Err A → Err B ; _⊛_ = ⋯
  modify : ∀ {i : ⊤} → (KS → KS) → SKS ⊤ ; modify = ⋯
  kt : ∀ {X} → String → SKS (Err X) ; kt = ⋯
  kompile-arglist : List $ Arg Term → List ℕ → Telescope → SKS $ Err (List Expr)
  kompile-arglist = ⋯
  mk-iota-mask : ℕ → List ℕ ; mk-iota-mask = ⋯
  normalise-name : String → String ; normalise-name = ⋯
\end{code}
\begin{code}
  kompile-term : Term → Telescope → SKS $ Err Expr
  kompile-term (def (quote _+_) args@(arg _ a ∷ arg _ b ∷ [])) vars = do
    a ← kompile-term a vars
    b ← kompile-term b vars
    return $ BinOp <$> ok Plus ⊛ a ⊛ b

  kompile-term (def (quote F.fromℕ<) args) vars = do
    ok (x ∷ []) ← kompile-arglist args (0 ∷ []) vars
                  where _ → kt "wrong assumptions about arguments of fromℕ<"
    return $ ok x

  kompile-term (def n args@(_ ∷ _)) vars = do
    modify λ k → record k { funs = KS.funs k ++ [ n ] }
    args ← kompile-arglist args (mk-iota-mask $ length args) vars
    return $ Call <$> ok (normalise-name $ showName n) ⊛ args

  kompile-term t vars = ⋯
\end{code}
We demonstrate three representative clauses of the term extracting function.
First, we turn \AD{SKS} and \AD{Err} into monads by defining their bind and
return actions.  As each moand is an applicative functor, we get \AF{\_<\$>\_}
and \AF{\_⊛\_} operations for free.  The instance resolution mechanism~\cite{}
makes it possible to overload moanadic/functorial operations without explicitly
mentioning in which monad we are operating.  Therefore, a typical translation,
as in case of natural number addition, extracts the arguments and puts them
together in a corresponding expression of the target language.

For some constructions it is convenient to handle arguments without
explicitly pattern-matching them, \eg{} some constructor with a long argument
list where we are interested only in a particular subset.  For such reasons we
introduce the two-argument \AF{kompile-arglist} function where the first argument
is the list of \AC{Arg}uments; and the second argument is the mask that specifies
indices into the first argument.  The function extracts each argument from the
list as specified by the mask.  In case of \AF{fromℕ<} we use this function to
extract the first argument from the \AB{args} list.

The last clause deals with general function calls that do not require special
treatment.  We ensure that argument list is non-empty: the \AF{\_ ∷ \_} pattern.
Then we add the name of the function into the \AR{funs} field of the state record.
This list would be used by \AF{kompile} to traverse the call graph of the function
and extract all the necessary dependencies.  Then we extract the arguments, using
the helper function \AF{mk-iota-mask} that generates indices from \AS{0} to the
length of the argument list.  Finally we create an \AD{Expr}ession for a function
call.  We use the extracted arguments and we normalise the name to get rid of
unicode symbols.



\subsection{\label{sec:rewriting}Rewriting}
% \todo[inline]{Explain how rewriting rules could be used as additional
% optimisation steps prior extraction.  Mention that the availability of
% telescopes (that Jesper added to Agda) facilitates pushing rewriting
% under the function clauses, which used to be a nightmare.}

One of the unfortunate features of intuitionistic dependently-typed systems is the
distinction between definitional and propositional equalities.  A famous
example that demonstrates the problem is addition of natural numbers defined
inductively on the first argument:
\begin{code}
  plus : ℕ → ℕ → ℕ
  plus 0       b = b
  plus (suc a) b = suc (plus a b)
\end{code}
With this definition \AS{0}\AF{+}\AB{x} is definitionally equal to \AS{x},
but \AB{x}\AF{+}\AS{0} is not:
\begin{code}
  0-plus : ∀ x → 0 + x ≡ x          -- plus-0 : ∀ x → x + 0 ≡ x
  0-plus x = refl                   -- does NOT hold definitionally
\end{code}
The problem is that there is no explicit reduction rule that can be applied
to \AB{x}\AF{+}\AS{0} --- it is a neutral term.  As computation is an
essential part of dependent type checking, some perfectly reasonable
programs may be rejected.  For example, a vector of length \AB{n}
concatenated with an empty vector is not of the type vector
of length \AB{n}:
\begin{code}
  -- rejected : ∀ {n} → (x : Vec ℕ n) → Vec ℕ n
  -- rejected x = x ++ []
\end{code}
The reason is that \AB{x} \AF{++} \AC{[]} is of type \AD{Vec} \AD{ℕ}
(\AB{n} \AF{+} \AS{1}).  This problem might seem too theoretical, unfortunately
such cases are very often seen in practice, as a result of a long
$\beta$-reduction sequence.  In the context of extraction, such terms
make the extracted code less efficient.

Fortunately, Agda makes it possible to work around this
problem with rewrite rules~\cite{}. Any binary
relation can be registered as a source of rewrites.  Propositional equality
\AF{\_≡\_} is typically a good choice.  Functions that return such a relation
can be registered as rewrite rules.  For example:
\begin{code}
  plus-0 : ∀ x → plus x 0 ≡ x
  plus-0 zero    = refl
  plus-0 (suc x) = cong suc $ plus-0 x

  {-# BUILTIN REWRITE _≡_ #-}
  {-# REWRITE plus-0 #-}
  plus-0-test : ∀ x → plus x 0 ≡ x
  plus-0-test x = refl
\end{code}
We have defined a propositional equality \AF{plus-0}, and registered it as a
rewrite rule.  By doing so, \AF{plus-0} became a defintional equality, and
we go the ``missing'' reduction rule.  We can now show that \AB{x}\AF{+}\AS{0}
is definitionally equal to \AB{x}.

In the context of extraction rewrite rules can be seen as a mechanism to define
custom optimisations.  As rewrite rules are applied prior to extraction, extractors
are operating on rewritten terms.  The benefit of this approach is that rewrite
rules that we register are \emph{formally verified} (when using \AF{\_≡\_} as a
rewrite relation).  For example, we could define the following rule that we were
taught at school:
\begin{code}
  open import Data.Nat.Solver ; open +-*-Solver
  sum-square : ∀ x y → x * x + 2 * x * y + y * y ≡ (x + y) * (x + y)
  sum-square = solve 2 (λ x y → x :* x :+ con 2 :* x :* y :+ y :* y
                        :=  (x :+ y) :* (x :+ y)) refl
  {-# REWRITE sum-square #-}
\end{code}
so that we can perform two arithmetic operations instead of six when computing
the polynomial.  It might seem that such an example on natural numbers are not
very practical, but it gets more prominent for more complex data structures.
For example, the famous list equality on distributivity of \AF{map}s over
\AF{\_∘\_}:
\begin{code}
  open import Data.List using (map)
  map-∘ : ∀ {X Y Z : Set}{g : X → Y}{f : Y → Z} → ∀ xs → (map f ∘ map g) xs ≡ map (f ∘ g) xs
  map-∘ [] = refl
  map-∘ (x ∷ xs) = cong (_ ∷_) (map-∘ xs)
\end{code}
tells us that we can save one list traversal.  Instead of traversing all the elements
of \AB{xs} and then all the elements of the \AF{map} \AB{g} \AB{xs}, we can compute
the same result in a single traversal.  Generally, we often know a number of properties
about the data structures we are working with.  In a dependently-typed systems we can
make those properties explicit and formally verify them, but in rewriting-capable
systems we can selectively turn properties into optimisations.

One danger with custom rewrite rules is the ability to create a sequence of
non-terminating rewrites.  For example if one registers commutativity of addition
as a rewrite rule, then any expression of the form \AB{a} \AF{+} \AB{b} would
cause an infinite sequence of rewrites.  One of the measures to prevent this
is a recently introduced rewrite rule confluence checker~\cite{}.  It can be
turned on and it would report when the registered set of rewrite rules is not
confluent.  While confluence does not guarantee termination, it becomes very
practical in combination with restrictions on the left-hand-side of each rule
that must be a constructor or a function applied to neutral terms.  In the
adding zero on the right example, the confluence checker will complain that
\AF{plus} (\AC{suc} \AB{x}) \AS{zero} can be rewritten into two different
ways: (\AC{suc} \AB{x}) and \AC{suc} (\AF{plus} \AB{x} \AS{zero}).  So if
we add a new rewrite rule for \AF{plus} (\AC{suc} \AB{x}) \AS{zero} $\mapsto$
\AC{suc} \AB{x}, our rewrite becomes confluent.  In case of commutativity,
the confluence checker would complain that \AS{0} \AF{+} \AB{m} reduces
to \AB{m} but rewrites to \AS{m} \AF{+} \AC{zero}, so fixing this would
require a rule \AB{m} $\mapsto$ \AB{m} \AF{+} \AC{zero}, but such a rewrite
is not allowed, as the left hand side is not a constructor/function application.
For more details on rewrite rules and their confluence checking refer to~\cite{}.


\todo[inline]{Now we want to propagate rewriting rules under the lambdas.}

\subsubsection{Telescopes}
Added telescopes in this pull request \url{https://github.com/agda/agda/pull/4722}.
\todo[inline]{Explain what they are.}

\todo[inline]{Explain our normalisation procedure modulo reconstruction.}




\subsection{Monadic Workaround for Lets}
One of the unfortunate design choices of the Agda internal language is
the lack of let constructs.  All the lets we use in the code are eliminated
by substituting the bound expression in the body of the let.  While
this is sound semantically, it may lead to unnecessary code duplication:
\begin{code}
  ex₈ : ℕ → ℕ
  ex₈ x = let a = x * x + 3 * x + 5 in a + a
  --    ⇒ (x * x + 3 * x + 5) + (x * x + 3 * x + 5)
\end{code}
While this is too large of a change in Agda, we can use the following
elegant workaround.  Agda's do-notation is a syntactic sugar that
expands if we define two operations \AF{\_>>=\_} and \AF{return}
for some monad~\cite{}.  This includes the identity monad as well:
\begin{code}
module Monadic where
  _>>=_ : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂} → A → (A → B) → B
  a >>= f = f a
  return : ∀ {ℓ}{A : Set ℓ} → A → A
  return a = a
\end{code}
With such definitions at hand we can use do-notation instead of lets,
given that we add support for the above bind and return in our extractor.
\begin{code}
  ex₈′ : ℕ → ℕ
  ex₈′ x = do
    a ← x * x + 3 * x + 5
    return $ a + a
\end{code}


%\todo[inline]{Explain that we can workaround the lack of lets in the internal
%syntax by introducinog a fake monad; give an example.}


\subsection{Example}
% \todo[inline]{This is an example explaining how to define a function
%   that is not structurally recursive.  Is it worth while keeping?
%   We use the same technique in the kompile-clpats.  Maybe make it
%   into a final example and demonstrate that we can extract it.}

Let us consider the actual output that our extractor generates for a
reasonably complex function.  We use binary logarithm as an example.
We take the simplest specification, and we assume that logarithm of zero
is zero.  One difficulty with this function is that it is not structurally
recursive and Agda does not recognise that it terminates.  Therefore
we need to take some steps to prove this.  We are going to use a standard
technique of recursing on a well-founded \AF{\_<\_} predicate (comparison
of natural numbers.  Here is Agda definition and the extracted code
(slightly reformatted) arranged line-by-line:

\begin{code}[hide]
  open import Data.Nat.DivMod
  open import Data.Nat.Properties
\end{code}
\begin{code}
  -- _/_ : (x y : ℕ) {≢0 : False (y ≟ 0)} → ℕ

  x<m⇒sx/2<m : ∀ x m → x < m → suc x / 2 < m
  x<m⇒sx/2<m x m x<m = ≤-trans (m/n<m (suc x) 2 (s≤s z≤n) ≤-refl) x<m
  -- Extracted with command : kompile log₂ (quote ≤-refl ∷ quote _<_ ∷ []) []
  log₂′ : ∀ {m} → (n : ℕ) → (n < m) → ℕ  -- def log2' (x_1, x_2, x_3):
                                         --   let x_3_assrt = assert (x_2 < x_1)
  log₂′ {m}     0         _   = 0        --   let __ret = if (x_2 == 0):
                                         --     let m = x_1 ; x = x_3
                                         --     0
  log₂′ {m}     1         _   = 0        --   else if (x_2 > 0) && (x_2 - 1 == 0):
                                         --     let m = x_1 ; x = x_3 
                                         --     0
  log₂′ {suc m} n@(suc x) n<m =          --   else if (x_1 > 0) && (x_2 > 0):
    1 + log₂′ {m = m} (n / 2)            --     let m = x_1 - 1 ; x = x_2 - 1 ; n<m = x_3
        (x<m⇒sx/2<m x m $ ≤-pred n<m)    --     1 + log2' (m, 0 + (x + 1 - 0) / (1 + 1), 1)
                                         --   else:
                                         --     assert (0)

  log₂ : ℕ → ℕ                           -- def log2 (x_1):
  log₂ x = log₂′ x ≤-refl                --   let x = x_1 ; __ret = log2' (1 + x, x, 1)
                                         --   __ret
\end{code}
We define two functions: \AF{log₂} which is a wrapper and \AF{log₂′} where the
actual work happens.  We define two base cases for \AS{0} and \AS{1} and the recursive
case on the argument divided by \AS{2}.  Notice that \AF{\_/\_} function has an implicit
argument that asserts that the divisor is non-zero. Agda is capable to deduce the proof
automatically for constant value such as \AS{2}.  In the extracted code we start with
the assertion that was extracted from the type of \AB{n<m}.  The first case is trivial.
In the second case we see \AB{x\_2} \AF{-} \AS{1} \AF{==} \AS{0},
rather than \AB{x\_2} \AF{==} \AS{1}, which is an artefact of the algorithm
used in \AF{kompile-clpats} and the fact that \AS{1} is represented as
\AC{suc} \AC{zero}.  This is a correct translation, as we ensure that \AB{x\_2}
is greater than zero before subtracting one.  However, this could be further
optimised either by the target language or as a post-extraction step.

In the recursive case, division looks suspiciously complex, and instead of the
proof we have the value \AS{1}.  The reason for the complexity of the division
operation is because \AF{\_/\_} expands to the internal representation given by a
\AF{div-helper} \AB{k} \AB{m} \AB{n} \AB{j} that corresponds to the expression
\AB{k} \AF{+} ((\AB{n}\AF{+}\AB{m}\AF{-}\AB{j}) \AF{/} (\AS{1}\AF{+}\AB{m})).
We could have suppressed the normalisation of \AF{\_/\_}, but this is not
generally desirable, as it prevents evaluation prior to extraction.  For example,
without suppression (\AS{2}\AF{+}\AB{n})\AF{/}\AS{2} normalises to
\AS{1}\AF{+}(\AB{n}\AF{/}\AS{2}), whereas suppressed \AF{\_/\_} would be treated
as an opaque object.

As for the proof, per our assumption, \AF{\_<\_} is used as a static assertion
(we cannot pattern-match on its value).  This means that any function that has
a return type \AB{a} \AF{<} \AB{b} can be replaced with the unit value.  This
is valid, because we are extracting function calls that were verified by the
typechecker.  Therefore, we can completely omit the proof part of \AF{\_<\_},
only acknowledging that the type is inhabited.  This particular case relies
on \AF{≤-trans} (from the inlined proof) and \AF{≤-refl} (from \AF{log₂}
definition) being extracted into unit values.

We have the \AK{else} case that is not specified in the original code on the left.
The reason for this is that our pattern-matching
is not exact.  We are missing the case where \AB{m} is zero and \AB{n} is greater
than \AS{2}.  While the coverage checker is convinced that such case is impossible,
the missing case is automatically inserted into internal representation
as an absurd clause.

Finally, in the \AF{log₂} definition, \AF{≤-refl} is a proof that \AB{x} is less
than \AB{x}\AF{+}\AS{1}.
