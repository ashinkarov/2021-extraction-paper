\begin{code}[hide]
{-# OPTIONS --rewriting #-}

--open import Data.Nat as ℕ hiding (_≟_)
open import Data.String using (String) --; length)
open import Data.List as 𝕃 using (List; []; _∷_; [_])
open import Data.Unit hiding (_≟_)
--open import Data.Bool as 𝔹 hiding (_<_; _≟_; T)
open import Function
module _ where
postulate
  ⋯ : ∀ {a}{A : Set a} → A
\end{code}
\section{\label{sec:basic-extr}Basic Extraction}

% On a high level, extraction translates reflected
% Agda terms into corresponding terms in the target language,
% but the devil is hidden in the details.  Design of embedding
% is a difficult balance between mimicing the structure of the
% target language, ease of proving facts about embedded programs,
% and normalisation friendliness --- can we make the host language
% to optimise our code prior extraction?  Sometimes we find that the
% existing reflection interface of Agda is missing desirable
% functionality.  In those case we extend Agda to accommodate our
% needs. Finally, we have reflection challenges that have to do with the actual
% translation: matching embedded encoding against the actual language or
% dealing with type difference in type systems.

In this section we demonstrate basic mechanisms that are necessary when
implementing reflection-based extractors.  In order to make our examples
concrete, we use a minimalist language called
Kaleidoscope~\cite{kaleidoscope} as our target.  We explain the challenges
and demonstrate Agda code snippets of the actual extractor for Kaleidoscope.

\subsection{Framework Overview}

The extraction process naturally splits into a language-dependent and
a language-independent part. We start by explaining the reusable
language-independent module, which we refer to the as the
``framework''.
%
The entry point of the framework is a parametrised module \AM{Extract} that
contains a single macro called \AF{kompile}:
\begin{code}[hide]
module ExtrMod where
  open import Reflection
  open import Data.Nat as ℕ hiding (_≟_) public
  SKS : Set → Set ; SKS = ⋯
  Prog : Set ; Prog = ⋯
  module Kaleid where
    kompile-fun : Type → Term → Name → SKS Prog
    kompile-fun = ⋯
\end{code}
\begin{code}
  module Extract (kompile-fun : Type → Term → Name → SKS Prog) where
    macro
      kompile : Name → Names → Names → (Term → TC ⊤)
      kompile n base skip hole = --
\end{code}
\begin{code}[hide]
                                quoteTC 42 >>= unify hole
\end{code}
The \AB{kompile-fun} parameter is a language-specific function
specifying how to compile a single Agda function, given by
its type, body and name.
%
It operates within the \AF{SKS} state monad, which it can use to
register other functions that should also be extracted, and returns
either a representation of the extracted function in the target
language in case extraction succeeded, or an error message, as
specified by the \AD{Prog} type.
%
%
\begin{mathpar}
\codeblock{
\begin{code}
data Err {ℓ} (A : Set ℓ) : Set ℓ where
  error : String → Err A
  ok    : A → Err A
\end{code}
}
\and
\codeblock{
\begin{code}[hide]
module ExtrStructMod where
  open import Data.Nat as ℕ hiding (_≟_)
  open ExtrMod using (module Kaleid; module Extract)
\end{code}
\begin{code}
  SKS : Set → Set    -- State Monad (KS)
  TC  : Set → Set    -- TypeChecking Monad
  Prog = Err String  -- String or Error
\end{code}
}
\end{mathpar}
\begin{code}[hide]
  SKS = ⋯
  TC = ⋯
\end{code}

Assuming \AF{kompile-fun} is defined
in the module \AM{Kaleid} here is how to instantiate the framework:
\begin{code}
  open Extract (Kaleid.kompile-fun)
  foo : ℕ → ℕ ; foo = ⋯ ; base-functions = ⋯ ; skip-functions = ⋯
  extracted = kompile foo base-functions skip-functions
\end{code}
The first argument to the \AF{kompile} macro is the name of the main
function that we want to extract, in this case \AF{foo}. The second
and the third parameters of \AF{kompile} are lists of names that
control function inlining in the extracted terms and traversal into
the definitions found in the call graph (explained later).
The \AF{kompile}
macro will obtain the normalized type and body of the main function, run
\AF{kompile-fun} for the actual extraction and recursively extract
any functions that have been registered for extraction during the
processing of \AF{foo}.

To avoid repeated extraction of the same function, \AF{kompile}
keeps track of already compiled functions.%
\footnote{We had to postulate termination of this traversal as
  since the reflection API of Agda currently does not
  provide the guarantee that there is only a finite number of function
  symbols.}
After all required functions have been compiled, the bodies
of all extracted functions are concatenated and
returned as the result of extraction.



\subsection{Kaleidoscope}
We borrow the Kaleidoscope example language from the tutorial on
building frontends to LLVM~\cite{kaleidoscope}. Kaleidoscope is a minimalist first-order
language with a single data type, the type of natural numbers\footnote{The original
version of Kaleidoscope used floats, but natural numbers are easier in the context of Agda
as we can prove more properties of them.},
with basic arithmetic operations and comparisons. Following C convention, boolean values
are encoded as numbers where 0 is false, and any other value is
true.  Function calls and conditionals operate as usual, and `let'
makes it possible
to bind immutable values to variables.  We extend Kaleidoscope with a one-argument \AF{assert}
operator that terminates the program if its argument evaluates to zero.
Functions are defined by giving a name, a list of arguments and the
expression for its body.  External functions are defined by giving a name and a list of its
arguments. We encode Kaleidoskope's AST as follows:

\begin{code}[hide]
module Kaleid where
  open import Data.Nat as ℕ hiding (_≟_)
\end{code}
\begin{mathpar}
\codeblock{%
\begin{code}
  Id = String

  data Op : Set where
    Plus Minus Times Divide : Op
    Eq Neq And Gt Lt : Op

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
}
\and
\codeblock{\begin{code}
  -- Recursive Fibonacci function:
  fib = Function "fib" ("n" ∷ []) $
        If (BinOp Lt (Var "n") (Nat 2))
           (Nat 1)
           (BinOp Plus
            (Call "fib"
                  [ BinOp Minus (Var "n") (Nat 2)])
            (Call "fib"
                  [ BinOp Minus (Var "n") (Nat 1)]))
\end{code}
}
\end{mathpar}

\subsection{A shallow embedding of Kaleidoscope in Agda}
To extract a Kaleidoscope program from an Agda program,
we first need to identify what subset of Agda can be sensibly translated to Kaleidoscope.
Let us start with the types. First, we need the natural
number type \AD{ℕ} as it is the main data type of Kaleidoscope. To
describe invariants we also support the type  \AD{Fin n} of natural number
strictly less than \AD{n}, as well as the identity type
\AD{\_≡\_} and the inequality type \AD{\_<\_} on natural numbers.
The \AD{Fin} type is mapped to numbers in the target language, while
all proofs of \AD{\_≡\_} and \AD{\_<\_} are mapped to the constant \AN{1}.
We also allow the decidability predicates
\AD{Dec (a ≡ b)} and \AD{Dec (a < b)}, which carry a boolean
value and a proof that the relation holds or does not hold,
depending on the value of the boolean.
We map \AC{true} to \AN{1} and \AC{false} to \AN{0}, ignoring the proof. First order
functions of the above types such as basic arithmetic \AD{\_+\_}, \AD{\_-\_},\ldots
are mapped to corresponding functions in the target language.

While it is tempting to say that any Agda term of the above types could
be translated into Kaleidoscope, this is not the case.  For example, consider
a function:
\begin{code}[hide]
module Problem where
  open import Data.Nat.Show renaming (show to showNat)
  open import Data.String using (length)
  open import Data.Nat as ℕ hiding (_≟_)
\end{code}
\begin{code}
  ex : ℕ → ℕ
  ex x = length (showNat x)
\end{code}
where \AF{showNat} returns a string representation of
the given number.  Neither \AF{length} nor \AF{showNat}
are representable in Kaleidoscope, as there is no notion of strings
in the language.
%
In order to pin down precisely what fragment of Agda we can extract,
we would have to restrict what
types are allowed in embedded functions and what terms can appear
in function bodies, taking us away from the world of
shallow embeddings and into the world of deep embeddings.
%
While it is certainly possible to define strongly typed deep
embeddings in a dependently typed host language, all current solutions
are very heavyweight when one has to deal with an embedded language
that uses dependent types, as we do here (recall that we allow
\AF{\_<\_}, \AF{\_≡\_}, \etc{}). In particular, one needs to encode
not only types and terms of the embedded language, but also contexts
and explicit substutions, turning even the simplest programs into
large and non-trivial terms. It is still an open question whether
there exists a satisfying middle ground between shallow and
deep embedding.
%(see Section~\ref{sec:related} for related work in
% this direction).

Our solution in this paper is to avoid the encoding problem entirely
and rely instead on metaprogramming to extract a subset of Agda into
our target language.  An Agda term is defined to belong to the
embedding if the extractor does not fail on it.

% While these are hard and interesting problems in itself, this paper takes a
% radically different approach.  Instead of trying to restrict types and terms
% prior to extraction, we simply allow our extractor to fail.  Extractors
% would have to take care of error reporting, but we would be able to use
% any Agda terms as valid extraction candidates.


\subsection{Normalisation}
Working with a shallow embedding gives us an important benefit: we may use any host
language constructs that are not present in the embedding, as long as they can
be eliminated prior to extraction.  For example, the target language may not
support polymorphic or higher-order functions, yet we could write
programs such as:
\begin{mathpar}
\codeblock{\begin{code}[hide]
module NormMod where
  open import Data.String using (length)
  open import Data.Product
  open import Data.Nat as ℕ hiding (_≟_)
\end{code}
\begin{code}
  ex : (n : ℕ) → n < length "999" → ℕ
  ex = ⋯
\end{code}}
\and
\codeblock{\begin{code}
  fib : (k m n : ℕ) → ℕ
  fib 0        m n  = m
  fib (suc k)  m n  = let  m' , n' = n , m + n
                      in   fib k m' n'
\end{code}}
\end{mathpar}
In the type of \AF{ex}, \AF{length} is a function from \AD{String} to \AD{ℕ}, but
it is applied to a constant string.  In the second clause of \AF{fib} we
create a tuple (\AB{n} \AC{,} \AB{m} \AF{+} \AB{n})
and immediately destruct it via pattern matching. Note that Kaleidoscope
supports neither strings nor tuples, soneither \AF{length} nor \AF{\_,\_}
can be part of the final
extracted Kaleidoscope code.
%The same holds for the universe of types, which we
%could still use as a convention:
%\begin{code}
%  saturated-add : I $ nat ▹ λ max → fin max ▹ λ a → fin max ▹ λ b → ⟨ fin max ⟩ ; saturated-add = ⋯
%\end{code}
However, if we simplify the terms, the result no longer contains any
about strings or tuples, and hence can be extracted safely.


Such a simplification can be conveniently achieved by
normalising the terms, \ie{}~by applying reduction rules to (sub)terms until
they turn into values or neutral terms.
%
%\subsubsection{Telescopes}
Agda's reflection API offers a function \AF{normalise} for this purpose.
However, this will only normalize the term itself and not the body of
functions used in this term.
%
This is a technical limitation that has to do with the chosen internal
represenation of the pattern-matching functions.
%
To work around this limitation, we also recursively traverse the
definition of each function used in the term and normalise all terms
in their bodies.

During the implementation of this traversal, we were faced with
the challenge of reconstructing the right typing context for each clause.
Agda constructs this context internally during elaboration of the clauses,
but the reflection API did not provide access to it. Rather than going
through the painful and error-prone process of reconstructing this
context, we instead extended the reflection API to provide it for us
(see \url{https://github.com/agda/agda/pull/4722} for the full story).
Thanks to this change, it is straightforward to normalise the right-hand
side of each clause in a function definition.

\begin{comment}
In order to normalise the right-hand side of a clause in a function definition,
we need to provide the right context with the types of the pattern
variables of that clause, which is non-trivial to reconstruct.
%
In particular, it is non-trivial because we would have to reverse-engineer
the choices that the Agda type checker made while elaborating the
clause to its internal representation.
%
Here is an example showing the contexts that we would need to compute
for the function that is adding two vectors element-wise:
\begin{code}[hide]
  open import Data.Nat as ℕ hiding (_≟_)
  open import Data.Vec using (Vec; []; _∷_)
\end{code}
\begin{code}
  vadd : ∀ {n} → (a b : Vec ℕ n) → Vec ℕ n
  -- ^ type : {n : ℕ} (a : Vec ℕ v0) (b : Vec ℕ v1) → Vec ℕ v2
  vadd {n} []       _        = []
  -- ^ cxt  : (Vec ℕ 0)
  vadd {n} (x ∷ xs) (y ∷ ys) = x + y ∷ vadd xs ys
  -- ^ ctx  : (m : ℕ) (x : ℕ) (xs : Vec ℕ v0) (y : ℕ) (ys : Vec ℕ v3)
\end{code}
We use the \texttt{vi} notation for de Bruijn index \texttt{i}.  The
first context contains the type for the second vector (underscore),
but does not contain an entry for \AB{n}, as it is instantiated to
\AC{zero} internally.
%
In the second context the binding \AB{m} does not correspond to the
first element of the context, as \AB{n} is instantiated to \AC{suc}
\AB{m} internally.

Instead of trying to recomputing contexts we have extended the reflection
API to provide us the correct one.  This has been implemented in the
pull request \url{https://github.com/agda/agda/pull/4722}.
%
In the new version of the reflection API, each clause of the function
definition comes with an extra argument of type \AD{Telescope}:
\begin{code}[hide]
module TelMod where
  open import Data.Product
  open import Reflection using (Term; Type; Arg; Pattern)
  open import Data.Nat as ℕ hiding (_≟_)
\end{code}
\begin{code}
  Telescope = List (Σ String λ _ → Arg Type)
  data Clause : Set where
    clause        : (tel : Telescope) (ps : List (Arg Pattern)) (t : Term) → Clause
    absurd-clause : (tel : Telescope) (ps : List (Arg Pattern)) → Clause
\end{code}
The telescope is the list of pairs where each pair contains the name
and the type of a free variable.  When the definition is reflected,
the telescope is constructed from the internal representation of the
definition.

As a result, we can straight-forwardly apply normalisation to the body
of the given clause.  Given \AC{clause} \AB{ctx} \AB{pat} \AB{t}, we may
run \AF{inContext} \AB{ctx} (\AF{normalise} \AB{t}) to normalise the body.
%Such a call is performed by \AF{kompile} function for every
%extracted function.
\end{comment}

\subsection{Controlling Reduction}


Fully normalising a term sometimes leads to undesirable results.
Consider the following program:
\begin{code}[hide]
module RedMod where
  open import Relation.Nullary
  open import Data.Nat as ℕ
\end{code}
\begin{code}
  ex₅ : ℕ → ℕ
  ex₅ x with x ≟ 42
  ... | yes _ = 10
  ... | no  _ = 20
\end{code}
The definition of \AF{\_≟\_} in the standard library is quite complex:
\begin{code}[hide]
module RedMod2 where
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary
  open import Relation.Nullary
  open import Data.Bool using (T)
  open import Data.Nat as ℕ hiding (_≟_)
  postulate
    ≡ᵇ⇒≡ : ∀ m n → T (m ≡ᵇ n) → m ≡ n
    ≡⇒≡ᵇ : ∀ m n → m ≡ n → T (m ≡ᵇ n)
    T? : ∀ x → Dec (T x)
  _≟_ : Decidable {A = ℕ} _≡_
  map′ : ∀ {P Q : Set} → (P → Q) → (Q → P) → Dec P → Dec Q ; map′ = ⋯
\end{code}
\begin{code}
  m ≟ n = map′ (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n) (T? (m ≡ᵇ n))
\end{code}
%(the details of how \AF{map′} is defined are not relevant here).
The four functions used in the body (\eg{} \AF{map′}, \AF{≡ᵇ⇒≡}, \etc{}) are not
representable in Kaleidoscope, but comparison of natural numbers is.
%
More generally, there is a common pattern where the host language
represents a concept in a radically different way than in the target
language.
%A typical reason for this is proof relevance, like in the above case, but could also be a general
%invariant that we attach to objects.
In such cases, we can customize the extractor by hard-coding the
mapping of the Agda function to the target language function.  For
example, in this case we map \AF{\_≟\_} to \AC{Eq}.

In order to do this, we have to make sure that normalisation does not expand
certain definitions.  This is what the second argument (base) to our interface
function \AF{kompile} is used for --- to specify the list of functions that
must not reduce during normalisation.
%
This functionality was not previously available in Agda, so we added two new primitives
to the reflection API --- \AF{dontReduceDefs} and \AF{onlyReduceDefs} with pull
request \url{https://github.com/agda/agda/pull/4978}.
%The functions have the following
%types:
%\begin{code}[hide]
%module Funs where
%  open import Reflection using (Name; TC)
%\end{code}
%\begin{code}
%  onlyReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A ; onlyReduceDefs = ⋯
%  dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A ; dontReduceDefs = ⋯
%\end{code}
These functions give us an environment in which any call to
\AF{reduce} or \AD{normalise} will avoid reducing any function that is
in the list (for \AF{dontReduceDefs}) or not in the list (for
\AF{onlyReduceDefs}).
%
This new feature is used by the \AF{kompile} macro to avoid reducing
functions for which we have a fixed translation in the target language.

% \todo[inline]{Here we explain what is the meaning of the arguments
% to kompile, and that we had to extend Agda in order to make this happen}

\subsection{\label{sec:maptypes}Mapping Agda Types to Kaleidoscope Assertions}

The next step after normalisation is to verify and translate the type
signature of the embedded function into the target language.  Kaleidoscope
does not support type annotations, but we
still need to verify that the function is first-order, and that the
argument and return types are from the right universe.
This is implemented in the \AF{kompile-ty} function, of which we present a
small fragment here:
\begin{code}[hide]
module KompTy where
  open import Reflection hiding (TC; return; _>>=_; _>>_)
  open import Reflection.Term
  open import Data.Fin
  open import Data.Bool using (Bool; true)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Nat as ℕ hiding (_≟_)
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
    ok p  ← sps-kompile-term x where error x → ke x
    v     ← PS.cur <$> get
    modify $ _p+=a (mk v (BinOp Lt (Var v) p))
    return $ ok tt
  kompile-ty _ _ = ⋯
\end{code}
It operates within the state monad \AD{SPS} where the state is given
by the type \AD{PS} (pi-type state).  As we traverse the type signature
of a function, for non-dependent types such as \AD{ℕ} we only verify
whether the type is supported.

Dependent types such as \AD{Fin} can be seen as encoding some
predicate on their arguments as well as the element of the dependent
type itself.  We preserve this information encoded in them by mapping
them to assertions in the target language, essentially trading static
checks for dynamic ones.
%
Preserving this information is is important for two reasons.
%
First, the toolchain can
use this information for more aggressive optimisations.  For example,
the Kaleidoscope expression \texttt{if a > b: x else: y} can be simplified
to \texttt{x} if we know from the types that \texttt{a} is greater than \texttt{b}.
Second, extraction can be applied to partial programs.  When extracted
functions are being called externally, the calls are not typechecked, so
the preconditions on the arguments that would normally be enforced by
the type system may not hold.  For example, given
\begin{code}[inline]
  f : (x : ℕ) → x > 0 → ℕ
\end{code}
\begin{code}[hide]
  f = ⋯
\end{code}, its first argument must not be zero.  However, as \AB{x} \AF{>}
\AN{0} cannot be represented, external calls may pass zero to
the extracted version of \AF{f}.

In the case for \AF{Fin} in the definition of \AF{kompile-ty}, we
first extract the argument \AB{x} (obtaining a Kaleidoscope
expression).  Then we get the name of the function argument by
referring to the \AR{PS.cur} field of the state.  Finally, we generate
an assertion that checks whether the encoded witness is less than the
argument to \AD{Fin} (the upper bound), and add it to the state.

In general, to translate a dependent type $\AF{P} : \AF{I} →
\AF{Set}$, we start by picking basic types \AD{TI} and \AD{TP} that
encode \AD{I} and \AD{P}, together with encoding functions $\AF{enc-i}
: \AD{I} → \AD{TI}$ and $\AF{enc-p} : ∀ \{i\} (p : \AD{P}\ i) →
\AD{TP}$.  We then introduce a function $\AF{assrt-p} : (\AB{ti} :
\AD{TI})(\AB{tp} : \AD{TP}) → \AD{Bool}$ that decides whether the
encoded arguments \AB{ti} and \AB{tp} come from a valid input, that is
whether \AB{tp} is the image under \AF{enc-p} of some $\AB{p} :
\AD{P}\ i$ where \AB{ti} is the image of \AB{i}. Finally, we prove
soundness and completeness of the encoding:
\begin{code}[hide]
  I : Set ; TP : Set ; TI : Set
  P : I → Set ; T : Set → Set -- T I ≡ TI ; T (P i) ≡ TP
  enc-i : I → TI ; enc-p : ∀ {i} (p : P i) → TP
  assrt-p : (ti : TI) (tp : TP) → Bool
\end{code}
\begin{code}
  sound-p : ∀ {i}{p : P i} → assrt-p (enc-i i) (enc-p p) ≡ true
  complete-p : ∀ ti tp → assrt-p ti tp ≡ true → ∃₂ λ i (p : P i) → ti ≡ enc-i i × tp ≡ enc-p p
\end{code}
\begin{code}[hide]
  P = ⋯ ; I = ⋯ ; TI = ⋯ ; TP = ⋯ ; T = ⋯
  enc-i = ⋯ ; enc-p = ⋯ ; assrt-p = ⋯ ; sound-p = ⋯ ; complete-p = ⋯
\end{code}
Dependent types with multiple arguments can be
treated in exactly the same way.


% One of the important features of extraction is the ability to propagate
% invariants from Agda down to the target language.  Recall that our original
% goal was to ensure that the function behaves according to the specification.
% This is ensured by the fact that our function typechecks in Agda.  Each
% dependent type in the function signature can be thought of as a (n-fold)
% relation that encodes some facts about its arguments.  This knowledge
% can be very useful to the target language, for example to generate a
% better performing code.  Therefore,
% we turn such relations into assertions in the target language.
%
% Apart from using assertions for optimisations, they are crucially`
% important in case of partial program extractions.  For example:
%%\begin{code}[inline]
%%   f : (x : ℕ) → x > 0 → ℕ
%%\end{code}
%%\begin{code}[hide]
%%  f = ⋯
%%\end{code}
%  However, in the extracted code, the relation
% between the first and the second argument will be lost, and \AF{f} may
% be called with \AN{0} as a first argument.  Assertions would prevent
% this by turning a static check into a dynamic one.


% When generating assertions from the relation we typically have the following
% two options: we can find an encoding for the witness and a way to verify
% that encoded arguments are related by the encoded witness.  The other
% common case is when
% our relation is decidable, the witness structure is not used inside the
% function.  In this case, the encoding of the relation is the unit type,
% and the decision procedure is translated to assertion.

Now, for decidable relations, we can entirely avoid encoding the proof
object, as long as the computational behaviour of the function does not
depend on the structure of the proof. This is in particular always the
case for proof-irrelevant types such as \AD{\_≡\_} and \AD{\_<\_}.
We encode the elements of these types with the unit value (natural number \AN{1}).
We then generate an assertion that uses the decision procedure. This
decision procedure returns an element of the \AD{Dec} type
which we interpret as a boolean value: \AN{1} for \AC{yes} and 0 for \AC{no}.
%Pattern matching on the value of \AD{\_≡\_} is straight-forward as there
%is only one constructor.  Constructors of \AD{\_<\_}
%essentially encode the difference between the arguments, which we
%have chosen not to encode since it can be reconstructed easily.
%Otherwise we were to lose information,  for example:
%\begin{code}
%  ex₆ : ∀ {a b} → a ℕ.< b → ℕ
%  ex₆ (s≤s z≤n) = 1
%  ex₆ (s≤s (s≤s a<b)) = 1 ℕ.+ ex₆ (s≤s a<b)
%\end{code}
%As a consequence we are only allowed to pass the inequality around, but not
%``look inside'' the proof. A different extraction scheme that does not erase
%equality proofs is surely possible, but since we only use inequalities as
%a static assertion erasing them works well in our case.

If a function returns a value of a dependent type, we also generate an assertion
using the same rules. We organise the body of the extracted function
such that there is a fixed variable binding the return value,
and attach the assertion to that variable. Here is an example:
\begin{code}[hide]
module ExFin where
  open import Data.Fin using (Fin; fromℕ<)
  open import Data.Nat.Properties
  open import Data.Nat as ℕ hiding (_≟_)
\end{code}
\begin{code}
  ex₇ : (n : ℕ) → Fin (1 + n * n)     -- def ex7 (x_1):
  ex₇ n = fromℕ< $ n<1+n (n * n)      --   let n = x_1 ; __ret = n * n
                                      --   let __ret_assrt = assert (__ret < 1 + x_1 * x_1)
                                      --   __ret
\end{code}
First, note the
assertion for the return value, which has been generated from the return
type of \AF{ex₇}. Next, recall the types of \AF{fromℕ<} and \AF{n<1+n}:
\begin{code}[hide]
module Signatures where
  open import Data.Fin using (Fin)
  open import Data.Nat as ℕ hiding (_≟_)
\end{code}
\begin{code}
  fromℕ<  : ∀ {m n} → m < n → Fin n
  n<1+n   : ∀ n → n < 1 + n
\end{code}
\begin{code}[hide]
  fromℕ< = ⋯
  n<1+n = ⋯
\end{code}
The \AF{fromℕ<} function turns a proof of \AB{m} \AF{<} \AB{n} into an element of type
\AF{Fin} \AB{n}.  As we are encoding \AF{Fin}s as natural numbers,
the extracted version of \AF{fromℕ<} just returns the first argument of
\AF{\_<\_}, which is the implicit argument \AB{m}.
%
Note that by doing so we are not losing any information,
as the proof here is merely asserting that \AB{m} fits the specification.
%
In general, it is always possible to extract the type-level arguments
of a dependent type such as \AF{\_<\_}, as long as we avoid using
features that distinguish between type-level and term-level arguments
such as parametricity or run-time irrelevance.

It might seem that the assertion on the result is unneccessary, since it is guaranteed to be satisfied
by construction. However, by inserting this assertion we
pass on information further down the toolchain, which may be used for example
by the compiler of the target language to perform more optimizations.
All these assertions may
be turned off if a programmer or a compiler decides so, but this is
not a concern of the extractor.

\subsection{Pattern Matching}
Many target languages do not support function
definitions in a pattern-matching style, whereas in Agda it is the primary
way of defining functions.
%Most Agda data structures are inductive, and pattern-matching
%is a natural way of traversing them. Agda's termination checker also
%relies on structural recursion to prove termination, which requires
%pattern matching to reveal structurally smaller arguments.
Hence extractors often need to transform a definition by pattern matching
into one using conditionals.
In this section we show how to do this, and
demonstrate how implementing the extractor in Agda can lead to
extra safety guarantees.


% The key mechanisms that we need to implement for each constructor \AC{c} of
% some type \AD{X} and its encoding type \AD{TX} is: i) a mapping from \AD{TX}
% into encoding of arguments of \AC{c} that  (\AF{args-c} below); ii) a predicate
% that determines whether the image of the given value of \AD{TX} was originally
% constructed with \AD{c} (\AF{pred-c} below).  The translation scheme looks as
% follows:
%\begin{code}[hide]
%module PatScheme where
%  open import Data.Bool
%  open import Relation.Binary.PropositionalEquality
%  open import Data.Product
%
%  Y : Set ; TX : Set ; TY : Set
%\end{code}
%\begin{code}
%  data X : Set where c : (a₁ : Y) {- ... -} → X
%  enc-x : X → TX ; args-c-a₁ : TX → TY ; pred-c : TX → Bool
%  sound-c : ∀ a → pred-c (enc-x (c a)) ≡ true
%  complete-c : ∀ tx → pred-c tx ≡ true → ∃ λ a → tx ≡ enc-x (c a)
%\end{code}
%\begin{code}[hide]
%  Y = ⋯ ; TX = ⋯ ; TY = ⋯ ; enc-x = ⋯ ; pred-c = ⋯
%  args-c-a₁ = ⋯ ; sound-c = ⋯ ; complete-c = ⋯
%\end{code}
%The predicate \AF{pred-c} is sound when it admits all the
%\AC{c}-based elements of \AD{X}.  The predicate is complete when
%for any admitted value \AB{tx} there exists a \AC{c}-based element
%of \AD{X} that encodes to \AB{tx}.


The problem of compiling a definition by pattern matching splits
naturally into two subproblems: computing a condition from
each given clause, and joining all such conditions in a single conditional.
Let us start with the latter.
%
We implement the algorithm in the \AF{kompile-cls} function
of the following type:
% TODO we also call kompile-term in this function!
\begin{code}[hide]
module Cls where
  open import Reflection
  open import Data.Nat as ℕ hiding (_≟_)
  Strings = List String
  open Kaleid
  open ExtrStructMod using (SKS)

\end{code}
\begin{code}
  kompile-cls : (cls : Clauses) → (vars : Strings) → (ret : String) → SKS (Err Expr)
\end{code}
\begin{code}[hide]
  kompile-cls = ⋯
\end{code}
The first argument is the list of clauses, the second argument is the
list of variable names, and the last argument is the name of the variable
we assign the return value to.  As we are extracting the body of the clauses,
we need to propagate the state of extraction, so the function operates in the \AD{SKS}
monad.  The function traverses clauses in the order they appear
in the definition and combines them in a nested if-then-else chain as
in the following example:
\begin{code}
  ack : ℕ → ℕ → ℕ                                   -- def ack (x1, x2):
  ack 0       n        = 1 + n                      --   if x1 == 0: 1 + x2
  ack (suc m) 0        = ack m 1                    --   else if x1 > 0 && x2 == 0: ack (x1-1) 1
  ack (suc m) (suc n)  = ack m (ack (suc m) n)      --   else: ack (x1-1) (ack x1 (x2-1))
\end{code}
%While the definition of the function is straight-forward,
Note that in the second conditional, we have an explicit check that
\AB{x1} \AF{>} \AN{0}, which is redundant.  However, if the first
and the second clauses were swapped, such a comparison with zero must be
present.  Our current implementation takes a minimalist approach and generates
predicates for each clause separately, without taking the previous clauses
into account.
Many target languages will optimize away such redundant checks.

To compile definitions with absurd clauses, we need a way to abort
computation. For example:
\begin{code}
  ex₁₁ : ∀ n → n < 0 → ℕ      -- def ex11 (x1, x2):
  ex₁₁ n ()                   --   assert (0)
\end{code}
%The function from above does not provide any body, and instead simply shows that
%no arguments can possibly satisfy the type signature.
%
%To generate a syntactically valid program in the target
%language we need to give a body to the function.
%
Rather than returning an arbitrary value, we use \AF{assert} (\AN{0})
to abort computation.
%
When a function has both regular and absurd clauses, we are faced with
a design decision. We can either preserve the absurd clauses and use
\AF{assert} (\AN{0}) as their body, or eliminate them entirely.
While eliminating them is sound, leaving them in can provide valuable
information for the compiler of the target language. Cnsider the following example:
\begin{code}
  ex₁₀ : let P x = x * x + 2 ∸ 3 * x in ∀ x → 0 < P x → ℕ
  ex₁₀ 1 () ; ex₁₀ 2 () ; ex₁₀ x pf = ⋯
\end{code}
We can generate an assertion that \AF{P} \AB{x} is greater than 0, and
after eliminating first two cases, the body of the function would
reduce to a single statement over variables \AB{x} and \AB{pf}.
However, deducing that \AB{x} does not equal \AN{1} or \AN{2} is not
straightforward.  Instead, we preserve this information as an
assertion, so the compiler of the target language can make good use of
it.

The actual translation from patterns to predicates is implemented in
\AF{kompile-clpats}. Here we show only two clauses for compiling a
function that matches on the \AF{Fin} constructors \AC{zero} and
\AC{suc}, respectively.

\begin{code}[hide]
module ClPats where
  open import Reflection hiding (_>>=_; return; _>>_)
  open import Reflection.Term using (Telescope; con)
  open import Data.Fin as F using (Fin; zero; suc)
  open import Data.Product
  open import Data.List using (_++_)
  open import Data.Nat as ℕ hiding (_≟_)
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
  kompile-clpats : Telescope → (pats : List (Arg Pattern)) → (exprs : List Expr) → PatSt → Err PatSt
  kompile-clpats tel (arg i (con (quote F.zero) ps) ∷ l) (e ∷ ctx) pst =
    kompile-clpats tel l ctx $ pst +=c (BinOp Eq e (Nat 0))
  kompile-clpats tel (arg i (con (quote F.suc) ps@(_ ∷ _ ∷ [])) ∷ l) (e ∷ ctx) pst = do
    (ub , pst) ← pst-fresh pst "ub_"
    kompile-clpats tel (ps ++ l) (Var ub ∷ (BinOp Minus e (Nat 1)) ∷ ctx)
                   $ pst +=c (BinOp Gt e (Nat 0))
  kompile-clpats tel ps ctx pst = ⋯
\end{code}
%
The function take four arguments:
the telescope mapping variables used in the pattern list to their names
and types;
the list of patterns; the list of expressions that are being matched
by the patterns; and the state record \AD{PatSt}. When compiling a clause,
the list of expressions is initialised with the function arguments. The state record
contains the counter for fresh variables, the list of conditions
accumulated so far, local assignments, and so on.

For each constructor pattern we produce a condition that holds only
when the encoded value in the target language represents the value
that was built using the given constructor.  For example, as we
represent \AF{Fin} with natural numbers, the conditions for matching
\AB{e} against a pattern \AC{zero} \{\AB{ub}\} constructor is \AB{e}
\AF{==} \AN{0} (note that the precondition generated from the type of
\AB{e} already enforces that \AB{e} \AF{<} \AB{ub}, so we do not need
to check it again).
%
Correspondingly, the pattern \AC{suc} \{\AB{ub}\} \AB{x} yields the condition
\AB{e} \AF{>} \AN{0}.
%
The \AF{pst-fresh} function generates a variable with the unique
(within the clause) name, and \AF{\_+=c\_} adds the new condition to
the state.

Note that we marked this function as terminating.  We had to do so as
the recursive call to \AF{kompile-clpats} with argument \AB{ps}
\AF{++} \AB{l} is not structurally decreasing.
%Indeed, if we keep increasing the list of the patterns at each recursive step
%then the function might not terminate.
%While this particular function
%is actually safe, we can prove this formally, demonstrating the power
%of Agda when building extractors.
%
Nevertheless, the function is terminating because the \AF{Pattern}
type is well-founded, and all the objects of that type are finite.
The full version of our code works around this limitation of the
termination checker by adding an extra argument expressing the
overall size of the pattern, but we omit it here for simplicity.

\begin{comment}
We can prove this formally
by extending \AF{kompile-clpats} with an extra argument $\AB{m} : \AF{ℕ}$,
together with a proof of \AF{sz} \AB{pats} \AF{<} \AB{m}, where
the size of a list of patterns is defined as follows:
\begin{code}
  sz : List (Arg Pattern) → ℕ
  sz [] = 0
  sz (arg i (con c ps) ∷ l) = 1 + sz ps + sz l
  sz (arg i _ ∷ l) = 1 + sz l
\end{code}
For a given pattern list we chose an upper bound that is one greater than the
actual size of the pattern list. For the full details of how we prove
termination of \AF{kompile-clpats}, see the code accompanying this paper.
\end{comment}

\begin{comment}
Therefore, if we find a
metric that would witness this and decrease at each \AF{kompile-clpats} call,
our recursion would become structural.  Here is one way to do this:
\begin{code}
  ps++l<m : ∀ {m} ps l → suc (sz ps + sz l) ℕ.< suc m → sz (ps ++ l) ℕ.< m
  sz[l]<m : ∀ {m} ps l → suc (sz ps + sz l) ℕ.< suc m → sz l ℕ.< m

  kompile-clpats′ : ∀ {m} → Telescope → (pats : List (Arg Pattern)) → .(sz<m : sz pats ℕ.< m)
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
  open import Data.Nat as ℕ hiding (_≟_)
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
\end{comment}

As a side note, Agda internally represents definitions by pattern
matching as \emph{case trees} where most redundant checks have been
eliminated. However, unfortunately this representation is currently
not available via the reflection API. However, if we wanted to
generate more efficient code it would probably be simpler to extend
the reflection API rather than reimplement the translation to a case
tree ourselves.

%\todo[inline]{Do we want to say anything about the overall idea of folding
%  pattern-matching cases into a conditional, and reverse mappings of the
%  encoding back into constructors that we are dealing with?}

% \todo[inline]{Explain how do we turn a pattern-matching function definition
% into a single definition with a conditional inside.  We have to make sure
% that we explained the telescopes (or explain them here), and we can
% reiterate absurd patterns here.}

\subsection{Translating terms}
The actual translation of Agda terms into Kaleidoscope terms is a
mechanical process.  However, as the translation may fail, the use of
monads and \AK{do}-notation for managing errors help us to keep the
code clean:
\begin{code}[hide]
module KompTerm where
  open import Reflection hiding (_>>=_; return; _>>_)
  open import Reflection.Term
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong)
  open import Relation.Nullary
  open Kaleid
  open ExtrStructMod using (SKS)
  open import Data.Fin as F using ()
  open import Data.List using (length; _++_)
  open import Data.Nat as ℕ hiding (_≟_)
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
  kompile-term : Term → Telescope → SKS (Err Expr)
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
return actions.  As each monad is an applicative functor, we get \AF{\_<\$>\_}
and \AF{\_⊛\_} operations for free.  The instance resolution
mechanism\footnote{For the details see the ``Instance Arguments''
  section of Agda's manual~\cite{agda}.}
makes it possible to overload monadic/functorial operations without explicitly
mentioning in which monad we are operating.

A typical case of \AF{kompile-term} extracts the arguments and puts them
together in a corresponding expression of the target language,
as for example in the case for \AF{\_+\_}.

For some constructions it is convenient to handle arguments without
explicitly pattern-matching them, \eg{} some constructor with a long argument
list where we are interested only in a particular subset.  For such reasons we
introduce the \AF{kompile-arglist} function where the first argument
is the list of \AC{Arg}uments; and the second argument is the mask that specifies
indices into the first argument.  The function extracts each argument from the
list as specified by the mask.  In case of \AF{fromℕ<} we use this function to
extract the first argument from the \AB{args} list.

The last clause deals with general function calls that do not require special
treatment.  We first ensure that argument list is non-empty: the \AF{\_ ∷ \_} pattern.
Then we add the name of the function into the \AR{funs} field of the state record,
which is used by \AF{kompile} to extract all the necessary dependencies.
Then we extract the arguments, using
the helper function \AF{mk-iota-mask} that generates indices from \AN{0} to the
length of the argument list.  Finally we create an \AD{Expr}ession for a function
call.  We use the extracted arguments and we normalise the name to get rid of
unicode symbols.



\subsection{Example}
% \todo[inline]{This is an example explaining how to define a function
%   that is not structurally recursive.  Is it worth while keeping?
%   We use the same technique in the kompile-clpats.  Maybe make it
%   into a final example and demonstrate that we can extract it.}

Let us consider the actual output that our extractor generates for a
reasonably complex function:  the binary logarithm.
We take the simplest specification, and we assume that logarithm of zero
is zero.  One difficulty with this function is that it is not structurally
recursive and Agda does not recognise that it terminates. We use a standard
technique of recursing on a well-founded \AF{\_<\_} predicate (inequality
of natural numbers) to prove termination.  Here is the Agda definition and the extracted code
(slightly reformatted) arranged side-by-side:

\begin{code}[hide]
  open import Data.Nat.DivMod
  open import Data.Nat.Properties
\end{code}
\begin{code}
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
actual work happens.  We define two base cases for \AN{0} and \AN{1} and the recursive
case on the argument divided by \AN{2}.  Note that the function
$\AF{\_/\_}~:~(x\ y~:~\AD{ℕ}) \{\AB{≢0}~:~\AF{False} (\AB{y}\ \AD{≟}\ \AN{0})\} → \AD{ℕ}$ takes an implicit
argument that asserts that the divisor is non-zero. Agda is capable to deduce the proof
automatically for constant values such as \AN{2}.  In the extracted code we start with
the assertion that was extracted from the type of \AB{n<m}.  The first case is trivial.
In the second case we see \AB{x\_2} \AF{-} \AN{1} \AF{==} \AN{0},
rather than \AB{x\_2} \AF{==} \AN{1}, which is an artefact of the algorithm
used in \AF{kompile-clpats} and the fact that \AN{1} is represented as
\AC{suc} \AC{zero}.  This is a correct translation, as we ensure that \AB{x\_2}
is greater than zero before subtracting one.  However, this could be further
optimised either by the target language or as a post-extraction step.

In the recursive case, division looks suspiciously complex.
%
The reason for the complexity of the division
operation is because \AF{\_/\_} in Agda is defined in terms of a helper function
\AF{div-helper} \AB{k} \AB{m} \AB{n} \AB{j} that corresponds to the expression
\AB{k} \AF{+} ((\AB{n}\AF{+}\AB{m}\AF{-}\AB{j}) \AF{/} (\AN{1}\AF{+}\AB{m})).
We could have suppressed the normalisation of \AF{\_/\_}, but this is not
generally desirable, as it prevents evaluation prior to extraction.  For example,
without suppression (\AN{2}\AF{+}\AB{n})\AF{/}\AN{2} normalises to
\AN{1}\AF{+}(\AB{n}\AF{/}\AN{2}), whereas with \AF{\_/\_} suppressed it would be treated
as an opaque object.

Also note how the recursive call uses the value \AN{1} instead of an
actual proof. Per our assumption, \AF{\_<\_} is used as a static assertion
(we cannot pattern-match on its value).  This means that any function that has
a return type \AB{a} \AF{<} \AB{b} can be replaced with the unit value.  This
is valid, because we are extracting function calls that were verified by the
typechecker.  Therefore, we can completely omit the proof part of \AF{\_<\_},
only acknowledging that the type is inhabited.  This particular case relies
on \AF{≤-trans} (from the inlined proof) and \AF{≤-refl} (from \AF{log₂}
definition) being extracted into unit values.

There is also the final \AK{else} case, which is not specified in the
original code on the left.  The reason for this extra case is that our
pattern matching is not complete.  We are missing the case where
\AB{m} is zero and \AB{n} is greater than \AN{2}.  While Agda's
coverage checker agrees that such case is impossible, it automatically
inserts the missing case into internal representation as an absurd
clause.

%Finally, in the \AF{log₂} definition, \AF{≤-refl} is a proof that \AB{x} is less
%than \AB{x}\AF{+}\AN{1}.




\subsection{\label{sec:rewriting}Rewriting}
% \todo[inline]{Explain how rewriting rules could be used as additional
% optimisation steps prior extraction.  Mention that the availability of
% telescopes (that Jesper added to Agda) facilitates pushing rewriting
% under the function clauses, which used to be a nightmare.}

A common way to define domain-specific compiler optimizations is through
the specification of \emph{rewrite rules} that rewrite terms matching
a given pattern to an equivalent form that is either more efficient
or reveals further optimization opportunities.
%
By giving a shallow embedding of our target language in Agda, we have
the opportunity to define \emph{verified} rewrite rules, providing
a proof that the left- and right-hand side of the rewrite rule are
equivalent.
%
To achieve this, we could define our own representation of verified
rewrite rules and integrate them into the extractor.
%
However, we can avoid the effort of doing so since Agda already has a
built-in concept of rewrite rules.
%
Rewrite rules were originally introduced to Agda to work around the
limitations of definitional equality in intentional type theory.
%
For example, it can be used to make $0 + x$ definitionally equal to
$x + 0$.
%
Since we work with a shallow embedding, these rewrite rules are
equally well suited to optimize the embedded programs we write before
they are extracted.

\begin{comment}
One of the unfortunate features of intuitionistic dependently-typed systems is the
distinction between definitional and propositional equalities.  A famous
example that demonstrates the problem is the addition of natural numbers defined
inductively on the first argument:
\begin{code}[hide]
module PlusZ where
  open import Data.Nat as ℕ hiding (_≟_; _+_)
  open import Relation.Binary.PropositionalEquality
  open import Agda.Builtin.Equality.Rewrite
\end{code}
\begin{mathpar}
\codeblock{%
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  _+_ 0       b = b
  _+_ (suc a) b = suc (a + b)
\end{code}
}
\and
%With this definit \AN{0}\AF{+}\AB{x} is definitionally equal to \AN{x},
%but \AB{x}\AF{+}\AN{0} is not:
\codeblock{
\begin{code}
  0-p : ∀ x → 0 + x ≡ x
  0-p x = refl
\end{code}
}
\and
\codeblock{
\begin{code}
  p-0 : ∀ x → x + 0 ≡ x
  -- does NOT hold
  -- definitionally
\end{code}
}
\end{mathpar}
\begin{code}[hide]
  p-0 = ⋯
\end{code}
The problem is that there is no explicit reduction rule that can be applied
to \AB{x}\AF{+}\AN{0} --- it is a neutral term.  As computation is an
essential part of dependent type checking, some perfectly reasonable
programs may be rejected.  For example, a vector of length \AB{n}
concatenated with an empty vector is not of the type vector
of length \AB{n}:
\begin{code}
  -- rejected : ∀ {n} → (x : Vec ℕ n) → Vec ℕ n
  -- rejected x = x ++ []
\end{code}
The reason is that \AB{x} \AF{++} \AC{[]} is of type \AD{Vec} \AD{ℕ}
(\AB{n} \AF{+} \AN{1}).  This problem might seem too theoretical, unfortunately
such cases are very often seen in practice, as a result of a long
$\beta$-reduction sequence.  In the context of extraction, such terms
make the extracted code less efficient.

Fortunately, Agda makes it possible to work around this
problem with rewrite rules~\cite{DBLP:conf/types/Cockx19}. Any binary
relation can be registered as a source of rewrites.  Propositional equality
\AF{\_≡\_} is typically a good choice.  Functions that return such a relation
can be registered as rewrite rules.  For example:
\begin{mathpar}
\codeblock{%
\begin{code}
  --plus-0 : ∀ x → x + 0 ≡ x
  --plus-0 zero    = refl
  --plus-0 (suc x) = cong suc $ plus-0 x
\end{code}
}
\and
\codeblock{
\begin{code}
  --{-# REWRITE plus-0 #-}
  --plus-0-test : ∀ x → x + 0 ≡ x
  --plus-0-test x = refl
\end{code}
}
\end{mathpar}
We have defined a propositional equality \AF{plus-0}, and registered it as a
rewrite rule.  By doing so, \AF{plus-0} became a defintional equality, and
we go the ``missing'' reduction rule.  We can now show that \AB{x}\AF{+}\AN{0}
is definitionally equal to \AB{x}.

In the context of extraction rewrite rules can be seen as a mechanism to define
custom optimisations.  As rewrite rules are applied prior to extraction, extractors
are operating on rewritten terms. The benefit of this approach is that rewrite
rules that we register are \emph{formally verified} (when using \AF{\_≡\_} as a
rewrite relation).
\end{comment}
%
A typical example of a rewrite rule in Agda rewrites expressions of
the form \AB{x} \AF{+} 0 to \AB{x}:
%
\begin{code}
  plus-0 : ∀ x → x + 0 ≡ x
  plus-0 zero    = refl
  plus-0 (suc x) = cong suc $ plus-0 x
  {-# REWRITE plus-0 #-}
\end{code}
The definition of \AF{plus-0} proves the equivalence of the left- and
right-hand sides of the rule, and the \AK{REWRITE} pragma registers it as a
rewrite to be applied automatically during normalisation.  As another
example, we could define the following rule that we were taught in
school:
\begin{code}[hide]
module PlusZSolv where
  open import Data.Nat as ℕ hiding (_≟_)
  open import Relation.Binary.PropositionalEquality
  open import Agda.Builtin.Equality.Rewrite
\end{code}
\begin{code}
  open import Data.Nat.Solver ; open +-*-Solver
  sum-square : ∀ x y → x * x + 2 * x * y + y * y ≡ (x + y) * (x + y)
  sum-square = solve 2 (λ x y → x :* x :+ con 2 :* x :* y :+ y :* y :=  (x :+ y) :* (x :+ y)) refl
  {-# REWRITE sum-square #-}
\end{code}
%so that we can perform two arithmetic operations instead of six when computing
%the polynomial.

It might seem that such an example of rewriting expressions
over natural numbers are not very practical, but the benefit becomes more
obvious for more complex data structures.
%
For example, here is the famous fusion law for distributing \AF{map}s over
function composition \AF{\_∘\_}:
\begin{code}[hide]
  open import Data.List using (map)
\end{code}
\begin{code}
  map-∘ : ∀ {X Y Z : Set}{g : X → Y}{f : Y → Z} → ∀ xs → (map f ∘ map g) xs ≡ map (f ∘ g) xs
  map-∘ []        = refl
  map-∘ (x ∷ xs)  = cong (_ ∷_) (map-∘ xs)
  {-# REWRITE map-∘ #-}
\end{code}
Instead of traversing all the elements
of \AB{xs} and then all the elements of the \AF{map} \AB{g} \AB{xs}, we can compute
the same result in a single traversal.  Generally, we often know a number of properties
about the data structures we are working with.  In a dependently-typed systems we can
make those properties explicit and formally verify them, but in rewriting-capable
systems we can selectively turn properties into optimisations.

% One danger with custom rewrite rules is the ability to create a sequence of
% non-terminating rewrites.  For example if one registers commutativity of addition
% as a rewrite rule, then any expression of the form \AB{a} \AF{+} \AB{b} would
% cause an infinite sequence of rewrites.

One danger with rewrite rules is that we can get different result depending on the order of rule application.
The recently introduced confluence checker~\cite{10.1145/3434341}
helps to prevent this problem.  When it is turned on, it will report
when the registered set of rewrite rules is not
confluent.  For example, in case of \AF{plus-0} rule, the confluence checker
complains that
\AF{plus} (\AC{suc} \AB{x}) \AC{zero} can be rewritten to either
(\AC{suc} \AB{x}) or \AC{suc} (\AF{plus} \AB{x} \AC{zero}).  If
we add a new rewrite rule for \AF{plus} (\AC{suc} \AB{x}) \AC{zero} $\mapsto$
\AC{suc} \AB{x}, our rewrite system is again accepted.

%The other known danger is that rewrite rules can lead to a never
%terminating sequence of rewrites.  While confluence does not guarantee
%termination, in combination with restriction that the left-hand-side
%of each rule that must be a constructor or a function applied to neutral terms,
%it helps to prevent some cases of non-termination.  For example, it keeps us
%from registering commutativity of addition as a rewrite rule, which would
%otherwise lead to non-termination.

% In case of commutativity,
% the confluence checker would complain that \AN{0} \AF{+} \AB{m} reduces
% to \AB{m} but rewrites to \AB{m} \AF{+} \AC{zero}, so fixing this would
% require a rule \AB{m} $\mapsto$ \AB{m} \AF{+} \AC{zero}, but such a rewrite
% is not allowed, as the left hand side is not a constructor/function application.
% For more details on rewrite rules and their confluence checking refer to~\cite{}.


\subsection{Monadic Workaround for Lets}
One of the unfortunate design choices of the Agda internal language is
the lack of a `let' construct.  All the lets we use in the code are eliminated
eagerly through substitution of the bound expression in the body.  While
this is semantically sound, it leads to unnecessary code duplication:
\begin{code}
  ex₈ : ℕ → ℕ
  ex₈ x = let a = x * x + 3 * x + 5 in a + a -- ⇒ (x * x + 3 * x + 5) + (x * x + 3 * x + 5)
\end{code}
While changing Agda itself to support `let' in the internal language
would be a major change, we can use the following
elegant workaround.  Agda's do-notation is a syntactic sugar that
expands to the monadic bind \AF{\_>>=\_}.
In particular, we can work in the identity monad by defining
$a~\AF{>>=}~f = f~a$ and adding it to our extractor,
\begin{code}[hide]
module Monadic where
  open import Data.Nat as ℕ hiding (_≟_)
\end{code}
\begin{code}[hide]
  _>>=_ : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂} → A → (A → B) → B
  a >>= f = f a
  return : ∀ {ℓ}{A : Set ℓ} → A → A
  return a = a
\end{code}
allowing us to use do-notation instead of let:
\begin{code}
  ex₈′ : ℕ → ℕ
  ex₈′ x = do a ← x * x + 3 * x + 5; a + a
\end{code}


%\todo[inline]{Explain that we can workaround the lack of lets in the internal
%syntax by introducinog a fake monad; give an example.}
