\begin{code}[hide]
postulate
  ⋯ : ∀ {a}{A : Set a} → A
module _ where
module Basics where
\end{code}
\section{Background}
We start with a brief overview of key Agda constructions that
are used in this paper.  We also present relevant parts of the
reflection API.  For a more in-depth introduction to Agda refer
to the Agda user manual~\cite{agda}.

\subsection{Agda Basics}
Agda is an implementation of Martin-L{\"o}f's dependent type
theory~\cite{Martin-Lof-1972} extended with many convenience
constructions such as records, modules, do-notation, \etc{}
Types are defined using the following syntax:
\begin{mathpar}
\codeblock{
\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
\end{code}
}
\and
\codeblock{
\begin{code}
  data Fin : ℕ → Set where
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} → Fin n → Fin (suc n)
\end{code}
}
\and
\codeblock{
\begin{code}
  data _≡_ {a} {A : Set a}
      (x : A) : A → Set a where
    refl : x ≡ x
\end{code}
}
\end{mathpar}
Unary natural numbers \AD{ℕ} is a type with two constructors:
\AC{zero} and \AC{suc}.  \AD{Fin} is an indexed type, where the index
is of type \AD{ℕ}.  Constructor names can be overloaded and are
disambiguated from the typing context, or can be prefixed with the
type name: \AC{ℕ.zero}, \AC{ℕ.suc}.
%
The \AD{Fin} \AB{n} type represents natural numbers that are bounded
by \AB{n}.  In the definition of \AD{Fin}, ∀ binds the variable
without needing to specify its type.  Curly braces indicate hidden
arguments, which can be left out at function applications: we have
\AC{suc} \AC{zero}~:~\AD{Fin} \AN{3}, assuming that Agda can infer a
(unique) value for the hidden argument.  Hidden arguments can be
passed explicitly using the syntax $\AC{zero}\ \{\AB{n} = \AB{x}\}$.
%
The propositional equality type \AF{\_≡\_} expresses equality of its
two arguments, and has a single constructor \AC{refl} stating that any
value \AB{x} is equal to itself.  It uses mixfix
syntax~\cite{10.1007/978-3-642-24452-0_5}: the
underscores in the name indicate placeholders for the arguments.
%
\AF{Set} is the name of the type of all small types.  Sets form a
predicative hierarchy, meaning that \AF{Set} \AB{i} is of type
\AF{Set} (\AF{ℓsuc} \AB{i}), and \AF{Set} is a synonym for \AF{Set}
\AF{ℓzero}.  The functions \AF{ℓsuc} and \AF{ℓzero} are used to construct elements of type \AD{Level}.


Functions are defined in a pattern-matching style:
\begin{code}[hide]
  postulate _+_ : ℕ → ℕ → ℕ

\end{code}
\begin{mathpar}
\codeblock{
\begin{code}
  _*_ : ℕ → ℕ → ℕ
  zero     * y  = zero
  (suc x)  * y  = y + (x * y)
\end{code}
}
\and
\codeblock{
\begin{code}
  abs : Fin zero → ℕ
  abs ()
\end{code}
}
\and
\codeblock{
\begin{code}
  wth : (a b : ℕ) → ℕ
  wth a b with a * b
  ...     | zero = zero
  ...     | _    = b
\end{code}
}
\end{mathpar}
The definition of \AF{abs} uses the \emph{absurd pattern} (),
indicating an impossible case for the first argument, \ie{} there is
no constructor constructing a term of type \AD{Fin} \AC{zero}.
Clauses with absurd patterns do not have a body, as the type system
guarantees that they are never called at run-time.
%
In the definition of \AF{wth} we demonstrate the use of the \AK{with}
construction~\cite{10.1017/S0956796803004829} which makes it possible
to match on the result of an expression locally.

% \todo[inline]{Amongst other things we need to explain with-clauses
%   and pattern-matching functions.  Maybe records and their eta-equality.
%
%   Nat, Fin, Vec, Eq, with, patterns, hidden values, mixfix}

\subsection{Reflection}
Instead of explaining the full structure of all types that Agda uses
to encode reflected syntax, we consider a small but representative
sample: the function \AF{foo} (left) and its reflection (right).
\begin{code}[hide]
module FunExample where
  open import Data.List
  open import Data.Nat
  open import Data.Fin using (Fin)
  open import Data.Bool
  open import Reflection
  open import Data.Unit
  open import Data.Product
  open import Function

\end{code}
\begin{mathpar}
\codeblock{
\begin{code}
  foo : ℕ → ℕ
  foo 0        = zero
  foo (suc x)  = x + x
\end{code}
}
\and
\codeblock{
\begin{code}
  `foo = Definition.function
       $ Clause.clause
           []
           (vArg (Pattern.con (quote ℕ.zero) []) ∷ [])
           (Term.con (quote ℕ.zero) [])
       ∷ Clause.clause
           (("x" , vArg (Term.def (quote ℕ) [])) ∷ [])
           (vArg (Pattern.con (quote ℕ.suc) (vArg (Pattern.var 0) ∷ [])) ∷ [])
           (def (quote _+_) (vArg (Term.var 0 []) ∷ vArg (Term.var 0 []) ∷ []))
       ∷ []
\end{code}
}
\end{mathpar}
The reflected function is defined by the list of clauses \AC{Clause.clause}.  Each
clause has three arguments: i) the telescope, which is a list of free variables
and their types; ii) the list of patterns; and iii) the body of the
clause.  The first clause does not have free variables, so the telescope
is empty. The second clause has one variable called \AB{x}.  The
pattern list in the first clause has one argument;  \AC{vArg} denotes that
it is visible argument (\AC{hArg} is used for hidden arguments).
The actual pattern matches against the \AC{zero} constructor, as expressed
by \AC{Pattern.con}, which has two arguments: the reflected constructor name and the
list of reflected arguments.  The number of reflected arguments must be the
same as the number of the actual arguments, which is none in the case of \AC{zero}.
The \AK{quote} primitive returns
a representation of the name for the given Agda definition or constructor,
which is of type \AD{Name}.
%
Variables (both in patterns and in terms) are given as de Bruijn indices
into the telescope of the clause.  That is, in the second clause the
de Bruijn index \AN{0} refers to the variable \AS{x}.  Note that we write
\AN{0} instead of \AC{zero}, as numbers are expanded
into their corresponding \AC{zero}/\AC{suc} representations.


Effectively using Agda's reflection API can be challenging because the
syntax it uses matches the \emph{internal}
representation of Agda terms, which differs significantly from the
surface syntax.
%
Many constructs such as
implicit arguments, instance arguments, \AK{let} and \AK{with} definitions
exist only in the surface language.  Translation from the surface
language is performed by the \emph{elaborator}.
%As types may depend
%on the values, elaboration involves evaluation of expressions.
%
%For example, if the function
%{
%\begin{code}[inline]
%  f : (x : Bool) → if x then ℕ else Bool
%\end{code}
%\begin{code}[hide]
%  f = ⋯
%\end{code}
%}
%
%is applied to the value \AC{true}, the type of the result will compute
%to \AF{ℕ}.
Following the approach of \emph{elaborator reflection}
introduced by Idris~\cite{idris-refl}, Agda exposes many parts
of the elaborator to the reflection API, including reduction
and normalisation of expressions.
%
These operations are made available through the \AD{TC} monad, which
takes care of managing the current context of the elaborator.

The key metaprogramming primitives are \AK{quote} and
\AK{unquote}, that operate as follows:
\begin{mathpar}
\codeblock{
\begin{code}
  ex : (a : Bool) → if a then ℕ else Bool
  ex true = unquote helper
    where helper : Term → TC ⊤
          helper h = unify h (lit (nat 42))
  ex false = false
\end{code}
}
\and
\codeblock{
\begin{code}
  macro getDef : Name → (Term → TC ⊤)
        getDef n h = do
         d ← getDefinition n
         t ← quoteTC d
         unify h t
  ``foo = getDef foo
\end{code}
}
\end{mathpar}
In \AF{ex}, the \AK{unquote} occurs in the \AC{true} clause of the
function.
%In this case the return type of the function normalises to
%\AD{ℕ}.  Therefore, the type of \AK{unquote} \AF{helper} must be
%\AB{ℕ} as well.
%
The argument to \AK{unquote} is expected to be a
function of type \AD{Term} → \AD{TC} \AD{⊤}, where \AD{⊤} is the unit
type. During elaboration,  Agda creates a
metavariable \AB{h} of type \AD{ℕ}, quotes it, and passes it to the
function \AF{helper}. In the body of \AF{helper}, we call the \AF{TC}
operation \AF{unify} \AB{h} (\AC{lit} (\AC{nat} \AN{42})) to
unify the two expressions, instantiating
\AB{h} to the value 42.  Finally, Agda replaces the
expression \AK{unquote} \AF{helper} expression with the instantiated
value of \AB{h}.  Overall, the effect of \AK{unquote} \AF{helper} is
identical to just writing \AN{42}.  However, the expression inside the
\AF{helper} can be arbitrarily complex and can depend on the syntactic
structure of the term \AB{h} as well as information obtained through
operations in the \AF{TC} monad.

Instead of quoting/unquoting explicitly, we can use the \AK{macro}
keyword to wrap any function with return type \AD{Term} →
\AD{TC} \AD{⊤}.  This takes care of quoting the arguments and unquoting
the result.  On the right, we define a macro \AF{getDef} that
obtains the definition of a name.  The macro calls three functions
from the reflection API.  Firstly, \AF{getDefinition} obtains the definition
of the object with the name \AB{n}.  Secondly, \AF{quoteTC} quotes the
previously obtained definition (resulting in a doubly-quoted expression).
Finally, we \AF{unify} the quoted hole and the doubly quoted definition,
so that after unquoting we get the reflected definition (and not the
original one).  We apply the macro in the last line, and as can be seen,
no \AK{quote}/\AK{unquote} is needed.
%
More details on reflection in Agda can be found in the user
manual~\cite{agda}.


% \begin{code}[hide]
%  module TermLang where
%   open import Data.List
%   open import Data.Nat
%   postulate
%     Sort   : Set
%     Clause : Set
%     Name : Set
%     Visibility : Set
%     Literal : Set
%     Meta : Set
%   data Arg {a} (A : Set a) : Set a where
%   data Abs {a} (A : Set a) : Set a where
%   data Term : Set
%   Type = Term
% \end{code}
%
% The actual innternal data representation is very compact:
% \begin{code}
%   data Term where
%     var       : (x : ℕ) (args : List (Arg Term)) → Term
%     con       : (c : Name) (args : List (Arg Term)) → Term
%     def       : (f : Name) (args : List (Arg Term)) → Term
%     lam       : (v : Visibility) (t : Abs Term) → Term
%     pat-lam   : (cs : List Clause) (as : List (Arg Term)) → Term
%     pi        : (a : Arg Type) (b : Abs Type) → Term
%     agda-sort : (s : Sort) → Term
%     lit       : (l : Literal) → Term
%     meta      : (x : Meta) → List (Arg Term) → Term
%     unknown   : Term
%
%   data Definition : Set where
%     function    : (cs : List Clause) → Definition
%     data-type   : (pars : ℕ) (cs : List Name) → Definition
%     record-type : (c : Name) (fs : List (Arg Name)) → Definition
%     data-cons   : (d : Name) → Definition
%     axiom       : Definition
%     prim-fun    : Definition
% \end{code}
