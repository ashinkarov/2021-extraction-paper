\begin{code}[hide]
postulate
  ⋯ : ∀ {a}{A : Set a} → A
module _ where
module Basics where
\end{code}
\section{Background}
We start with a brief overview of key Agda constructions that
are used in this paper.  We also present relevant parts of the
reflection API.  For full introduction to Agda refer to~\cite{}.

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
Unary natural numbers \AD{ℕ} is a type with two constructors: \AC{zero}
and \AC{suc}.  \AD{Fin} is an indexed type, where the index is of type
\AD{ℕ}.  As it can be seen, the names of the constructors are allowed to
coincide.  They are disambiguated from the type context, or they can be
prefixed with the type name: \AC{ℕ.zero}, \AC{ℕ.suc}.  In \AD{Fin} definiton,
\AS{∀} binds the variable name without the need to specify type.  The
arguments inside braces are called hidden, meaning that they can be leaved
out at function applications: we write \AC{suc} \AC{zero}, assuming
that there is enough typing information.  Hidden arguments can be passed
explicitly as follows: \AC{zero} \{\AB{n} \AS{=} \AB{x}\}.
The \AD{Fin} \AB{n} type represents natural
numbers that are bound by \AB{n}.  The propositional equality \AF{\_≡\_} type
is a relation of two arguments, and it has a single constructor.  It uses the
mix-fix syntax~\cite{}, meaning that the underscores in the name indicate
placeholders for the arguments.  \AF{Set} is the name of the type of all
small types.  Sets form a predicative hierarchy, meaning that \AF{Set} \AB{i}
is of type \AF{Set} (\AC{suc} \AB{i}), and \AF{Set} is a synonym for
\AF{Set} \AN{0}.

Functions are defined in a pattern-matching style, where patterns are checked
in order as they appear.
\begin{code}[hide]
  postulate _+_ : ℕ → ℕ → ℕ

\end{code}
\begin{mathpar}
\codeblock{
\begin{code}
  _*_ : ℕ → ℕ → ℕ
  zero * y = zero
  (suc x) * y = y + (x * y)
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
The definition of \AF{abs} uses the \emph{absurd pattern}.
The () symbol indicates an impossible case for the first argument,
\ie{} there is no constructor(-s) leading to \AD{Fin} \AC{zero}.
Absurd patterns do not have body, as anything can be deduced from
falsehood.  In the definition of \AF{wth} we demonstrate the use
of the \AK{with} construction~\cite{} which makes it possible to
match local expressions similarly to function arguments.

% \todo[inline]{Amongst other things we need to explain with-clauses
%   and pattern-matching functions.  Maybe records and their eta-equality.
% 
%   Nat, Fin, Vec, Eq, with, patterns, hidden values, mixfix}

\subsection{Reflection}
Instead of specifying exact structure of all the types that are being
used to encode reflected terms, we consider a small but representative
example: the function \AF{foo} and its reflection.  The term on the right
is built entirely out of constructors.  We annotate each constructor with
the name of the type it belongs to, \ie{} instead of \AC{zero} we write
\AC{ℕ.zero}.
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
The function is defined by the list of clauses \AC{Clause.clause}.  Each
clause has three arguments: i) the telescope which is a list of free variables
and their types; ii) the list of patterns; iii) the body of the
clause.  The first clause does not have free variables, so the telescope
is empty.  In the second clause we have one variable called \AB{x}.  The
pattern list in the first clause has one argument;  \AC{vArg} denotes that
it is visible argument. We would use \AC{hArg} for hidden arguments.
The actual pattern matches against the \AC{zero} constructor.  This is expressed
with \AC{Pattern.con} which hsa two arguments: reflected constructor name and the
list of reflected arguments.  The number of reflected arguments must be the
same as the number of the actual arguments.  As \AC{zero} has no arguments,
we pass empty list to \AC{Pattern.con}.   The \AK{quote} function returns the
name of type \AD{Name} for the given Agda definition or constructor.
Variables inside of patterns and terms are given as de Bruijn indices
into the corresponding telescope.  That is, in the second clause the
reference to \AS{x} is the de Bruijn index zero.  Note that we write
\AN{0} instead of \AC{zero}, as numbers are expanded
into their corresponding \AC{zero}/\AC{suc} representations.




Metaprogramming within the
dependently-typed system is challenging because there is a significant
gap between the surface and core languages.  Many constructs such as
implicit arguments, instances, \AK{let} and \AK{with} definitions
exist only in the surface language.  Translation from the surface
language is performed by the \emph{elaborator}.  As types may depend
on the values, elaboration involves computing normal forms which may
reveal new information about the terms.  For example, if the function
{
\begin{code}[inline]
  f : {x : Bool} (n : ℕ) → if x then ℕ else Fin n
\end{code}
\begin{code}[hide]
  f = ⋯
\end{code}
} is applied in the context where the value of \AB{x} is known,
the type of the function application will change.  As we want
reflected code to be type
safe, we have to pass this changing information to metaprograms.
That is why Agda's reflection API, following
Idris~\cite{idris-refl} design, exposes elaboration context
to the language.

All the metaprogramming operations are happening within the
\AD{TC} monad, so that the elaboration context could be properly
shared.  The key metaprogramming primitives are \AK{quote} and
\AK{unquote} operating as follows.
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
In \AF{ex}, the \AK{unquote} occurs in the \AC{true} clause of the function.
In this case the return type of the function normalises to \AD{ℕ}.
Therefore, the type of \AK{unquote} \AF{helper} must be \AB{ℕ} as well.
The argument to \AK{unquote} is expected to be a function of type \AD{Term} \AS{→}
\AD{TC} \AD{⊤}, where \AD{⊤} is the unit type.  Then the typechecking proceeds
as follows.  We create a metavariable \AB{hole} of type \AD{ℕ}; we quote it and
pass it to \AF{helper}.  Within the \AF{helper}, we assume that the
metavariable will be instantiated, and we replace the \AK{unquote} \AF{helper}
expression with \AB{hole}.  Instantiation in \AF{helper} is achieved by
the call to \AF{unify}.  This is one of the reflection API functions that
unifies two terms and solves the metavariables in the process.
Overall, the effect of \AK{unquote} \AF{helper} is identical to
just writing \AN{42}.  However, the expression inside the \AF{helper}
can be arbitrarily complex.

Instead of quoting/unquoting explicitly, we can use the \AK{macro}
keyword to wrap any function with return type \AD{Term} \AS{→}
\AD{TC} \AD{⊤}.  This takes care of quoting the arguments and unquoting
results.  On the right, we demonstrate how it can be used: \AF{getDef}
obtains the definition from the name.  The macro calls three functions
from the reflection API.  Firstly, \AF{getDefinition} obtains the definition
of the object with the name \AB{n}.  Secondly, \AF{quoteTC} quotes the
previously obtained definition (we get doubly-quoted definition).
Finally, we \AF{unify} the quoted hole and the doubly quoted definition,
so that after unquoting we get the reflected definition (and not the
original one).  We apply the macro in the last line, and as can be seen,
no quote/unquote is needed.

There are many other functions in the reflection API that are not essential
for the purposes of this paper.  However, all the details can be found
in the Reflection section of Agda's manual~\cite{agda}.


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
