\section{\label{sec:array}Array Language}

In this section we switch to extraction of a different language
called Single Assignment C --- \sac{} for short.  We explain essence of the language,
our embedding for it in Agda, and the difference in the
extraction process when comparing to Kaleidoscope.

\subsection{\sac{} --- Single Assignment C}
\sac{} is a first-order array language that looks like C syntactically,
but nonetheless
is purely functional.  The main goal of \sac{} is to provide
a framework to efficiently operate with multi-dimensional arrays.
All types in \sac{} represent arrays with potentially unknown ranks
(number of dimensions) and shapes (extents along dimensions).
Its purely functional nature is achieved by ruling out
expressions that have side effects, undefined behaviour, pointers, and
other imperative constructions of C.  This allows the compiler
to use implicit memory management and to make decisions about
parallel execution of certain code parts without requiring
any explicit annotations.  The current compiler \texttt{sac2c}
supports efficient~\cite{sac-nbody} compilation to multicore and GPU
architectures.  We introduce the key aspects of
the language that will be used in extraction examples.  For
more information about SaC refer to~\cite{GrelSchoIJPP06}.

\paragraph{Type system}
The main distinctive features of SaC are its hierarchy of array types,
intersection types and the unified data-parallel array comprehensions.
In SaC, functions express rank-polymorphic computations.  That is, they
compute on arrays of arbitrary rank and shape.  The type system tracks
information about shapes by using explicit attributes.  For example,
arrays where elements are integers and the shape is statically known
are expressed as:
\begin{lstlisting}
  int[] scal;         int[42] vec;         int[10,10,10] ten;
\end{lstlisting}
The shape of an array at runtime is always given by a tuple of natural
numbers.  In types, the shape attribute is an approximation of the
runtime value.  In the example above array \texttt{scal} is of rank
zero, representing a scalar value. The \texttt{vec} is a 1-dimensional array
containing 42 elements, and \texttt{ten} is a 3-dimensional array of
shape $10\times10\times10$.

Arrays with static dimensions but without a static size can be specified
using a dot \texttt{.}:
\begin{lstlisting}
  int[.] a;         int[.,.] b;         int[.,.,.] c;
\end{lstlisting}
The variables \texttt{a}, \texttt{b} and \texttt{c} are of ranks one,
two, and three respectively, with unknown shapes.
Finally, arrays can have a dynamic number of dimensions:
\begin{lstlisting}
  int[+] d;         int[*] e;
\end{lstlisting}
where \texttt{d} is an array of rank 1 or higher, and \texttt{e} is an array of any rank.

There is a natural partial order on type attributes according to the
precision with which they describe the rank and dimensions of an array:
\begin{lstlisting}
  [] $\le$ [*]      [42] $\le$ [.] $\le$ [+] $\le$ [*]     [2,2] $\le$ [.,.] $\le$ [+] $\le$ [*]
\end{lstlisting}
This shape hierarchy gives rise to function overloading based on the
shape of the arguments, where the compiler will pick the most specific
instance in case of overlap.
% During the optimisation cycle the compiler creates instances
% based on the uses of the overloading.

A limitation of \sac{} is that there is no way to express
complex shape relations in case of statically unknown shapes.  For example,
it would be useful to specify matrix multiplication as:
\begin{lstlisting}
  int[m,n] matmul (int[m,k], int[k,n])
\end{lstlisting}
Unfortunately, this cannot be expressed as there is no notion of type-level varibales.
%
This becomes even more problematic for functions like \texttt{take} or \texttt{drop} below:
\begin{lstlisting}
  int[.] take(int n, int[.] v)  // take(2, [1,2,3,4]) == [1,2]
  int[.] drop(int n, int[.] v)  // drop(2, [1,2,3,4]) == [3,4]
\end{lstlisting}
%
Annotating them with a precise size would require some form of
dependent types, which means that we would have to give up global type
inference.

The key language construct in SaC is the \texttt{with}-loop --- a
data-parallel array comprehension construct.  The programmer
specifies how index sets are to be mapped into element values
and whether the computed values form an array or are folded
into a single value.  This could be also thought of as a generalised
map/reduce construct.  Consider an example of matrix multiplication:
\begin{lstlisting}
  int[.,.] matmul (int[.,.] a, int[.,.] b) {
    M = shape(a)[0]; K = shape(a)[1]; N = shape(b)[1];
    return with {
      ([0,0] <= [i,j] < [M,N]): sum (with {
         ([0] <= [k] < [K]): a[[i,k]]*b[[k,j]];
      }: fold (+, 0);
    }: genarray ([M,N], 0);
  }
\end{lstlisting}
First, we obtain the number of rows and columns in the matrices by
querying their shape (which is a 1-dimensional array) and selecting
its corresponding components.  The outer with-loop specifies
the index range from $[0,0]$ up to $[M,N]$ and tells that all the
computed values should be put into the array of shape $M\times N$.
The latter is specified with \texttt{genarray} at the end of the
with-loop, where the first argument is the shape of the result,
and the second one is the default element.  The default element serves
two purposes: i) providing a value for the array indices that were
not specified in the index ranges; ii) providing the shape of each
element.  The latter is important because the computed elements
must all have the same shape.
The shape of the result is a concatenation of the \texttt{genarray}
shape and the shape of the default element.
The inner with-loop computes the sum of point-wise multiplied
$i$-th row and $j$-th column, expressed by \texttt{fold (+, 0)}.
%Note that
%the index in index ranges (and selections) is always a 1-dimensional
%array.  In the example above we have pattern-matched its components
%becuase the rank is statically known.  However, in general case we
%can bind the index to a single variable.
%
For more details on programming in SaC refer to~\cite{GrelckCEFP11}.


\subsection{Embedded Array Language}
\begin{code}[hide]
postulate
  ⋯ : ∀ {a}{A : Set a} → A
module _ where
module ArType where
  open import Data.Vec using (Vec; []; _∷_)
  open import Data.Nat
  open import Data.Fin
  open import Function
  infixr 5 _∷_
\end{code}

In order to embed SaC, we have to define a type of multi-dimensional
arrays, and three constructs: with-loops, shapes, and selections.  Our goal
is to express non-trivial shape relations
between the arguments of a function and to ensure in-bound array indexing
statically.  We achieve this with the following two Agda types:
\begin{code}
  data Ix : (d : ℕ) → (s : Vec ℕ d) → Set where
    []   : Ix 0 []
    _∷_  : ∀ {d s x} → Fin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)

  record Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
    constructor imap
    field sel : Ix d s → X
\end{code}
Both types are indexed by a shape \AB{s}, represented
as a \AD{Vec}tor of natural numbers.  The \AD{Ix} type is a type of valid
indices within the index-space generated by the shape \AD{s}.  The valid
index in such an index-space is a tuple of natural numbers that is component-wise
less than the shape \AB{s}.  Finally, the array with elements of type \AB{X}
is given by a function from valid indices to $X$.
%
In some sense \AD{Ar} and \AD{Ix} are second-order versions of \AD{Vec}
and \AD{Fin}.  This could be also thought of as a
computational interpretation of the Mathematics of Arrays~\cite{LMRMullin:moa}
(where $\Psi$ becomes an array constructor), or as a generalisation of
pull arrays~\cite{pushpull}.

This encoding intrinsically guarantees that all the array accesses are within
bounds.
%If we compare \AC{imap} and the \texttt{genarray} \texttt{with}-loop,
%the former does not allow to specify multiple partitions, as the \AC{imap}
%function must be defined over the entire range.  Instead, we would
%have to use a conditional within the \AC{imap} function to express a partition.  While this might
%have an impact on performance in some cases, it is significantly easier to
%prove properties about \AC{imap}s than with-loops.  Also, almost all
%our examples use the index space uniformly, so there is no need for conditionals.
As for \texttt{fold}
\texttt{with}-loops, there is no need for a special construct:
we can define
a recursive function (analogous to reduce on \AD{Vec}), and let the extractor
translate it into the corresponding fold \texttt{fold} \texttt{with}-loop.

Consider now the matrix multiplication example expressed in the embedded
language:
\begin{code}[hide]
  open Ar public
  private
   postulate
    sum : ∀ {n}  → Ar ℕ 1 (n ∷ []) → ℕ
\end{code}
\begin{code}
  mm : ∀ {a b c} → let Mat x y = Ar ℕ 2 (x ∷ y ∷ []) in Mat a b → Mat b c → Mat a c
  mm (imap a) (imap b) = imap body where
     body : _
     body (i ∷ j ∷ []) = sum $ imap λ where (k ∷ []) → a (i ∷ k ∷ []) * b (k ∷ j ∷ [])
\end{code}
With a similar level of expressiveness, the
implementation encodes the correct shape relation between the arguments and
guarantees in-bound indexing without any explicit proofs.

Our definition of \AD{Ar} satisfies the very useful property that
any composition of operations on arrays normalises to a single
\AC{imap}.  Consider an example:
\begin{code}[hide]
module ExFuse where
  open ArType
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open import Data.Vec using (Vec; [];  _∷_; reverse; _++_; splitAt)
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat.Properties
  open import Data.Product
  open import Reflection
  open import Data.List using (List; []; _∷_)
  open import Function using (_$_)
  open import Data.Fin using (Fin; zero; suc)
  infixl 7 _*_
  infixl 6 _+_
  postulate
    sum : ∀ {d s} → Ar ℕ d s → ℕ
    reverse-inv : ∀ {X : Set}{n} (xs : Vec X n) → reverse (reverse xs) ≡ xs
    ix-reverse : ∀ {d s} → Ix d s → Ix d (reverse s)
\end{code}
\begin{code}
  _*_ _+_ : ∀ {d s} → (a b : Ar ℕ d s) → Ar ℕ d s
  _+_ a b = imap λ iv → sel a iv ℕ.+ sel b iv
  _*_ a b = imap λ iv → sel a iv ℕ.* sel b iv

  _ᵀ : ∀ {X : Set}{d s} → Ar X d s → Ar X d (reverse s)
  _ᵀ a = imap λ iv → sel a (subst (Ix _) (reverse-inv _) (ix-reverse iv))

  ex : ∀ {m n} → Ar ℕ 2 (n ∷ m ∷ []) → Ar ℕ 2 (m ∷ n ∷ []) → Ar ℕ 2 (m ∷ n ∷ [])
  ex a b = a ᵀ + (b * b)
\end{code}
Here we defined \AF{\_+\_} and \AF{\_*\_} as element-wise operations
on the array elements.  The \AF{\_ᵀ} is a transposition of the matrix,
which reverses the order of the dimensions.  Note that all
of these are defined in a rank-polymorphic style.  For transposition
we had to apply a proof (\AF{reverse-inv}) that reversing an
index is involutive.  The body of \AF{ex} is given as four
operations on the entire arrays, conceptually creating a new copy
of an array at every application.  Due to our encoding, the
the body of \AF{ex} normalises into a single \AC{imap}.
%
This is largely possible because we defined \AD{Ar} as a record,
and these are guaranteed to preserve $\eta$-equality.  That is,
every \AB{x} : \AD{Ar} \AB{d} \AB{s} is \emph{definitionaly} equal
to \AC{imap} (\AR{sel} x).

During the implementation of our extractor for \sac{} in Agda, we
encountered an unexpected challenge related to the definition of
\AD{Ar}.  By defining it as a record type, the elaborator of Agda
decides to erase the (implicit) arguments $a$, $X$, $d$, and $s$ of
the constructor \AC{imap}, replacing them by the constructor
\AC{unknown} in the reflected syntax.
%
The reason why Agda does this is because these parameters can always
be reconstructed from the type of the array.
%
However, inferring them is far from trivial as \AC{imap} may appear in
arbitrary contexts.
%
To work around this issue, we extended the reflection API of Agda with
a new primitive \AF{withReconstructed} that instructs all the further
calls to \AF{getDefinition}, \AF{normalise}, \AF{reduce}, \etc{} to
reconstruct the arguments that are normally marked as \AC{unknown}.
We use this function when \AF{kompile} obtains the representation of
each definition. For more details on this new feature, see \url{https://github.com/agda/agda/pull/5022}.

\begin{comment}

\subsection{Argument Reconstruction}
However, using a record type for \AD{Ar} posed an unexpected challenge.
%
As our extractor translates \AC{imap} to a \texttt{genarray} with-loop, it has
to supply the shape of the resulting array.  In our encoding, this is
a type-level value (the last argument of \AD{Ar}) which is not stored
in the internal representation of the record value.  For example, consider
the following function and its reflected body:
\begin{mathpar}
\codeblock{
\begin{code}
  const : ℕ → Ar ℕ _ (5 ∷ 5 ∷ [])
  const n = imap λ x → n
\end{code}
}
\and
\codeblock{
\begin{code}
  `const-b = (con (quote imap)
      (hArg unknown ∷ hArg unknown ∷
       hArg unknown ∷ hArg unknown ∷
        vArg (lam visible (abs "x" (var 1 [])))
       ∷ []))
\end{code}
}
\end{mathpar}
The (hidden) type-level arguments to \AC{imap} that we need are erased by Agda, as they can be
found in the type.  They are present in the type signature, and
in principle they could be inferred.  However, this far from
trivial as \AC{imap} may appear in arbitrary contexts.  Therefore,
we would have to implement local type inference for an arbitrary
Agda term.

Instead, we decided to extend the reflection API and implement type argument
reconstruction in the following pull request:
\url{https://github.com/agda/agda/pull/5022}.
In particular, we have added the following primitive function:
\begin{code}
  withReconstructed : ∀ {a} {A : Set a} → TC A → TC A
\end{code}
\begin{code}[hide]
  withReconstructed = ⋯
  infixr 1 _=<<_
  _=<<_ : ∀ {A B : Set} → (A → TC B) → TC A → TC B
  _=<<_ = ⋯
  postulate
    f : Name
    base-funs : Names
    dontReduceDefs : ∀ {a} {A : Set a} → Names → TC A → TC A
\end{code}
that instructs all the further calls to \AF{getDefinition}, \AF{normalise},
\AF{reduce}, \etc{} to reconstruct the arguments that are normally
marked as \AC{unknown}.  This is the biggest modification to Agda that
we had to do.  We use this function when \AF{kompile} obtains the
representation of each definition.  For example, getting the type signature
of some function \AF{f} looks like:
\begin{code}
  ty = withReconstructed $ dontReduceDefs base-funs $ normalise =<< getType f
\end{code}
\end{comment}

\subsection{Validating Types}
One of the major differences between extracting into Kaleidoscope and
into SaC is the presence of the non-trivial type system in the latter.
This requires us to choose which Agda types are going to be supported
and how to translate them into the target language.

SaC lacks support for heterogeneously nested arrays: all the
elements in the array must be of the same shape.  Therefore, there
is no way to construct the following types:
\begin{lstlisting}
  (int[.])[5]       (int[.])[.]     (int[*])[.]    (int[*])[*]
\end{lstlisting}
Furthermore, syntactically, there is no way to express a nested array
type.  However, one can deal with homogeneous nesting by flattening as
follows:
\begin{lstlisting}
  (int[5])[6] => int[6,5]        (int[$\tau$])[$\sigma$] => int([$\sigma$] ++ [$\tau$])
\end{lstlisting}
Also, the \texttt{with}-loop construct makes it possible to express
the computation in a nested style, but the resulting array type will
be flattened according to the scheme above.   Consider an example:
\begin{lstlisting}
  int[5] foo (int[1]);  // some function that produces 5-element vectors.
  int[6] gen (int[6,5] a) {
    return with {
      ([0] <= iv < [6]): foo (iv);
    }: genarray ([6], with{}: genarray ([5], 0));
  }
\end{lstlisting}
The function \texttt{gen} computes a two-dimensional array.  The
\texttt{with}-loop that this array generates has a 1-dimensional
index-space (specified by the shape [6]), and non-scalar elements.
The latter is given by the shape of the default element, which is a
vector of 5 zeroes.  As a result we get an array of shape [6,5].

This suggests that nested \AC{imap}s can be mapped directly to
with-loops, translating nested array types in Agda into flattened
types in SaC.  However, while \AC{imap} is a constructor for \AD{Ar},
there is also the projection \AR{sel}.  Selecting into a nested array
would result in selection on a partial index:
\begin{code}
  partial-sel : Ar (Ar ℕ 1 (5 ∷ [])) 1 (6 ∷ []) → Ar ℕ 1 (5 ∷ [])
  partial-sel x = sel x (zero ∷ [])
  -- int[5] partial_sel (int[5,6] a) { return ?? }
\end{code}
The argument to \AF{partial-sel} is a nested array of shape [6],
with inner elements of shape [5].  We can represent it in SaC as
an array of shape [5,6].  Selections into such an array require
two-element indices, but in the above code, selection happens on
a 1-element index.  Fortunately, we can generalise SaC selections
as follows:
\begin{lstlisting}
  int[*] sel(int[.] idx, int[*] a) {
    sh_inner = drop (shape (idx), shape (a));
    return with {
      (0*sh_inner <= iv < sh_inner): a[idx ++ iv];
    }: genarray (sh_inner, 0);
  }
\end{lstlisting}
When selecting an array \texttt{a} at index \texttt{idx},
the shape of the result is computed by dropping
\texttt{idx}-many elements from the shape of the argument.  The
content of the result is given by a mapping \texttt{iv} $\mapsto$
\texttt{a}[\texttt{idx} \texttt{++} \texttt{iv}], where \texttt{iv}
iterates over the index space of the resulting array.  Essentially,
we partially apply the selection operation to \texttt{idx}.  Partial
selection is a well-known pattern and it is defined in the standard
library for all the supported base types such as int, float, \etc{}

Array shapes in Agda are represented by the \AD{Vec} type, whereas
SaC shapes are 1-dimensional arrays.  Mapping a vector type is
straight-forward, as we only need to implement nil/cons to construct
vectors and head/tail to eliminate them\footnote{Here we show
  1-dimensional versions of the functions, but in reality we
  implement rank-polymorphic cons/hd/tail using the idea
  similar to \texttt{sel} from above.}:
\begin{lstlisting}
int[.] cons (int x, int[.] xs) {          int[.] tl (int[.] xs) {
  return with {                             return with {
    ([0] <= iv <= [0]): x;                    (. <= iv <= .): xs[iv+1];
    ([1] <= iv <= .): xs[iv - 1];           }: genarray (shape (xs) - 1); }
  }: genarray (1 + shape (xs));
}                                         int hd (int[.] xs) { retunr xs[0]; }
\end{lstlisting}
Finally, we notice that if we can extract \AD{Vec}s, we can extract
\AD{List}s into exactly the same target language constructs.
The difference would
be in the analysis of the nesting of the type.  \AD{Ar} of \AD{Vec}
and \AD{Vec} of \AD{Ar} are always homogeneous as long as the leaf
element is some base type like \AD{ℕ}.  \AD{List}s of base types
or lists of homogeneous arrays are also homogeneous.  However, whenever
\AD{List} shows up on any inner level of the nesting, we loose
homogeneity, \eg{} \AD{List}\AF{∘}\AD{List} is inhomogeneous, because
the inner elements may be of different sizes.  We implement this analysis
in the extractor, therefore allowing for the combination of nested
\AD{Ar}, \AD{Vec} and \AD{List} over the base types \AD{ℕ} and \AD{Float}.

% \begin{lstlisting}
%  (τ[*])[.,.,.]   → τ([.,.,.] ++ [*])   = τ[*]
%  (τ[.,.])[.,.,.] → τ([.,.,.] ++ [.,.]) = τ[.,.,., .,.]
%  (τ[5,6])[.,.,.] → τ([.,.,.] ++ [5,6]) = τ[.,.,., .,.]
%  (τ[*])[5,6]     → τ([5,6] ++ [*]) = τ[*]
%  (τ[.,.])[5,6]   → τ([5,6] ++ [.,.]) = τ[.,.,.,.]
%  (τ[7,8])[5,6]   → τ([5,6] ++ [7,8]) = τ[5,6,7,8]
% \end{lstlisting}

\begin{comment}
\subsection{Example}

\todo[inline]{I'll explain the APL part first and then come back
  and see how much space I'll have for an example.  We are pretty
  low on space right now, so we may skip SaC example, and do
  APL ones.

  We can also think whether it is worth telling about
  dealing with lambdas as arguments to fold (lifting)
  and the macro trick in imap with lambdas.
}
\end{comment}
