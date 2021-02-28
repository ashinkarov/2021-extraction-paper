\section{\label{sec:array}Array Language}

In this section we switch to extraction of a different language
called SaC.  We explain essence of the language,
our embedding for it in Agda, and the difference in the
extraction process when comparing to Kaleidoscope.

\subsection{\sac{} --- Single Assignment C}
SaC is a first-order array language that looks like C syntactically,
but nonetheless
is purely functional.  The main idea of \sac{} is to provide
a framework to efficiently operate with multi-dimensional arrays.
All types in \sac{} represent arrays with potentially unknown ranks
(number of dimensions) and shapes (extents along dimensions).
Purely functional nature is achieved by ruling out
side-effecting expressions, undefined behaviour, pointers, and
other imperative constructions of C.  This allows the compiler
to use implicit memory management and to make decisions about
parallel execution of certain code parts without requiring
any explicit annotations.  We introduce the key aspects of
the language that will be used in extraction examples.  For
more information about SaC refer to~\cite{GrelSchoIJPP06,sactut}.

The main distinctive features of SaC is its hierarchy of array types,
intersection types and the unified data parallel array comprehensions.

\paragraph{Type System}
In SaC, functions can express rank-polymorphic computations.  That is
compute on arrays of arbitrary rank and shape.  The type system tracks
the information about shapes by using explicit attributes.  For example,
arrays where elements are integers and the shape is statically known
are expressed as:
\begin{lstlisting}
  int[] scal;         int[42] vec;         int[10,10,10] ten;
\end{lstlisting}
The shape of an array at runtime is always given by a tuple of natural
numbers.  In types, the shape attribute is an approximation of the
runtime value.  In the example above array \texttt{scal} is of rank
zero, and it represents a single element.  These arrays are often referred
as scalars in array theories.  The \texttt{vec} is 1-dimensional array
containing 42 elements, and \texttt{ten} is a 3-dimensional array of
shape $10\times10\times10$.

Arrays with static dimensions but without a static size can be specified
as:
\begin{lstlisting}
  int[.] a;         int[.,.] b;         int[.,.,.] c;
\end{lstlisting}
The dot can be thought of as a regular expression for a number.  Therefore
\texttt{a}, \texttt{b} and \texttt{c} are of ranks one two and three
correspondingly.  Finally, arrays can have a dynamic number of dimensions:
\begin{lstlisting}
  int[+] d;         int[*] e;
\end{lstlisting}
where plus means anything nonzero, and star means any shape.

These type attributes form a natural partial order:
\begin{lstlisting}
                       [ ]  $\le$  [*]
    [42]   $\le$  [.]    $\le$  [+]  $\le$  [*]
    [2,2]  $\le$  [.,.]  $\le$  [+]  $\le$  [*]
    ...
\end{lstlisting}
This shape hierarchy gives rise to function overloading.  The idea is
that a programmer may define a generic algorithm as well as a number of
special cases for certain chosen shapes.  By giving the same name, we
create an overloading, as long as instances
can be clearly disambiguated from the shapes of the arguments.  Moreover,
the compiler guarantees that that the most specific instance is always going
to be taken.  During the optimisation cycle the compiler creates instances
based on the uses of the overloading.

The design of the type system is driven by the user convenience.  As the
shape attributes are type-level objects, we can successfully run the type
inference.  The drawback however is that there is no way to express
complex shape relations in case of statically unknonwn shapes.  For example,
it would be useful to specify matrix multiplication as:
\begin{lstlisting}
  int[m,n] matmul (int[m,k], int[k,n])
\end{lstlisting}
Unfortunately, there is no notion of type-level varibales.  While this problem
can be fixed relatively easy, the functions like take or drop:
\begin{lstlisting}
  int[.] take(int n, int[.] v)  // take(2, [1,2,3,4]) == [1,2]
  int[.] drop(int n, int[.] v)  // drop(2, [1,2,3,4]) == [3,4]
\end{lstlisting}
would require some form of dependent types, which means that we would have
to give up global type inference.

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
    }: genarray ([m,n], 0);
  }
\end{lstlisting}
First, we obtain the number of rows and columns in the matrices by
querying their shape (which is a 1-dimensional array) and selecting
its corresponding components.  The outer with-loop specifies
the index range from $[0,0]$ up to $[m,n]$ and tells that all the
computed values should be put into the array of shape $m\times n$.
The latter is specified with \texttt{genarray} at the end of the
with-loop, where the first argument is the shape of the result,
and the second one is the default element.  The default element servers
two purposes: i) providing a value for the array indices that were
not specified in the index ranges; ii) provide the shape of each
element.  The latter is important because the computed elements
at each index may be arrays of non-empty shapes.  However, all
the element shapes must be the same, \eg{} vectors of length 5.
The shape of the result is a concatenation of the genarray
shape and the shape of the default element.  Back to matmul ---
the inner with-loop computes the sum of point-wise multiplied
$i$-th row and $j$-th column.  This is expressed with \texttt{fold},
where the first argument is a binary function, and the second
argument is the neutral element of the reduction.  Note that
the index in index ranges (and selections) is always a 1-dimensional
array.  In the example above we have pattern-matched its components
becuase the rank is statically known.  However, in general case we
can bind the index to a single variable.

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

In order to embed SaC, we have to define the type for multi-dimensional
arrays, and three constructs: with-loop, shape, and selection.  Our goal
is to specify them such that we can express non-trivial shape relations
between the arguments of a function and to ensure in-bound array indexing
statically.  Surprisingly, this can be achieved with the following types:
\begin{code}
  data Ix : (d : ℕ) → (s : Vec ℕ d) → Set where
    []   : Ix 0 []
    _∷_  : ∀ {d s x} → Fin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)

  record Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
    constructor imap
    field sel : Ix d s → X
\end{code}
The \AD{Ar} data type is indexed by the shape \AB{s} which is represented
as a \AD{Vec}tor of natural numbers.  The \AD{Ix} type is a type of valid
indices within the index-space generated by the shape \AD{s}.  The valid
index in such an index-space is a tuple of natural numbers that is component-wise
less than the shape \AB{s}.  Finally, the array with elements of type \AB{X}
is given by a function from valid indices to $X$.

In some sense \AD{Ar} and \AD{Ix} are second-order versions of \AD{Vec}
and \AD{Fin}.  This could be also thought of as a
computational interpretation of the Mathematics of Arrays~\cite{} (where $\Psi$
becomes an array constructor) or generalisation of pull arrays~\cite{pushpull}.

This encoding intrinsically guarantees that all the array accesses are within
bounds.  If we compare \AC{imap} and \texttt{genarray} \texttt{with}-loop,
the former does not allow to specify multiple partitions, as \AC{imap}
function is define over the entire range.  Instead we would
have to use a conditional within the \AC{imap} function.  While this might
have an impact on performance in some cases, it is significantly easier to
prove properties about \AC{imap}s than with-loops.  Also, almost all
our examples use the entire index space.  As for the \texttt{fold}
\texttt{with}-loop, we do not need a special construct.  We can define
a recursive function (analogous to reduce on \AD{Vec}) and extract
its application into the fold \texttt{fold} \texttt{with}-loop.

Consider now the matrix multiply example expressed in the embedded
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
As it can be seen, with a similar level of expressiveness, the
implementation encodes the correct shape relation between the arguments and
guarantees in-bound indexing without any explicit proofs.

\subsection{Argument Reconstruction}
The proposed \AC{Ar} type has a very satisfying property that
any composition of operations on arrays normalises to a single
imap.  Consider an example:
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
on the array elements.  The \AF{\_ᵀ} is a transpose.  Note that all
of these are defined in a rank-polymorphic style.  With transpose
we had to apply a proof (\AF{reverseinv}) that reverse of an
index is involutive.  The body of \AF{ex} is given as four
operations on the entire arrays, conceptually creating a new copy
of an array at every application.  Due to our encoding, the
the body of \AF{ex} normalises into a single \AC{imap}.

This is largely possible because we defined \AD{Ar} as a record,
and these are guaranteed to preserve $\eta$-equality.  That is,
every \AB{x} : \AD{Ar} \AB{d} \AB{s} is \emph{definitionaly} equal
to \AC{imap} (\AF{sel} x).  However, there is an unfortunate consequence.

As we extract \AC{imap} into a \texttt{genarray} with-loop, we have
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
the type-level arguments that we need are erased, as they can be
found in the type.  They are present in the type signature, and
in principle they could be inferred.  However, this far from
trivial as \AC{imap} may appear in arbitrary context.  Therefore
we would have to implement local type inference for an arbitrary
Agda term.

Instead, we extend the reflection API and implement type argument
reconstruction in the following pull request:
\url{https://github.com/agda/agda/pull/5022}.
We have added the following function:
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
\AF{reduce}, \etc{} to reconstruct the arguments that are currently
marked as unknonwn.  This is the biggest modification to Agda that
we had to do.  We use this interface when \AF{kompile} obtains the
representation of each definition.  For example getting a type signature
of some function \AF{f} looks like:
\begin{code}
  ty = withReconstructed $ dontReduceDefs base-funs $ normalise =<< getType f
\end{code}

\subsection{Validating Types}
One of the major difference between extracting into Kaleidoscope and
into SaC is the presence of the non-trivial type system in the latter.
This requires us to choose which Agda types are going to be supported
and how do we translate them into the target language.

SaC is lacking support for inhomogeneously nested arrays.  All the
elements in the array must be of the same shape.  Therefore, there
is no way to construct the following types:
\begin{lstlisting}
  (int[.])[5]       (int[.])[.]     (int[*])[.]    (int[*])[*]
\end{lstlisting}
Furthermore, syntactically, there is no way to express a homogeneously
nested array type.  However, one can deal with homogeneous nesting in
the following way.  Any homogeneous nesting can be flattened as follows:
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
\texttt{with}-loop that this array is generated with has a 1-dimensional
index-space (specified by the shape [6]), and non-scalar elements.
The latter is given by the shape of the default element, which is a
vector of 5 zeroes.  As a result we get an array of shape [6,5].

This suggests that nested \AC{imap}s can be mapped directly into
with-loops, translating nested array types in Agda into flattened
types in SaC.  However, while \AC{imap} is a constructor for \AD{Ar},
there is also an eliminator \AR{sel}.  Selecting into a nested array
would result in selection on a partial index.  That is:
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
we partially apply selection operation with \texttt{idx}.  Partial
selection is a well-known pattern and it is defined in the standard
library for all the supported base types such as int, float, \etc{}

Array shapes in Agda are represented with \AD{Vec} type, whereas
SaC shapes are 1-dimensional arrays.  Mapping a vector type is
straight-forward, as we only need to implement nil/cons to construct
vectors and head/tail to eliminate them:
\begin{lstlisting}
int[.] cons (int x, int[.] xs) {          int[.] tl (int[.] xs) {
  return with {                             return with {
    ([0] <= iv <= [0]): x;                    (. <= iv <= .): xs[iv+1];
    ([1] <= iv <= .): xs[iv - 1];           }: genarray (shape (xs) - 1); }
  }: genarray (1 + shape (xs));           
}                                         int hd (int[.] xs) { retunr xs[0]; }    
\end{lstlisting}
Finally, we notice that if can extract \AD{Vec}s, we can extract
\AD{List}s into exactly the same operations.  The difference would
be in the analysis of the nesting in the type.  \AD{Ar} of \AD{Vec}
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


\subsection{Exaample}

\todo[inline]{I'll explain the APL part first and then come back
  and see how much space I'll have for an example.  We are pretty
  low on space right now, so we may skip SaC example, and do
  APL ones.

  We can also think whether it is worth telling about
  dealing with lambdas as arguments to fold (lifting)
  and the macro trick in imap with lambdas.
}
