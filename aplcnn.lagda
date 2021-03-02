\begin{code}[hide]
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Unit
open import Data.Fin using (Fin; zero; suc)
open import Data.List
open import Function
open import Reflection
module _ where
module APL where
  data Ix : (d : ℕ) → (s : Vec ℕ d) → Set where
    []   : Ix 0 []
    _∷_  : ∀ {d s x} → Fin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)

  record Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
    constructor imap
    field sel : Ix d s → X
\end{code}
\section{\label{sec:apl}APL and CNN}

In this section we consider the embedding of an
APL subset that is large enough to port the implementation~\cite{cnninapl}
of a convolutional neural network.  APL presents an interesting case
for our approach as it because it introduces the notions that are
difficult to express in Agda, and presumably any other existing theorem
prover.

APL is a language that pioneered the concept of rank- and shape-polymorphic
programming.  Expressions in APL are written in index-free combinator style
with a very few syntactic rules.  The language is dynamically typed, and
each combinator is an operation on (multi-dimensional) arrays.  Consider
the following (valid) APL expression:
\begin{flushleft}
  \qquad\apl{b ← 2 ÷⍨ (1 ⌽ a) + ¯1 ⌽ a}\qquad\qquad
  $b_i = \frac{1}{2}\left(a_{(i-1)\%n} + a_{(i+1)\%n}\right)$
\end{flushleft}
%
% where combinators are
% rank-polymorphic array operations.  As an example consider the following (valid) APL
% expression: {
% \aplfont
% \begin{verbatim}
%   2 ÷⍨ 1 ⌽ a + ¯1 ⌽ a
% \end{verbatim}
% }%
% %\noindent{}
that computes a two-point convolution of the array {\apl{a}} using cyclic
boundaries.  This is done by 
first rotating vectors along the last axis of {\apl{a}} one element to the
left ({\apl{¯1 ⌽ a}}), then one element to the right
({\apl{1 ⌽ a}}), then adding these results element-wise
({\apl{+}}), and then dividing each element by two ({\apl{2 ÷⍨}}).
The important point is
that this expression is applicable to \apl{a} of \emph{any} rank, including
zero-dimensional arrays.
Not only the initial set of APL combinators found very useful in practice,
but it also gives rise to the number of universal equalities such as:
\begin{flushleft}
\qquad\apl{(-x) ⌽ x ⌽ a ≡ a}
\end{flushleft}
It says: if we first rotate vectors in the last axis of \apl{a}
\apl{x} elements in one direction and then rotate by \apl{x}
elements in the opposite direction, we will always get back the same array.
These universal equalities are based on simple
arithmetic facts, yet they give a powerful reasoning technique and they can
be used as rewrite rules when programs are automatically transformed.


\subsection{Embedding}
Besides the compact notation, and a syntactic conventions that all the
operators are right-associative, semantics of each operator is heavily
overloaded.  This means that the same symbol has different meanings
depending on how many arguments are being passed and what these arguments
are, \ie{} their shapes, sign, \etc{}.  For example, consider the
\apl{\/} (slash) symbol, which can be used as:
\begin{table}[h!]
\begin{tabular}{ll}
  \apl{ +/a    } & sum array elements, \apl{+} is an argument   \\
  \apl{2+/a    } & sum in groups of 2, \apl{+} and \apl{2} are arguments \\
  \apl{ 2/a    } & replicate each element 2 times \\
  \apl{ +/[k]a } & sum over the $k$-th axis, \apl{[k]} is an optional axis specification
\end{tabular}
\end{table}
it can be seen, there are some optional arguments that can be omitted,
and the first argument can be either a binary operation or an integer.

While the embedding does not have to match the original syntax one-to-one,
we are willing to preserve one behaviour of the operators
that is used incredibly often --- the automatic cast between scalars,
vectors, and multi-dimensional arrays.  In APL every object is an
array, therefore vectors and scalars can be simply used as arguments
to the functions that expect arrays.  Shapes of arrays are 1-dimensional
arrays themselves.  Replicating such a behaviour in Agda would lead
to infinite recursion: we would have to index \AD{Ar} type with
\AD{Ar}, which is not possible.  Furthermore, binary operations
in APL have the following casting behaviour:
\begin{table}[h!]
\begin{tabular}{ll}
  \apl{1 2 3   + 1    } & computes to \apl{2 3 4} \\
  \apl{1       + 1 2 3} & computes to \apl{2 3 4} \\
  \apl{1 2 3   + 1 2 3} & computes to \apl{2 4 6} \\
  \apl{1 2 3 4 + 1 2 3} & runtime error
\end{tabular}
\end{table}
if one of the arguments to the binary operation is a singleton array,
it is automatically replicated to match the shape of the other element.

\paragraph{Overloading Saga}
Normally, overloading in Agda is solved by using instance arguments.
These are special kind of implicit arguments that are resolved using
an instance resolution algorithm.  This achieves a similar effect as
when using classes and instances in Haskell.  In our case, in order
to implement singleton replication, we would have to define relation
between the ranks and shapes of the arguments (and the result) of
the binary operation.  We start with a binary relation \AD{dy-args}
defined as follows:
\begin{code}
  data dy-args : ∀ m n → Vec ℕ m → Vec ℕ n → Set where
    n-n : ∀ {n s} → dy-args n n s  s
    n-0 : ∀ {n s} → dy-args n 0 s  []
    0-n : ∀ {n s} → dy-args 0 n [] s
\end{code}
These are specifications of valid argument array shapes to the binary
operation.  We either require the shapes to be identical, or one of
them can be a scalar (rank zero, shape empty).  One may hope that
by registering these constructors as instances, Agda would be able
to resolve the overloading automatically.  Unfortunately, it fails
to do so, in case two zero-dimensional arrays are supplied as arguments.
The problem is that in this case all three instances fit, but Agda
can only accept a unique solution.  Ironically, in this case, all
the three instances would lead to the same correct result.


It turns out that we can solve this problem by using metaprogramming.
This time round for the purposes of improving the specification.
We can define a macro that can be registered to resolve a given
hidden argument.  Within the macro, we are free to make arbitrary
choices in case of non-unique solutions.  Here is how we do this:
\begin{code}
  dy-args-dim : ∀ {m n sx sy} → dy-args m n sx sy → ℕ  -- pick the largest rank
  dy-args-shp : ∀ {m n sx sy} → (dy : dy-args m n sx sy) → Vec ℕ (dy-args-dim dy) 
  dy-args-ok? : Term → TC ⊤ -- macro that resolves the instances
\end{code}
\begin{code}[hide]
  dy-args-dim {m}    n-n = m
  dy-args-dim {m}    n-0 = m
  dy-args-dim {m}{n} 0-n = n

  dy-args-shp {m}{n}{sx}     n-n = sx
  dy-args-shp {m}{n}{sx}     n-0 = sx
  dy-args-shp {m}{n}{sx}{sy} 0-n = sy

  dy-args-ok? hole = do
    goal ← inferType hole
    def (quote dy-args) (vArg m ∷ vArg n ∷ vArg sx ∷ vArg sy ∷ []) ← reduce goal
      where _ → typeError (strErr "expected dy-args expression in goal, found:" ∷ termErr goal ∷ [])
    reduce m >>= λ where
      (lit (nat 0)) → unify hole (con (quote 0-n) [])
      (meta id _) → blockOnMeta id
      m → reduce n >>= λ where
        (lit (nat 0)) → unify hole (con (quote n-0) [])
        (meta id _) → blockOnMeta id
        n → do
          catchTC
            (unify m n)
            (typeError (strErr "no valid dy-args found for goal: " ∷ termErr goal ∷ []))
          unify hole (con (quote n-n) [])
\end{code}
\begin{code}
  dy-type : ∀ a → Set a → Set a
  dy-type a X = ∀ {m n sx sy} {@(tactic dy-args-ok?) args : dy-args m n sx sy}
                → Ar X m sx → Ar X n sy → Ar X _ (dy-args-shp args)

  lift′ : ∀ {a}{X : Set a} → (_⊕_ : X → X → X) → dy-type a X
  lift′ _⊕_ {args = n-n} (imap a) (imap b) = imap λ iv → a iv ⊕ b iv
  lift′ _⊕_ {args = n-0} (imap a) (imap b) = imap λ iv → a iv ⊕ b []
  lift′ _⊕_ {args = 0-n} (imap a) (imap b) = imap λ iv → a [] ⊕ b iv
\end{code}
We define the \AF{dy-args-dim} and \AF{dy-args-shp} to pick the largest
rank and shape from the arguments that are related by \AF{dy-args}.
Then we define a \AF{dy-args-ok?} macro that expects to be applied
in the context where the goal type is \AF{dy-args}.  It inspects the
arguments to \AF{dy-args}, and in case the first rank is zero it returns
\AC{0-n}, in case the second rank is zero it returns \AC{n-0} and if
two ranks are the same, it returns \AC{n-n}.  We 
use the \AK{tactic} keyword to register the decision procedure for
the hidden argument \AB{args}.  Finally, we define the \AF{lift′}
function that actually turns any binary operation on array elements
into a binary operation on arrays that replicates scalars correctly.
Here is how we demonstrate the lifting \AF{\_+\_} for natural numbers.
\begin{code}[hide]
  s : Vec ℕ 3
  s = 1 ∷ 2 ∷ 3 ∷ []
\end{code}

\begin{mathpar}
\codeblock{
\begin{code}
  _+_ = lift′ ℕ._+_
  a : Ar ℕ 3 s
  z : Ar ℕ 0 []
\end{code}
}
\and
\codeblock{
\begin{code}
  ex₁ ex₂ : Ar ℕ 3 s
  ex₁ = a + z
  ex₂ = a + a
\end{code}
}
\and
\codeblock{
\begin{code}
  ex₃ : Ar ℕ 0 []
  ex₃ = z + z
\end{code}
}
\and
\codeblock{
\begin{code}
  ex₄ ex₅ ex₆ : ∀ {n s}
      → Ar ℕ n s
      → Ar ℕ n s
\end{code}
}
\and
\codeblock{
\begin{code}
  ex₄ x = x + x
  ex₅ x = x + z
  ex₆ x = z + x
\end{code}
}
\end{mathpar}
\begin{code}[hide]
  a = imap λ iv → 10
  z = imap λ iv → 20
\end{code}
We define \AF{\_+\_} as lifted version of the addition on natural numbers.
Arrays with statically-known ranks are defined: \AF{a} is a 3-d array,
and \AF{z} is a scalar.  We can see that addition on arrays admit all the
desired variants.  The last three examples on the right show that it also
works for the cases when the rank is not known statically.




\begin{code}[hide]
  data SVup (X : Set) : Set → (d : ℕ) → (sh : Vec ℕ d) → Set where
    instance
      scal : SVup X X 0 []
      vect : ∀ {n} → SVup X (Vec X n) 1 (n ∷ [])
      arry : ∀ {d s} → SVup X (Ar X d s) d s

  cst : ∀ {a}{X : Set a}{d s} → X → Ar X d s
  cst x = imap λ _ → x

  infixr 30 ▴_
  ▴_ : ∀ {X A d s}{{t : SVup X A d s}} → A → Ar X d s
  ▴_ {{ t = scal }} a = cst a --imap λ _ → a
  ▴_ {{ t = vect }} a = imap λ where (i ∷ []) → V.lookup a i
  ▴_ {{ t = arry }} a = a

  infixr 30 ▾_
  ▾_ : ∀ {X A d s}{{t : SVup X A d s}} → Ar X d s → A
  ▾_ {{ t = scal }} (imap a) = a []
  ▾_ {{ t = vect }} (imap a) = V.tabulate λ i → a $ i ∷ []
  ▾_ {{ t = arry }} a = a

  data DyScalVec (X : Set) : Set → Set → (d : ℕ) → (sh : Vec ℕ d) → Set where
    instance
      s-s :           DyScalVec X X X 0 []
      s-v : ∀ {n} →   DyScalVec X X (Vec X n) 1 (n ∷ [])
      s-a : ∀ {d s} → DyScalVec X X (Ar X d s) d s
      v-s : ∀ {n} →   DyScalVec X (Vec X n) X 1 (n ∷ [])
      v-v : ∀ {n} →   DyScalVec X (Vec X n) (Vec X n) 1 (n ∷ [])
      a-s : ∀ {d s} → DyScalVec X (Ar X d s) X d s
      a-a : ∀ {m n sx sy}{@(tactic dy-args-ok?) args :
        dy-args m n sx sy} → DyScalVec X (Ar X m sx) (Ar X n sy) (dy-args-dim args) (dy-args-shp args)

  ▴ₗ : ∀ {X A B d s} {{t : DyScalVec X A B d s}} → A → Ar X d s
  ▴ₗ {{s-s}} a = cst a
  ▴ₗ {{s-v}} a = cst a
  ▴ₗ {{s-a}} a = cst a
  ▴ₗ {{v-s}} a = ▴ a
  ▴ₗ {{v-v}} a = ▴ a
  ▴ₗ {{a-s}} a = a
  ▴ₗ {{ t = a-a {args = n-n} }} a = a
  ▴ₗ {{ t = a-a {args = n-0} }} a = a
  ▴ₗ {{ t = a-a {args = 0-n} }} a = cst (Ar.sel a [])

  ▴ᵣ : ∀ {X A B d s} {{t : DyScalVec X A B d s}} → B → Ar X d s
  ▴ᵣ {{s-s}} b = cst b
  ▴ᵣ {{s-v}} b = ▴ b
  ▴ᵣ {{s-a}} b = b
  ▴ᵣ {{v-s}} b = cst b
  ▴ᵣ {{v-v}} b = ▴ b
  ▴ᵣ {{a-s}} b = cst b
  ▴ᵣ {{ t = a-a {args = n-n} }} b = b
  ▴ᵣ {{ t = a-a {args = n-0} }} b = cst (Ar.sel b [])
  ▴ᵣ {{ t = a-a {args = 0-n} }} b = b
  
  lift : ∀ {X A B d s}{{t : DyScalVec X A B d s}} → A → B → (_⊕_ : X → X → X) → Ar X d s
  lift {{ t }} a b _⊕_ = imap λ iv → Ar.sel (▴ₗ a) iv ⊕ Ar.sel (▴ᵣ b) iv

\end{code}

Notice that we have only presented the overloading between the \AD{Ar}
types of different shapes.  This still does not solve the problem of
implicit casts from base types such as \AD{ℕ} and vectors into arrays.
However, this can be solved by defining regular instances.  In the
code accompanying the paper, we define a similar \AD{lift} function
that extends the domain of the lifted binary operation and to accept
base types, vectors and arrays, and their combinations.

\subsection{CNN}
As an example of a practical application, we consider a convolutional
neural network for recognising hand-written digits.
The reference implementation we start from~\cite{cnninapl} is
written entirely in APL without relying on any external libraries
or frameworks. The implementation is very concise --- additionally
to built-in operators, it only requires to implement 10 new functions.
Each of these functions is a one line of APL code.  Our goal is to
translate these functions into our embedded array language.
This has two purposes.  First, we stress-test
abstractions used in our embedding and the extractor capabilities.
Second, we verify that all the shapes and ranks match, the indexing
is in-bound, no division by zero occurs, and that the functions are
terminating.  As APL is dynamically typed, it is difficult to be
sure that no runtime errors will occur.  Embedding the code into
Agda essentially requires us to define a type system for the operators
in use and guarantee that they hold.
We consider three representative examples of our encoding and explain
the details.

\begin{code}[hide]
module CNN where
  open import Array
  open import APL2
  open import Agda.Builtin.Float
  open import Data.Product hiding (_×_)
  postulate
    ⋯ : ∀ {a}{A : Set a} → A

  A<B⇒K<2⇒A*2+K<B*2 : ∀ {n s}{a b k : Ar ℕ n s} → a <a b → k <a (cst 2) → ((a × 2) + k) <a (b × 2)
  A<B⇒K<2⇒A*2+K<B*2 = ⋯

  _+ᵣ′_ = primFloatPlus

  -- Fuck you, unicode symbols!
  infixr 20 _¨_
  _¨_ = _̈_
\end{code}


\paragraph{Logistic function}
After the convolution and fully-connected layers in our CNN the
activation function is applied to each of the results.  The activation
function in use is called standard logistic and it is defined as:
\(
\frac{1}{1 - e^x}
\), and it is being applied to all the elements of the resulting
array.  Here is the implementation in APL and in our embedding:
\begin{code}
  -- logistic←{÷1+*-⍵}
  logistic : ∀ {n s} → Ar Float n s → Ar Float n s
  logistic ω = ÷ᵣ 1.0 +ᵣ *ᵣ -ᵣ ω
\end{code}
As it can be seen, the implementations are almost identical.
There are two important reasons for that: the ability to define the
precedence and the associativity of the operators; and the automatic
casts that we explained before.  All the operators in APL are
right-associative, which we implement as well.  We have chosen
to distinguish the operations on base types by adding a postfix
to the name.  That is why instead of \AF{\_+\_}, \AF{\_-\_}, \etc{}
we have \AF{\_+ᵣ\_}, \AF{\_-ᵣ\_} when we the arguments are arrays
of base type \AF{Float}.  If we read the body right to left, the
function negates (\AF{-ᵣ\_}) its argument, then it computes the
exponent (\AF{*ᵣ\_}) of that result, then it adds \AN{1.0} to all
the elements, and finally it takes a reciprocal (\AF{÷ᵣ\_}).  The
function is shape- and rank-polymorphic; it does not require additional
proofs and it normalises to a single \AC{imap}.

\paragraph{Mean Squared Error}
Generally, the nice behaviour of the above function is not surprising
because the function mapping scalar operations to individual array
elements.  However, this pattern is very common in array-based
applications.  Here is another example when we compute the mean
error which is a sum of squared elements divided by two:
% \begin{code}
%  -- backbias←{+/,⍵}
%  backbias : ∀ {n s} → Ar Float n s → Scal Float
%  backbias ω = _+ᵣ′_ / , ω
% \end{code}
\begin{code}
  -- meansqerr←{÷∘2+/,(⍺-⍵)*2}
  meansqerr : ∀ {n s} → Ar Float n s → Ar Float n s → Scal Float
  meansqerr α ω = _÷ᵣ 2.0 $ _+ᵣ′_ / , (α -ᵣ ω) ×ᵣ (α -ᵣ ω)
\end{code}
Here additionally to element-wise mapping we have a reduction of
the elements --- the \AF{\_/\_} operator.  On the right hand side
it gets an array that is being reduced, and the left operator is
a binary function that performs the actual operation.  We have a
flattened (\AF{,\_}) square of differences on the right, and
addition on \AD{Float}s on the left.  We need to flatten the
array on the right because \AF{\_/\_}, per APL semantics reduces
over the last axis of the array.  Also, in comparison to reductions
found in many functional languages, APL does not require the default
element.  Instead, it deduces the default element from the operation
in use.  We have encoded the same behaviour using instance resolution
mechanism.  However, we had to supply the addition on floats
\AF{\_+ᵣ′\_}, rather than our generalised addition on the arrays
and vectors of floats \AF{\_+ᵣ\_}.  This happens because otherwise
Agda fails to instantiate hidden arguments to \AF{\_+ᵣ\_}.  Finally,
partial application of division on the right \apl{÷∘2} is a built-in
feature of mix-fix operators in Agda.


\paragraph{Back Average Pool}
In the reverse average pooling function, we need to specify
a shape restriction.  The shape of the result must be twice
as big (in every element) as the shape of the input array.
\begin{code}
  -- backavgpool←{2⌿2/⍵÷4}⍤2
  backavgpool : ∀ {s} → Ar Float 2 s → Ar Float 2 $ ▾ (2 × s)
  backavgpool {s = _ ∷ _ ∷ []} ω = 2 ⌿ᵣ 2 /ᵣ′ ω ÷ᵣ 4.0
    where
      infixr 20 _/ᵣ′_
      _/ᵣ′_ = _/ᵣ_ {s = _ ∷ []}
\end{code}
We specify this relation using our lifted arithmetic operations:
\AN{2} \AF{×} \AB{s}, where the left argument is of type \AD{ℕ},
and the right argument is \AD{Vec} \AD{ℕ} \AN{2}.  The multiplication
returns a 1-dimensional array of type
\AD{Ar} \AD{ℕ} \AN{1} (\AN{2} \AF{∷} \AC{[]}), and we typecast it
back to \AD{Vec} using the \AF{▾\_} function.

The function itself divides all the array elements by \AN{4.0} and
replicates them two times across each row (\AF{\_/ᵣ\_}), and two
times across each column (\AF{\_⌿ᵣ\_}).  Notice that we had to
help Agda and specify that \AB{s} is guaranteed to be some vector
of two elements.  Also, similarly to the previous function, we
had to supply a hidden argument to \AF{\_/ᵣ\_}.  Notice that instead
of doing this inside the application chain, we used a \AK{where}
syntax to define a local variant of the row replicator \AF{\_/ᵣ′\_}.

\paragraph{Average Pooling}
Our final example is an average pooling function.  It gets a
two-dimensional array of floats as an argument, where each axis
is divisible by two.  It partitions the array into sub-arrays
of shape [2,2] and computes the average of each partition.
Here is how we implement this:
\begin{code}
  -- avg ← { (+/÷≢),⍵ }
  -- avgpool ← { (x y) ← ⍴⍵ ⋄ avg⍤2 ⊢ 0 2 1 3⍉(x÷2) 2 (y÷2) 2⍴ ⍵ }
  avgpool : ∀ {s} → Ar Float 2 $ ▾ (s × 2) → Ar Float 2 s
  avgpool {s} (imap p) = imap body
    where
      body : _ → _
      body iv = ▾ (_÷ᵣ 4.0 $ _+ᵣ′_ / , f ¨ ι [2,2])
        where
           [2,2] = cst {s = 2 ∷ []} 2
           f : _ → _
           f (i , pf) = let ix , ix<s = ix→a iv in
                        p $ a→ix ((ix × 2) + i) (s × 2) $ A<B⇒K<2⇒A*2+K<B*2 ix<s pf
\end{code}
It is interesting, that in this particular example, a direct
implementation that uses indexing is more straight-forward than
the one expressed in index-free style.  The result of average
pooling is given by the \AC{imap} where the index mapping is
given by the function called \AF{body}.  If we read the definition
of \AF{body} right to left: we obtain an array of indices (\AF{ι\_})
into a two-dimensional array of shape [2,2].  Note that \AF{[2,2]}
is just the identifier name.  Then for each element (\AF{\_¨\_})
in that array we apply a locally-defined function \AF{f}.  Then
we sum the elements up and divide them by \AN{4.0}.  The indices
returned by (\AF{ι\_}) are dependent pairs where the first component
is a 1-dimensional array representing the value of the index, and the
second component is a proof that the index is strictly less than the
array shape (in our case [2,2]).  In \AF{f}, we pattern-match
on the pair, and we compute selection into the argument of \AF{avgpool}
at index $2iv+i$.  When selecting at that index, we are required to
prove that it is within the bounds of the array.  This is done in
the last line of \AF{avgpool} where we had to prove a theorem that
this is indeed the case.


Here we consider an extracted \AF{avgpool} with some reformatting
for better readability.
\begin{lstlisting}[mathescape=false]
float[.,.] avgpool(int[2] x_1, float[.,.] x_3) {
  float[.,.] __ret;
  s = x_1;
  assert (shape (x_1)[0] == 2);
  assert (take (2, shape (x_3)) 
           == cons ((x_1[0] $* 2), cons ((x_1[1+0] $* 2), empty ([]))));

#define p(__x) (x_3)[__x]
  __ret = with {
    (.<= iv_1 <=.) {
       i = iv_1[0];
       j = iv_1[1+0];
    } : (   (p(cons(((i $* 2) $+ 0), cons(((j $* 2) $+ 0), []))) 
         $+ (p(cons(((i $* 2) $+ 0), cons(((j $* 2) $+ 1), []))) 
         $+ (p(cons(((i $* 2) $+ 1), cons(((j $* 2) $+ 0), [])))
         $+ (p(cons(((i $* 2) $+ 1), cons(((j $* 2) $+ 1), [])))
         $+ 0.0f))))
        $/ 4.0f);
  }: genarray (s, zero_float ([]));

  assert (take (2, shape (__ret)) == x_1);
  return __ret;
}
\end{lstlisting}
One of the important points of the extracted code is that all the
local definitions \AF{body} and \AF{f} were inlined, as well as
all the compound array operations.  We are very close to the code
that a programmer could write.  We start with assertions.  From
the type signature we deduce that the first argument must be a
two-element array, and the shape of the second argument is twice
the shape of the first argument.  We use arithmetic operations
prefixed with \$, to indicate that these are operations on scalars
(int and float) to help the compiler with instantiating overloadings.
At the end of the function, we generate an assertion that the shape
of the returned result must be equal to the first argument.
In the body of the \texttt{with}-loop we perform 4 selections
into the argument array and average them.  Notice how we define
a C preprocessor macro \AB{p}, so that we could use the
pattern-matched argument of the \AC{imap} as a function.
As SaC is first-order language, and the argument to
\AC{imap} is a function, we mimic the higher-order function
with the macro.  We are allowed to do this, because \AC{imap}
is the only supported construct that accepts a function as an
argument.

