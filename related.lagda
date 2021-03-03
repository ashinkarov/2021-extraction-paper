\section{\label{sec:related}Related Work}

\paragraph{Metaprogramming} There is a large body of
work on metaprogramming facilities in various programming
languages.  \citet{refl-masses} track the origins
of metaprogramming to Smith's work on reflection in Lisp~\cite{refl-lisp}.
%The paper introduces two systems: 2-lisp and 3-lisp.
%The former may access the structure of the terms from
%within a programs, while the latter can also alter the way terms
%are computed at runtime.  As Lisp is not compiled,
%a direct comparison with Agda is difficult. However, we can
%view the compile-time behaviour of Agda as a 3-lisp system,
%as we have an access to the elaborator and can trigger how the
%typechecking proceeds.
%
%Other work on metaprogramming includes notions
%such as reification~\cite{reification}, partial evaluation of
%interpreters~\cite{futurama}, and modular staging~\cite{lms}.
%
Some prominent metaprogramming systems include
MetaOcaml~\cite{metaocaml}, MetaML~\cite{metaml},
reFlect~\cite{DBLP:journals/jfp/GrundyMO06},
%However, often the main motivation of these systems is to generate
%new code, and not to travaerse or modify existing code.
Template Haskell~\cite{sheard2002template},
Racket~\cite{plt-tr1}, and various other Lisp/Scheme dialects.
%
However, these systems typically do not support dependent
types, so they are not well suited for our goal of statically
enforcing correctness of embedded programs.

\paragraph{Embedding}
Defining deep embeddings with static guarantees are a common application
of dependent types~\cite{10.5555/647849.737066,CHAPMAN200921,
10.1007/978-3-540-74464-1_7,10.1145/3236785,10.1145/1863495.1863497}.
%
These embeddings usually also define semantics of the embedded
language and therefore allow us to reason about the correctness
of program transformations and optimisations.
%
While the fact that this is possible is impressive in theory, the resulting
encodings are often difficult to use in practice. In this paper
we instead aim for a more lightweight approach.

\citet{deepshallow} propose to solve this problem with
a combination of deep and shallow embeddings.  Their idea is to define
a small deep embedding and leverage type classes in Haskell to define
the rest of the langauge on top of that.  It would be interesting to see
whether such an approach scales to dependently-typed embedded
languages.

%In~\cite{10.1145/2847538.2847541}
%TemplateHaskell is used to implement an embedded DSL Feldspar.


\paragraph{Extraction}
The Coq proof assistant is equipped with extraction
capabilites~\cite{10.1007/978-3-540-69407-6_39,10.1007/3-540-39185-1_12},
which extracts functional code from Coq proofs (or programs).  The
default target language is Ocaml, but a few other options were added
recently.
%
Likewise, Agda itself has a mechanism for defining custom backends, of
which the GHC backend is the most prominent.
%
Other proof assistants provide similar extraction tools as well.
%
The main difference from our approach in this paper
is that these extractors are written as a plugins to the proof
assistant, while we implement our extractors directly in the proof
assistant itself.
%
While it would be possible to implement extractors presented in this
paper as Coq plugins or Agda backends, conceptually they are more
heavyweight.  Our extractors and programs can (in principle)
communicate with each other. In addition, as they are just Agda programs, they can
be reflected themselves and their structure can be leveraged.


\paragraph{Dependently typed metaprogramming}
Several dependently-typed languages are equipped with metaprogramming
capabilities: Idris~\cite{idris-refl}, Lean~\cite{lean-refl},
Coq~\cite{metacoq}, and Agda~\cite{agda-refl}.  All of these
implement a similar API as described in this paper.  This is
reassuring, as it means our proposed approach is immediately portable
into many other contexts.
\citet{10.1145/3371071} introduce the Turnstile+ framework for
building dependently typed embedded DSLs and very much
shares the ideas advocated in this paper, suggesting that
our approach could work there as well.
\citet{10.1145/3371076} use MetaCoq to formally verify
the core type system of Coq. This combines very nicely with
our approach, as we could use the verified core language
as a basis to verify our custom extractors.
\citet{10.1145/3372885.3373829} use MetaCoq to implement
a DSL combining deep and shallow approaches, in a way that
is quite similar to our own. While they are able to formally
reason about preservation of semantics (which we can't do yet), it is unclear
whether their approach scales to dependently-typed embedded languages.

\paragraph{Arrays}
Using dependent types to verify properties of array programms
is not a novel idea.  For example, Qube~\cite{TROJAHNER2009643}
and Remora~\cite{10.1007/978-3-642-54833-8_3} are dependently
typed languages that are focused on array programming.  Both
of these focus on automating the type inference, which is a
big advantage for programmers.  However, one has to rely on
the capabilities of the inference engine, which may fail for
some complex examples.
In~\cite{10.1007/978-3-642-41582-1_11} authors use Agda as
a frontend for Accelerate which is an array library in Haskell.
The motivation of the work is similar to ours, to provide static
guarantees about array computations.  As the target language of
this work is Haskell, and Agda provides a backend for it,
the integration happens very smoothly without requiring
any extraction techniques.


%
% \begin{enumerate}
% \item Chapman, McBride, etc, on deep embedding within dependently-typed
%   languages
% \item Deep-shallow embedding; subformulas
% \item Metaprogramming, MetaOcaml
% \item Template metaprogramming?
% \end{enumerate}
%
%
% \todo[inline]{We should probably get rid of the text below
%   for the sake of space saving.}
%
% In a dependently-typed language such restrictions can be achieved by
% constructing a universe.  The strength of restrictions presents us an
% entire spectrum ranging from weak to strong.  Let us demonstrate a
% universe that restricts function types.
% \begin{code}[hide]
% module _ where
% module Univ where
%   --open Problem
%   open import Data.Nat
%   open import Data.Fin using (Fin; zero; suc)
%   open import Relation.Binary.PropositionalEquality
%   open import Data.Product
%   open import Data.Nat.DivMod
%   open import Data.Nat.Show renaming (show to showNat)
%   open import Data.String using (length)
%   open import Data.Bool hiding (_<_)
%   open import Function
%
%   postulate
%     ⋯ : ∀ {a}{A : Set a} → A
% \end{code}
% \begin{mathpar}
% \codeblock{%
% \begin{code}
%   data Ty : Set ; ⟦_⟧ : Ty → Set
%   data Ty where
%     nat   : Ty
%     fin   : ⟦ nat ⟧ → Ty
%     eq lt : (a b : ⟦ nat ⟧) → Ty
%
%   ⟦ nat ⟧    = ℕ
%   ⟦ fin x ⟧  = Fin x
%   ⟦ eq a b ⟧ = a ≡ b
%   ⟦ lt a b ⟧ = a < b
% \end{code}
% }
% \and
% \codeblock{%
% \begin{code}
%   data n-σ : Set where
%     ⟨_⟩   : Ty → n-σ
%     _▹_ : (τ : Ty) → (⟦ τ ⟧ → n-σ) → n-σ
%
%   I : n-σ → Set
%   I ⟨ τ ⟩   = ⟦ τ ⟧
%   I (τ ▹ P) = (t : ⟦ τ ⟧) → I (P t)
%
%   ex₁ : I $ nat ▹ λ m → nat ▹ λ n → lt m n ▹ λ m<n → ⟨ fin n ⟩
% \end{code}
% }
% \end{mathpar}
% \begin{code}[hide]
%   ex₁ = ⋯
% \end{code}
% We first define a universe of base types \AD{Ty} and its interpretation
% \AD{⟦\_⟧}.  Then we define a universe of $n$-fold dependent tuples of
% \AD{Ty}s, (a tuple where elements on the right may depend on all the
% previous elements) and its interpretation \AF{I} into dependent function
% space.
%
% Given that \AD{n-σ} contains only interpretations of valid types, it
% might seem that functions of type \AD{I e} guarantee correct extraction.
% Unfortunately it does not.  We still have the problem demonstrated in \AF{ex}
% example --- the terms are not restricted enough.  More importantly,
% as types may depend on terms we can write:
% \begin{code}
%   ex₂ : I $ nat ▹ λ n → ⟨ fin $ length $ showNat n ⟩ ; ex₂ = ⋯
%   ex₃ : I $ nat ▹ λ n → if n % 2 ≡ᵇ 0 then ⟨ nat ⟩ else ⟨ lt n 42 ⟩ ; ex₃ = ⋯
% \end{code}
% The argument to \AC{fin} is an unrestricted term, therefore we can write
% \AC{fin} \AF{ex} \AB{n} in \AF{ex₂}. The \AC{\_▹\_} constructor of \AD{n-σ} uses
% unrestricted lambdas to bind variables, therefore \AF{ex₃}.
%
% Many approaches show~\cite{} how further restrictions can be added to the
% terms, which essentially brings forces us to define deep embedding.  The
% problem with these approaches is that the encoding becomes very non-trivial
% to use.  The essence of the problem is that in order to solve \AD{ex₃} problem
% we need to handle variables explicitly.  This means that we have to parametrise
% our types and terms by contexts.  Approaches such as~\cite{} require explicit
% weakening, substitution and type equality as a part of the embedded language
% encoding.  McBride's work on Kipling~\cite{} shows how one could avoid some
% of these artefacts, but the resulting embedding is still very non-trivial to
% use.  Most importantly, in both cases, any existing Agda code
% such as properties about data types that we can find in the standard library
% will have to be internalised in the embedding.
