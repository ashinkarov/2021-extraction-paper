\section{\label{sec:related}Related Work}

\paragraph{Metaprogramming} There exists a very large body of
work that introduces metaprogramming facilities in a programming
language.  In~\cite{refl-masses} the authors track the origins
of the idea to Smith's work on reflection in lisp~\cite{refl-lisp}.
The paper introduces two systems: 2-lisp and 3-lisp.  The key difference
is that in the former may accessed the structure of the terms from
within the programs but the latter can also alter the way terms
are computed at runtime.  As lisp does not have static types,
the direct comparison is slightly difficult.  However, in some sense
we are closer to 3-lisp system within the dependent typechecker,
as we have an access to the elaborator and can trigger how the
typechecking proceeds.

These ideas developed were developed further introducing notions
such as reification~\cite{reification}, partial evaluation of
interpreters~\cite{futurama}, and modular staging~\cite{lms}.
Many systems are equipped with metaprogramming capabilities
based on the idea of \texttt{quote}/\texttt{unquote}:
MetaOcaml~\cite{metaocaml}, MetaMK~\cite{metaml},
reFlect~\cite{DBLP:journals/jfp/GrundyMO06} and many more.
However, very often the motivation of these systems is to generate
the new code, and not to trvaerse/modify the existing one.
In systems like Template Haskell~\cite{sheard2002template},
Racket~\cite{plt-tr1} or various lisp/scheme dialects, metaprograms
have full access to the existing parts of the program.

\paragraph{Embedding}
There exist various~\cite{10.5555/647849.737066,CHAPMAN200921,
10.1007/978-3-540-74464-1_7,10.1145/3236785,10.1145/1863495.1863497}
techniques on using dependent types for deep embedding.  While
the fact that this is possible is impressive, the resulting
encoding are difficult to use in practice.  On the other hand
deep embeddings force us to define semantics of the embedded
language therefore we can reason about its preservation when
transforming or optimising embedded programs.

In~\cite{deepshallow} this problem has been solved by proposing
a combination of deep and shallow embeddings.  The idea is to define
a small deep embedding and leverage classes in Haskell to define
the rest of the langauge on top of that.  It would be interesting
whether such an approach scales to dependently-typed embedded
languages.

%In~\cite{10.1145/2847538.2847541}
%TemplateHaskell is used to implement an embedded DSL Feldspar.


\paragraph{Extraction}
The Coq proof assistant is equipped with
extraction~\cite{10.1007/978-3-540-69407-6_39}
capabilites~\cite{10.1007/3-540-39185-1_12}, allowing to turn
a Coq proof (or program) into a functional language.  The default
backend is Ocaml, but a few other options were added recently.
The main difference from the approach that we are advocating in
this paper is that extractors are written as plugins to proof
assistant.  While it would be possible to implement extractors
presented in this paper as Coq plugins, conceptually they are
more heavyweight.  Our extractors and programs can (in principle)
communicate with each other.  As extractor is just an Agda
program it can be reflected an its structure can be leveraged.


\paragraph{Dependent Metaprogramming}
A number of dependently-typed languages have metaprogramming
capabilities: Idris~\cite{idris-refl}, Lean~\cite{lean-refl},
Coq~\cite{metacoq}, and Agda~\cite{agda-refl}.  All of the above
implement a similar API as described in this paper.  This is
reassuring, as the proposed approach is immediately portable
into many other contexts.
In~\cite{10.1145/3371071} the Turnstile+ dependent language
is introduced that focuses on embedding DSLs and very much
shares the ideas advocated in this paper, suggesting that
our approach could work there as well.
In~\cite{10.1145/3371076} authors use MetaCoq to formally verify
the core type system of Coq. This combines very nicely with
our approach, as we could use the verified core language
as a basis to verify our custom extractors.
In~\cite{10.1145/3372885.3373829} use MetaCoq to implement
a DSL combining deep and shallow approaches, and suggesting
a way to reason about preservation of semantics.  It is unclear
whether we could repeat the same for dependently-typed embeddings.

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
