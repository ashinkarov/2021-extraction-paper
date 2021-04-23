# Structure of the response

We would like to thank all the reviewers for their time and helpful comments!
We structure our response in two parts.  First, we address common concerns raised
by multiple reviewers; after that, we respond to the remaining individual
comments and questions.


# Part1: Common concerns

## The main goal of the paper as we see it

The main point of the paper is to demonstrate that it is possible to define
a practically usable *dependently-typed DSL* without the necessity to
implement a typechecker, as you share one with Agda.  Extraction gives
us a way to define an arbitrary target language that we translate our DSL
for further execution.  Two practical scenarios are possible: 1) I have a
(dep.typed) DSL and I want to translate it to target X; or 2) I have a
a language X which I would like to extend with dependent types.  Both
scenarios are possible with the presented work, and to our knowledge
this was not tried before.

## General principles and correctness

As our main focus is to provide all the means to write an extractor,
the question of correctness (in some sense) is orthogonal ---
one is free to make it as correct or incorrect as one pleases.

So far we can state that, as long as you trust that Agda type system
is sound:
  1. an embedded language has a sound type system (as it is a subset
     of Agda);
  2. programs in the embedded languages have expected properties
     of progress and preservation (as they can be executed within Agda)
  3. given that the extractor preserves the dynamic semantics of Agda:
     - static semantics is encoded using assertions;
     - if an entire program is extracted from Agda, these assertions
       shall never be triggered at runtime;
     - when extracting partial programs, assertions can only fire at
       the boundaries with unsafe code.

Ideally, we would want to write a theorem in Agda that the given
extractor preserves the semantics.  For that one needs to relate the
semantics of reflected terms with the semantics of the language we
are extracting to.  Unfortunately, at the time of writing there is
no official semantics for Agda reflected terms.  While in principle
it is possible to come up with one manually, we believe that reflection
system should give us the one we could actually trust.  This is our
future work.

## Shallow embedding and its semantics

One challenge with a shallowly embedded language is how to formally define
which terms of the host language actually form the embedding.  While we do
not have any syntactical means to do so, as we state in line 315, any Agda
term that is recognised by the extractor is considered to be the part of
the embedded language.  In that sense, semantics of the embedding is always
given by the semantics of Agda, and the language itself is defined by the
extractor.

## Pull Requests inclusion in the paper

We consider the changes that we made to Agda essential to the work that we
present in the paper.  As our approach has not been tried before, obviously
some required functionality is lacking, so we fixed it.  As for inclusion
in the paper, unfortunately we didn't find a better way of presenting these,
and according to our read of the definition of "lightweight double-blind"
inclusion of the links seem to be acceptable as we do not expose our names
or institutions, and as the work has been done specifically for this paper
we did not have to address it in third person.

We summarise the changes that we did to Agda's reflection system:
  - allow accessing the actual typing context (telescope) of the given term;
  - selective reduction and normalisation of the terms;
  - access typing information of the implicit arguments after normalisation
    -- the most challenging change.


# Part2: Remaining concerns

-- XXX stopped here XXX ---


ICFP 2021 Paper #150 Reviews and Comments
===========================================================================
Paper #150 Choosing is Losing: How to combine the benefits of shallow and
deep embeddings through reflection


Review #150A
===========================================================================

Overall merit
-------------
C. I would not accept this paper but will not argue strongly against
   accepting it.

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
1 Introduction: the idea of developing embedded programs hand-in-hand with custom
code generators for them.
2 Background, mostly standard stuff on Agda.  A little on quote/unquote.
3 Basic extraction, illustrated using Kaleidoscope, a minimalist 1st order language from the LLVM team.  Shows how to extract a Kaleidoscope program from an Agda term.  Example of the binary logarithm. Use of Agda rewrite rules.
4 Embedding the array language SaC in Agda, and extracting to it.
A key progression compared to 3 is that SaC has a sophisticated array type system, that can be represented (more or less) within Agda.
5 Embeds a form of APL within Agda.  The embedding is not all of APL; one key concept retained is automatic casting of scalars to vectors and arrays for use with binary operators.

Pros and Cons
+ new idea to embed DSL as a shallow embedding in Agda, but use reflection to access the syntax trees of the shallow embedding, a kind of deep embedding
+ the shallow embedding allows properties to be type-checking, while reflection allows extraction of the verified program back to the original language
+ three separate language examples: core language Kaleidoscope, array language SaC, and APL
+ dependently typed array operations simply fall out of the encoding in the underlying system
- no discussion of performance, eg, of the CNN
- the general principles here are not expressed crisply, eg, as theorems

Comments for author
-------------------
Thanks for all your work on this paper.  I learnt from reading it.

Unfortunately, the main weakness to me is that there is no general theory or crisp principles here, although that may be a weakness in the presentation, rather than the underlying coding.

For the author response, please respond to the next two paragraphs especially.

Your key contribution is the idea of a "reflection-based extractor" for a "shallowly-embeddable language".  What is the reflection-based extractor for your Kaleidoscope example?  What are its key properties?  Can they be expressed as theorems within (or possibly outside) Agda?

Another key contribution is a set of changes to Agda, described in three sections of the paper: 3.4, 3.5, and 4.2, each of which refer to pull requests. Can you describe the changes in terms of general principles that could apply in other settings?

How does the performance of the code extracted from the CNN model compare to the orginal?  I think the original is in APL and the extracted code is in SaC.

It is cool you can write APL formulas directly in Agda.

Can you say anything about what's like to program in these shallow embeddings?  Are the error messages readable?  Could they be customised to the embedded language?

Since their deep versus shallow terminology is in the title, you should cite the paper that originated the distinction between deep and shallow embeddings:

Richard J. Boulton, Andrew D. Gordon, Michael J. C. Gordon, John Harrison, John Herbert, John Van Tassel: Experience with Embedding Hardware Description Languages in HOL. TPCD 1992: 129-156



Review #150B
===========================================================================

Overall merit
-------------
C. I would not accept this paper but will not argue strongly against
   accepting it.

Reviewer expertise
------------------
Z. Some familiarity

Paper summary
-------------
This paper explores some applications of using reflection to implement code
extraction to embedded languages.  The idea is to use reflections facilities to
enable the translation of (subsets of) the host language (in this case, Agda)
into an embedded language.  Such a translation might require both type and term
translation, and might also require the generated code to include dynamic checks
to reconcile the expressive dependend types of the host with those of the
target.  The paper presents several case studies, including a translation of
Agda to Kaleidoscope (a toy language included as an example from the LLVM
framework), to a simple array language, and to APL.

Comments for author
-------------------
# Review

I had a very hard time getting anything out of this paper.  The authors espouse
the benefits of combining "shallow" and "deep" embeddings, ostensibly with the
purposes of doing things like verified extraction or code transformations, but
the paper doesn't really deliver on that promise.  Moreover, I found the
presentation very confusing.  I cannot support this paper for acceptance.

# Comments

- The introduction talks about the ability to "write a verified program
  hand-in-hand with an executor for it" (line 43; maybe you meant
  "extractor"?)), but this paper doesn't seem to include any semantics for the
  languages.  The "verification results" seem to be very limited in nature --
  providing, e.g., some additional guarantees on top of APL's weak shape-based
  type system.  Moreover, since assertations that capture those stronger
  constraints are propagated into the output, I would expect there to be some
  kind of theorem stating that those assertaions are never triggered (under
  reasonable assumptions).  There aren't (as far as I can see), and explicitly
  stated correctness or verification theorems mentioned in the paper. Is
  there  some kind of correctness guarantee that you get when translating from
  APL to SaC via your infrastructure?

- I'm not sure that I would consider the encodings of Kaleidoscope or SaC in
  this paper as "shallow embeddings": my understanding is that a shallow
  embedding uses the features of the host language (in this case, Agda) to
  implement the _semantics_ of the embedded language (often using host-level
  functions to represent embedding-level variable binding, etc.).  However, I
  didn't see any semantics ascribed to Kaleidoscope, and only minimally so for
  SaC.  It looks like this code doesn't do much more than provide the abstract
  syntax for the embedded languages in question -- based on the definitions in
  this paper could you prove anything about the behavior of a program extracted
  to Kaleidoscope?  The APL embedding seems like a true embedded language in the
  sense that its semantics are implemened in Agda.

- In several places, the paper mentions limitations of Agda's reflection API
  that were changed or enhanced while doing this work (e.g. paragraphs near line
  332, 362, 829), but these are mentioned mostly in passing and not described in
  enough detail to be meanginful in any way to the reader.  Pointing to github
  pull requests is not appropriate for a scholarly paper (and isn't kosher for
  double-blind reviewing).  These anecdotes made me wonder what the point of
  this paper is, since it's apparently *not* intended to explain any of the
  technical details involved with these changes.

- The translation of reflected terms into Kaleidoscope doesn't seem to be that
  complicated, but I would have appreciated if the discussion starting at line
  557 had walked though the code of `kompile-term` a bit more explicitly.

# Details

- line 184: says that the primitives are `quote` and `unquote` and that they
  operate "as follows", but the subsequent code uses `macro` and `quote` has
  already been explained above.

- line 331: "contains any about strings" $\to$ "contains any strings"

- line 355: This definition of decidable equality is unintelligible to a reader
  with no Agda experience.  (Also, it might be good to mention earlier that it's
  common for Agda identifiers to include symbols that are usualy considered
  reserved).

- line 787:

- line 789: The "lx type is a type of valid indices..." should probably be "lx d s type is..."

- line 1208: Seems pretty late in the paper to bury the lede about not *really* doing any kind of verification.



Review #150C
===========================================================================

Overall merit
-------------
A. I will champion accepting this paper.

Reviewer expertise
------------------
Y. Knowledgeable

Paper summary
-------------
This paper attempts to answer the choice between shallow and deep embeddings
(in particular in a dependently typed context), by refusing to answer the question
in the first place. Instead, the authors rely on compile-time metaprogramming facilities
in a host language to specify a subset of the host language (in this case Agda) that
serves as the shallow-ish embedding that can be extracted to the target language of choice,
while still allowing for reasoning about its code using all the convenience of a
language like Agda. The paper then proceeds to give two extensive and convincing case
studies using this approach.

Comments for author
-------------------
This paper was _really_ fun to read. It opens with an intriguing idea - can we use
reflection facilities in a dependently typed language - to get the best out of both
worlds: those of shallow and deep embeddings. And it technically delivers that!
The 2/2.5 case studies presented demonstrate convincingly that this is a viable
approach - the matrix multiplication example in particular is an excellent
demonstration that _users_ of the embedding can enjoy strong static guarantees
in a seamless manner like in a shallow embedding. What I'm less convinced by
is the ease of use for the _implementor_. In particular, promises of the introduction
like "No need to touch internals of the host language" are true only in spirit. Yes,
in a language with ideal reflection capabilities what the authors describe would be
even more convenient than described in the paper, but even for this work the authors
had to submit multiple pull requests to change Agda internals and expose additional
capabilities. A deep embedding for Kaleidoscope for example sounds simple enough to be
much more natural to implement - but I guess then you wouldn't enjoy the ease-of-use
that we're seeing here.

Still, even though the paper reads like a tour-de-force in Agda-fu, it is really well written,
with multiple carefully selected and well explained examples. Do I think that after
reading this paper I will be reaching when implementing my next DSL for this technique
(or even that I'm able to reach for this technique without significant investment in
metaprogramming internals)? Perhaps; probably not. But it is a novel first step taking
an old dilemma in a very interesting direction, while showing concrete potential.

======== Minor ==========

- L. 27: Not the canonical citation for Coq I think. Usually people reach for the reference manual

- Pull request links should probably have been elided for the review version
(I haven't clicked them yet as of the time of this writing, but I'm assuming the break double blind)

