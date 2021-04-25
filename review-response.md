
We would like to thank the reviewers for their time and helpful comments. We
will start this response by addressing common concerns raised by multiple
reviewers; after that, we respond to the remaining individual comments and
questions.

# Part1: Common concerns

## The main objective (reviewer B)

Our main objective is to demonstrate how to define a *dependently-typed DSL*
without implementing a full typechecker, as you share one with Agda. Extraction
allows us to translate our DSL to a target language for further execution. We
expect two possible scenarios: 1) translating an existing (dependently typed)
DSL to target X; or 2) extend existing language X with dependent types. Both
scenarios are possible by our approach, and are novel to the best of our
knowledge.

## Shallow embedding and its semantics (reviewers A and B)

For the purpose of this paper, we define any Agda term that is recognized by
the extractor to be part of the embedded language (as noted on line 315).
Moreover, the semantics of the embedded language is obtained by restricting the
semantics of Agda to this subset. The writer of the extractor thus has full
control over what parts of Agda to include or exclude.

## Lack of theory or general principles (reviewers A and B)

Despite our focus on the practical parts of writing custom extractors, this
does not mean our approach does not care about the semantics. In particular,
the extractor maps the reflected Agda syntax of the embedded language to the
target language, and inserts assertions corresponding to the static guarantees
of Agda's type system. Hence, given an extractor that preserves the dynamic
semantics of the embedded language, soundness of the Agda type system
guarantees that none of the inserted assertions will be triggered at run-time.
When only part of a program is extracted from Agda, assertions can only fire at
the boundaries with unsafe code.

Correctness of our approach thus relies on the preservation of the dynamic
semantics by the extractor code. Ideally we would like to prove this as a
theorem in Agda, but this is not yet possible as there is no formal semantics
for Agda reflected terms (see future work section).

## Pull Requests inclusion in the paper (all reviewers)

Our reason for including links to PRs is because we consider them essential to
the work presented in the paper. The important thing is not how they are
implemented (as this will be different for each host language), but rather what
features are required for our approach to reflection-based extraction. In
particular, we need:

- access to the full type and typing context of a given term,

- the ability to selectively normalise certain functions while keeping others
untouched,

- access to transient terms that are erased from the syntax but can be
reconstructed from the type.

As our approach has not been tried before, some functionality was lacking so we
had to add it. However, none of this is specific to a particular extractor (or
even specific to extraction in general), so it only needs to be done once.

According to our interpretation of the requirements of "lightweight
double-blind", inclusion of these links seems to be acceptable: they do not
expose our names or institutions, and as the work has been done specifically
for this paper we did not have to address it in third person. We apologize if
this differs from the intended interpretation.




# Part2: Remaining concerns


> For the author response, please respond to the next two paragraphs
> especially.
> 
> Your key contribution is the idea of a "reflection-based extractor" for a
> "shallowly-embeddable language".  What is the reflection-based extractor for
> your Kaleidoscope example?  What are its key properties?  Can they be
> expressed as theorems within (or possibly outside) Agda?

Reflection based extractor for the Kaleidoscope language is define in
`agda-extractor/Kaleid.agda` and it purpose is to translate the chosen
subset of Agda to Kaleidoscope language.  The key properties of the translator
is the preservation of dependent types such as Fin, `_<_`, `_>_`, 
equivalence/inequivalence of natural numbers in the generated code via
assertions.  Essentially, we have extended the original formulation of
the Kaleidoscope with dependent types.  E.g. in our log2 example we ensure
that the no dvivision by zero is possible, and we also ensure that the
function terminates (as each Agda function has to terminate).

> Another key contribution is a set of changes to Agda, described in three
> sections of the paper: 3.4, 3.5, and 4.2, each of which refer to pull
> requests. Can you describe the changes in terms of general principles that
> could apply in other settings?

See part 1.

> How does the performance of the code extracted from the CNN model compare to
> the orginal?  I think the original is in APL and the extracted code is in
> SaC.

As our main goal was to demonstrate the mere possibility of embedding
non-trivial languages, we didn't pay much attention to the performance aspect
of the extracted code, as in some sense it is orthogonal to the process.
However, as our code carefully follows this paper:
https://dl.acm.org/doi/10.1145/3315454.3329960
The paper includes the SaC version of the CNN application, and we create
our extractor to produce the code that is as close as possible to the existing
SaC code.  Unsurprisingly, performance of the SaC code that we generate is
almost identical to the performance of the SaC code reported in the paper:
it is 15 and 24 times faster for training and recognition correspondingly,
when comparing to APL.  However, this result cannot be treated as an exhaustive
set of measurements, as it is coming from a single example on a single machine.

> Can you say anything about what's like to program in these shallow
> embeddings?  Are the error messages readable?  Could they be customised to
> the embedded language?

There are two types of messages that are happening: i) Agda error messages that
can't be specific to the embedded DSL; ii) error messages coming from the extractor.
The latter is fully programmable, and as Agda gives basic capabilities to format
terms and report a custom error, these can be made as precise as needed by the
author of the extractor.

> Since their deep versus shallow terminology is in the title, you should cite
> the paper that originated the distinction between deep and shallow
> embeddings:
> 
> Richard J. Boulton, Andrew D. Gordon, Michael J. C. Gordon, John Harrison,
> John Herbert, John Van Tassel: Experience with Embedding Hardware Description
> Languages in HOL. TPCD 1992: 129-156

Of course, thank you for the reference, we are happy to include it in the paper.



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

