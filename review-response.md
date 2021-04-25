
We would like to thank the reviewers for their time and helpful comments. We
will start this response by addressing common concerns raised by multiple
reviewers; after that, we respond to the remaining individual comments and
questions.

# Part1: Common concerns

## The main objective (reviewer B)

Our main objective is to demonstrate how to define a *dependently-typed DSL*
without implementing a full typechecker, as you share one with Agda. Extraction
allows us to translate our DSL to a target language for further execution.  This
translation is expressed within Agda without necessity to modify the compiler.  We
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
When only part of a program is extracted from Agda (which is perfectly possible),
assertions can only fire at the boundaries with unsafe code.

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

## Review #150A

> For the author response, please respond to the next two paragraphs
> especially.
>
> Your key contribution is the idea of a "reflection-based extractor" for a
> "shallowly-embeddable language".  What is the reflection-based extractor for
> your Kaleidoscope example?  What are its key properties?  Can they be
> expressed as theorems within (or possibly outside) Agda?

Reflection based extractor for the Kaleidoscope language is defined in
`agda-extractor/Kaleid.agda` and it purpose is to translate the chosen
subset of Agda to Kaleidoscope language.  The key properties of the translator
is the preservation of dependent types such as Fin, `_<_`, `_>_`,
equivalence/inequivalence of natural numbers in the generated code via
assertions.  Essentially, we have extended the original formulation of
the Kaleidoscope to include dependent types.  E.g. in our log2 example types ensure
that the dvivision by zero is impossible, and we know that the extracted
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
non-trivial languages, we didn't focus too much on the performance aspect
of the extracted code in the text of the paper.  In some sense it is orthogonal
to the extraction process.  However, our code carefully follows this paper:
https://dl.acm.org/doi/10.1145/3315454.3329960
The paper includes a SaC version of the CNN application, and we created
our extractor to produce the code that is as close as possible to the existing
SaC code.  Unsurprisingly, performance of the SaC code that we generate is
almost identical to the performance of the SaC code reported in the paper:
it is 15 and 24 times faster for training and recognition correspondingly,
when comparing to APL (recall that APL is an interpreter, but SaC is
a compiled language).  However, this result should not be treated as an exhaustive
set of measurements, as it is coming from a single example on a single machine.

> Can you say anything about what's like to program in these shallow
> embeddings?  Are the error messages readable?  Could they be customised to
> the embedded language?

There are two types of error messages that can be triggered: i) Agda error messages;
ii) error messages coming from the extractor.  The former can't be specific to the
embedded DSL.  The latter is fully programmable; and as Agda includes basic capabilities
to format terms and report custom errors, these can be made as precise as needed by the
author of the extractor.  Practically, as long as functions are reasonably sized
(as in our case) the error messages are readable.

> Since their deep versus shallow terminology is in the title, you should cite
> the paper that originated the distinction between deep and shallow
> embeddings:
>
> Richard J. Boulton, Andrew D. Gordon, Michael J. C. Gordon, John Harrison,
> John Herbert, John Van Tassel: Experience with Embedding Hardware Description
> Languages in HOL. TPCD 1992: 129-156

Of course, thank you for the reference, we are happy to include it in the paper.

## Review #150B

> - The introduction talks about the ability to "write a verified program
>   hand-in-hand with an executor for it" (line 43; maybe you meant
>   "extractor"?)),

It seems that "executor" is adequate, as we assume to extract the code into
a language that can compile/run the extracted piece of code.

>   but this paper doesn't seem to include any semantics for the
>   languages.

See part 1: embedded language is a subset of Agda, therefore it shares Agda's
semantics.

>   The "verification results" seem to be very limited in nature --
>   providing, e.g., some additional guarantees on top of APL's weak shape-based
>   type system.

This is more "correct-by-construction programming" rather than classical verification.
As dependent types can encode virtually any constraints on terms, and the type system
guarantees that these hold statically, and extractor preserves (modulo extractor
correctness) these constraints in the generated code, we can talk about a verified
program.

>   Moreover, since assertations that capture those stronger
>   constraints are propagated into the output, I would expect there to be some
>   kind of theorem stating that those assertaions are never triggered (under
>   reasonable assumptions).  There aren't (as far as I can see), and explicitly
>   stated correctness or verification theorems mentioned in the paper. Is
>   there  some kind of correctness guarantee that you get when translating from
>   APL to SaC via your infrastructure?

See Part 1.

> - I'm not sure that I would consider the encodings of Kaleidoscope or SaC in
>   this paper as "shallow embeddings": my understanding is that a shallow
>   embedding uses the features of the host language (in this case, Agda) to
>   implement the _semantics_ of the embedded language (often using host-level
>   functions to represent embedding-level variable binding, etc.).  However, I
>   didn't see any semantics ascribed to Kaleidoscope, and only minimally so for
>   SaC.  It looks like this code doesn't do much more than provide the abstract
>   syntax for the embedded languages in question -- based on the definitions in
>   this paper could you prove anything about the behavior of a program extracted
>   to Kaleidoscope?  The APL embedding seems like a true embedded language in the
>   sense that its semantics are implemened in Agda.

Additionally to explanations in Part 1, all the three languages share Agda's semantics.
However, it happened so, that many Kaleidoscope and SaC constructs, such as Nat,
arithmetic expressions, functions, etc. are also built-in Agda's constructs.
Therefore, there is no obvious Agda function that implements some embedded structures.
However, reflection makes the entire Agda AST available, therefore as long as
Agda terms have semantics, so does the embedding.

> - In several places, the paper mentions limitations of Agda's reflection API
>   that were changed or enhanced while doing this work (e.g. paragraphs near line
>   332, 362, 829), but these are mentioned mostly in passing and not described in
>   enough detail to be meanginful in any way to the reader.  Pointing to github
>   pull requests is not appropriate for a scholarly paper (and isn't kosher for
>   double-blind reviewing).  These anecdotes made me wonder what the point of
>   this paper is, since it's apparently *not* intended to explain any of the
>   technical details involved with these changes.

See Part 1.

> - The translation of reflected terms into Kaleidoscope doesn't seem to be that
>   complicated, but I would have appreciated if the discussion starting at line
>   557 had walked though the code of `kompile-term` a bit more explicitly.

We will adjust this bit of the paper.

> - line 355: This definition of decidable equality is unintelligible to a reader
>   with no Agda experience.  (Also, it might be good to mention earlier that it's
>   common for Agda identifiers to include symbols that are usualy considered
>   reserved).

We are happy to expand on this.

> - line 789: The "lx type is a type of valid indices..." should probably be "lx d s type is..."

You are right. We used "type" and "type family" interchangeably.  We will clarify this.

- line 1208: Seems pretty late in the paper to bury the lede about not *really* doing any kind of verification.

This is because our main focus is to provide the framework in which it is
possible to define such embeddings in the first place.  When we extract Ocaml
from Coq it is as unverified as what we propose.


## Review #150C

> What I'm less convinced by
> is the ease of use for the _implementor_. In particular, promises of the introduction
> like "No need to touch internals of the host language" are true only in spirit. Yes,
> in a language with ideal reflection capabilities what the authors describe would be
> even more convenient than described in the paper, but even for this work the authors
> had to submit multiple pull requests to change Agda internals and expose additional
> capabilities. A deep embedding for Kaleidoscope for example sounds simple enough to be
> much more natural to implement - but I guess then you wouldn't enjoy the ease-of-use
> that we're seeing here.

Yes, you are right.  However, as we are trying a novel approach that hasn't been tried
before (to our knowledge), we don't expect all the necessary API to be present.
As you can see from Part 1, our extensions are not language-specific.  They are
of a general nature, and given a few more language embeddings will be tried out,
the API should stabilise rather quickly.

> - L. 27: Not the canonical citation for Coq I think. Usually people reach for
>   the reference manual

Thanks, happy to adjust that.

> - Pull request links should probably have been elided for the review version
> (I haven't clicked them yet as of the time of this writing, but I'm assuming
> the break double blind)

See Part 1.

