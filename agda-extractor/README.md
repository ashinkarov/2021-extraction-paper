# Extraction Framework for Agda Programs

This framework simplifies creation of custom extractors from Agda
into the programming language of your choice.  We heavily rely on
the reflection capabilities of Agda and essentially explain how to
turn reflected definitions into the programming language of your
choice.

The structure of this repository is as follows:

  * Extract.agda        -- Genreal extraction framework
  * ReflHelper.agda     -- Some helper functions to deal with reflection
  * Structures.agda     -- Common structures used by all extractors
                        -- All kinds of monads and instances

  * Kaleid.agda         -- Extractor for the Kaleidoscope langauge
  * KalExample-00.agda  -- Few examples of programs that we extract to Kaleidoscope

  * Array/              -- Data types for multi-dimensional arrays
  * Array.agda          -- A very simple wrapper-module
  * APL2.agda           -- Implementation of APL operators based on
                        -- Array library.
  * ExtractSac.agda     -- Extractor into SaC.
  * SacTy.agda          -- A module that deals with sac types.
  * sac-runtime/        -- A few sac definitions that are assumed to
                        -- be defined so that extracted programs run correctly.

  * Example-00.agda     -- Examples containing SaC/APL functions
  * Example-01.agda
  * Example-02.agda
  * Example-03.agda
  * Example-04.agda
  * Example-05.agda
