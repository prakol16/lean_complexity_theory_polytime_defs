# Polynomial-Time Algorithms in Lean

An attempt to define polynomial time algorithms in Lean. Parts of this code were based on https://github.com/leanprover-community/mathlib/pull/11046.

This repository duplicates a lot of code (e.g. in `tm_to_partrec`), or uses a very slight variation because the original code doesn't quite work.
Eventually, there will probably need to be a refactor that unifies all the computability stuff using some common ideas.

## Overview
  - `src/boolcodeable.lean` -- An analogue of `encodable` for bitstrings (`list bool`). The idea is to use instance search, but use only relatively "efficient" encodings.
  - `src/code.lean` -- Defines an encoding of computable functions that is efficient and uses bitstrings instead of natural numbers
  -  `src/time_boudn.lean` -- Defines what it means for a function to run in bounded time.
  -  `src/lists.lean` `src/part.lean` `src/frespects_pfun.lean` -- Miscellaneous helper functions 
