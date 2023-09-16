These are a few notes on conventions, style and formatting used in
this library.

# 1. Applying these notes
This library contains many different conventions mixed
together. So changing the style all at once would be a lot of work.
Instead it suffices that all new changes adhere to these notes.

The formatting is mostly based on what is easy to achieve with
ProofGeneral without further configuration.

# 2. Structure
Within ZornsLemma, the only files which shall develop any theory about
`Finite` and `FiniteT` shall be `Finite_sets` for the former and
`FiniteTypes` for the latter. This is to prevent circular
dependencies.

The folder `Cardinals` shall only contain facts which are independent of
any fixed type or subset. I.e. no properties of [nat] or uncountable sets.
Those shall be put in other files. But combinatorics of sets (existence of
injections, surjections, bijections/invertible maps) is fine.
This is again to prevent circular dependencies.

# 3. Imports
Prefer `Require Import` over `Require Export`.

Using `Require Export` the dependenices between files are kept
invisible, which makes it harder to detect which import causes a given
definition or notation to be loaded. Also, if circular dependencies
would arise, it can be hard to find out how it is caused.

Formatting of imports.
Prefer
```coq
From Coq Require Import
  ClassicalChoice
  Description
  Program.Subset.
From ZornsLemma Require Import
  DecidableDec
  EnsemblesImplicit
  Families
  FunctionProperties
  Image
  InverseImage
  Powerset_facts
  Proj1SigInjective.
(* load [RelationClasses] last to override [Relations_1] *)
From Coq Require Import RelationClasses.
```
to all previous styles. It is defined by
* A command has the form `From XX Require Import/Export YY.` to give
  the full path to each imported file.
  This prevents ambiguities.
* Start with imports from `Coq`, then other libraries if necessary,
  then imports from the current library.
  This allows the definitions of the current library to overwrite
  other libraries.
  If for some reason a file needs to overwrite previous imports, put
  it last.
* If multiple files from the same library are imported, use separate
  lines for each file. Indent by two spaces and order the files
  alphabetically.
  This creates simpler diffs when adding/removing files than when
  multiple files are on a single line. The merge conflicts can be very
  complicated.

# 4. Proof formatting
Proofs begin with `Proof.` on the same indentation as the `Lemma` (or
similar) statement. The Ltac commands of the proof start on a new line
and are indented by two spaces (as done automatically by ProofGeneral).
