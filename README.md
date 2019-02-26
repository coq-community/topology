# Zorn's Lemma

[![Travis][travis-shield]][travis-link]

[travis-shield]: https://travis-ci.com/coq-community/zorns-lemma.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/zorns-lemma/builds



This library develops some basic set theory.
The main purpose the author had in writing it was as support for the Topology library.



## Meta

- Author(s):
  - Daniel Schepler (initial)
- License: [GNU Lesser General Public License v2.1 or later](COPYING)
- Compatible Coq versions: Coq 8.6 or later
- Additional Coq dependencies: none

## Building and installation instructions

The easiest way to install the latest released version of Zorn's Lemma
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-zorns-lemma
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/zorns-lemma
cd zorns-lemma
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `ZornsLemma` namespace.



## Contents

In alphabetical order, except where related files are grouped together:

- `Cardinals.v` - cardinalities of sets
- `Ordinals.v` - a construction of the ordinals without reference to well-orders

- `Classical_Wf.v` - proofs of the classical equivalence of wellfoundedness, the minimal element property, and the descending sequence property

- `CSB.v` - the Cantor-Schroeder-Bernstein theorem

- `DecidableDec.v` - `classic_dec: forall P: Prop, {P} + {~P}.`

- `DependentTypeChoice.v` - choice on a relation (`forall a: A, B a -> Prop`)

- `EnsemblesImplicit.v` - settings for appropriate implicit parameters for the standard library's Ensembles functions
- `ImageImplicit.v` - same for the standard library's Sets/Image
- `Relation_Definitions_Implicit.v` - same for the standard library's Relation_Definitions

- `EnsemblesSpec.v` - defines a notation for e.g. `[ n: nat | n > 5 /\ even n ] : Ensemble nat.`

- `EnsemblesUtf8.v` - optional UTF-8 notations for set operations

- `Families.v` - operations on families of subsets of `X`, i.e. `Ensemble (Ensemble X)`
- `IndexedFamilies.v` - same for indexed families `A -> Ensemble X`

- `FiniteIntersections.v` - defines the finite intersections of a family of subsets

- `FiniteTypes.v` - definitions and results about finite types
- `CountableTypes.v` - same for countable types
- `InfiniteTypes.v` - same for infinite types

- `FunctionProperties.v` - injective, surjective, etc.

- `InverseImage.v` - inverse images of subsets under functions

- `Proj1SigInjective.v` - inclusion of `{ x: X | P x }` into `X` is injective

- `Quotients.v` - quotients by equivalence relations, and induced functions on them

- `WellOrders.v` - some basic properties of well-orders, including a proof that Zorn's Lemma implies the well-ordering principle

- `ZornsLemma.v` - proof that choice implies Zorn's Lemma

## Copyright

ZornsLemma Coq contribution
Copyright (C) 2011  Daniel Schepler

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

