<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Topology

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/topology/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/topology/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This library develops some of the basic concepts
and results of general topology in Coq.


## Meta

- Author(s):
  - Daniel Schepler (initial)
- Coq-community maintainer(s):
  - Andrew Miloradovsky ([**@amiloradovsky**](https://github.com/amiloradovsky))
  - stop-cran ([**@stop-cran**](https://github.com/stop-cran))
  - Columbus240 ([**@Columbus240**](https://github.com/Columbus240))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: Coq 8.16 or later (use the corresponding branch or release for other Coq versions)
- Additional dependencies:
  - Zorn's Lemma (set library that is part of this repository)
- Coq namespace: `Topology`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Topology
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-topology
```

To instead build both Topology and Zorn's Lemma manually, do:
``` shell
git clone https://github.com/coq-community/topology.git
cd topology
make   # or make -j <number-of-cores-on-your-machine>
```

## Contents of Topology, roughly grouped in related categories:

### Basic definitions

- `TopologicalSpaces.v`
- `InteriorsClosures.v`
- `Neighborhoods.v`
- `OpenBases.v`
- `NeighborhoodBases.v`
- `Subbases.v`
- `Continuity.v`
- `Homeomorphisms.v`

### Filters and nets

- `Filters.v`
- `FilterLimits.v`
- `DirectedSets.v`
- `Nets.v`
- `FiltersAndNets.v` - various transformations between filters and nets

### Properties

- `Compactness.v`
- `Connectedness.v`
- `CountabilityAxioms.v` - first countable, second countable, separable, Lindelof
- `SeparatednessAxioms.v` - T0, T1, Hausdorff, etc.

### General constructions of topologies

- `OrderTopology.v`
- `StrongTopology.v` - strong topology induced by a family of maps from
topological spaces
- `WeakTopology.v` - weak topology induced by a family of maps to
topological spaces
- `ProductTopology.v`
- `SumTopology.v` - also called "disjoint union" or "coproduct"
- `SubspaceTopology.v`
- `QuotientTopology.v`
- `ContinuousFactorization.v` - a continuous map factors through its image

### Metric spaces

- `MetricSpaces.v`
- `Completeness.v`
- `Completion.v`
- `UniformTopology.v` - the topology of uniform convergence

### Real analysis

- `SupInf.v`
- `RationalsInReals.v`
- `RTopology.v` - definition and properties of topology on R
- `RFuncContinuity.v` - reproof of continuity of basic functions on R

### "First nontrivial results of topology"

- `UrysohnsLemma.v`
- `TietzeExtension.v`

## Contents of Zorn's Lemma

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

- `EnsemblesTactics.v` - defines tactics that help in proofs about Ensembles

- `EnsemblesUtf8.v` - optional UTF-8 notations for set operations

- `Families.v` - operations on families of subsets of `X`, i.e. `Ensemble (Ensemble X)`
- `IndexedFamilies.v` - same for indexed families `A -> Ensemble X`

- `FiniteIntersections.v` - defines the finite intersections of a family of subsets

- `FiniteTypes.v` - definitions and results about finite types
- `CountableTypes.v` - same for countable types
- `InfiniteTypes.v` - same for infinite types

- `FunctionProperties.v` - injective, surjective, etc.

- `InverseImage.v` - inverse images of subsets under functions

- `Powerset_facts.v` - some lemmas about the operations on subsets that the stdlib is missing

- `Proj1SigInjective.v` - inclusion of `{ x: X | P x }` into `X` is injective

- `Quotients.v` - quotients by equivalence relations, and induced functions on them

- `ReverseMath` - a folder with some results in constructive reverse mathematics

- `WellOrders.v` - some basic properties of well-orders, including a proof that Zorn's Lemma implies the well-ordering principle

- `ZornsLemma.v` - proof that choice implies Zorn's Lemma
