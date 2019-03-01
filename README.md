# Topology

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]

[travis-shield]: https://travis-ci.com/coq-community/topology.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/topology/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby

This library develops some of the basic concepts and results of general topology.



## Meta

- Author(s):
  - Daniel Schepler (initial)
- Maintainer(s):
  - Andrew Miloradovsky ([**@amiloradovsky**](https://github.com/amiloradovsky))
- License: [GNU Lesser General Public License v2.1 or later](COPYING)
- Compatible Coq versions: Coq 8.6 or later (use the corresponding branch or release for other Coq versions)
- Additional dependencies:
  - [Zorn's lemma](https://github.com/coq-community/zorns-lemma)



## Building and installation instructions

The easiest way to install the latest released version is via
[OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-topology
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/topology
cd topology
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `Topology` namespace.

## Contents, roughly grouped in related categories:

### Basic definitions

- `TopologicalSpaces.v`
- `InteriorsClosures.v`
- `Neighborhoods.v`
- `OpenBases.v`
- `NeighborhoodBases.v`
- `Subbases.v`
- `Continuity.v`
- `Homeomorphisms.v`

# Filters and nets

- `Filters.v`
- `FilterLimits.v`
- `DirectedSets.v`
- `Nets.v`
- `FiltersAndNets.v` - various transformations between filters and nets

# Properties

- `Compactness.v`
- `Connectedness.v`
- `CountabilityAxioms.v` - first countable, second countable, separable, Lindelof
- `SeparatednessAxioms.v` - T0, T1, Hausdorff, etc.

# General constructions of topologies

- `OrderTopology.v`
- `StrongTopology.v` - strong topology induced by a family of maps from
topological spaces
- `WeakTopology.v` - weak topology induced by a family of maps to
topological spaces
- `ProductTopology.v`
- `SubspaceTopology.v`
- `ContinuousFactorization.v` - a continuous map factors through its image

# Metric spaces

- `MetricSpaces.v`
- `Completeness.v`
- `Completion.v`
- `UniformTopology.v` - the topology of uniform convergence

# Real analysis

- `SupInf.v`
- `RationalsInReals.v`
- `RTopology.v` - definition and properties of topology on R
- `RFuncContinuity.v` - reproof of continuity of basic functions on R

# "First nontrivial results of topology"

- `UrysohnsLemma.v`
- `TietzeExtension.v`

## Copyright

Topology Coq contribution
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

