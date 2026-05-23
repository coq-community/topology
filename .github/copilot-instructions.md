# Copilot / AI agent instructions — coq-community/topology

This repository is a Coq / Rocq library of general topology, supporting **Coq 8.16 through Rocq 9.1** (and `dev`). When making changes, keep all supported versions building.

## Quick orientation
- Sources: [theories/Topology/](../theories/Topology/), [theories/ZornsLemma/](../theories/ZornsLemma/).
- Build: `make clean && make -j$(nproc)` from the repo root (drives `coq_makefile`-generated `Makefile.coq`).
- Project-wide warning suppressions live in [_CoqProject](../_CoqProject): `-deprecated-from-Coq,-deprecated-missing-stdlib,-deprecated-dirpath-Coq`.
- Supported versions and CI matrix: [meta.yml](../meta.yml), [.github/workflows/docker-action.yml](workflows/docker-action.yml), [coq-topology.opam](../coq-topology.opam), [coq-zorns-lemma.opam](../coq-zorns-lemma.opam).

## Topic-scoped guidance

Granular guidance lives in [.github/instructions/](instructions/) and activates automatically when editing matching files:

- [coq-version-compat.instructions.md](instructions/coq-version-compat.instructions.md) — backwards-compat rules for `.v` files (Coq 8.16 floor, Rocq-9 migration landmines).
- [build-and-verify.instructions.md](instructions/build-and-verify.instructions.md) — build commands, warning auditing, devcontainer notes.
- [api-verification.instructions.md](instructions/api-verification.instructions.md) — verifying stdlib lemma / module names before relying on them.

## Default working rules
- Don't introduce features that break any supported Coq version. Verify replacements for deprecated APIs exist in **8.16** before substituting.
- Don't unconditionally add warning suppressions to `_CoqProject` to mask new issues — fix the source if back-compat allows, or discuss first.
- Don't touch out-of-scope files unless explicitly asked: `Ordinals.v` core, `WellOrders.v`, `ZornsLemma.v`, `TopologicalSpaces.v`, `MetricSpaces.v` definitions, `Cardinals/CSB.v` theorem proper, `FiniteImplicit.v`, `Finite_sets.v` wrappers.
- Run `make -j$(nproc)` and confirm zero errors before declaring a change complete.
