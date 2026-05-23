---
applyTo: "theories/**/*.v"
description: "Coq 8.16 → Rocq 9.1 compatibility rules for theory files"
---

# Coq / Rocq version compatibility

This library supports **Coq 8.16 through Rocq 9.1** (and `dev`). All `.v` edits must compile across that range.

## Forbidden constructs (Rocq-9-only)
- `From Stdlib Require …` — keep `From Coq Require …` everywhere. The resulting `deprecated-from-Coq` warning is suppressed project-wide.
- Identifiers that only exist in Rocq 9 (verify before using; see [api-verification.instructions.md](api-verification.instructions.md)).

## Known migration landmines

When you see a Rocq-9 deprecation warning telling you to "use X instead", **verify when X was introduced** before substituting. Several common replacements post-date 8.16:

| Deprecated form | Replacement | Replacement available since | Back-compat fix |
|---|---|---|---|
| `double_var` (Reals) | `Rplus_half_diag` | Coq 8.19 | Inline: `replace x with (x/2 + x/2) by lra.` |
| `inj_plus` | `Nat2Z.inj_add` | older | `Require Import ZArith.` then use `Nat2Z.inj_add` |
| `Coq.X.Y.foo` qualifier | `Stdlib.X.Y.foo` | Rocq 9 only | Drop only the top-level prefix → `X.Y.foo`. Works on all versions and silences `deprecated-dirpath-Coq`. |
| `From Coq Require …` | `From Stdlib Require …` | Rocq 9 only | Keep `From Coq`; warning suppressed in `_CoqProject`. |

`positive_nat_Z` and similar Z-arithmetic lemmas require `Require Import ZArith` explicitly under Rocq 9.

## Module qualifier shortening trick
The fully-qualified `Coq.X.Y.foo` triggers `deprecated-dirpath-Coq` under Rocq 9. **Dropping only the top-level `Coq.`** (e.g. `Coq.Sets.Powerset_facts.Disjoint_Intersection` → `Powerset_facts.Disjoint_Intersection`) resolves cleanly on every supported version. Fully unqualifying (`Disjoint_Intersection`) may collide with locally-defined lemmas of the same name — e.g. [theories/ZornsLemma/Powerset_facts.v](../../theories/ZornsLemma/Powerset_facts.v) defines its own `Disjoint_Intersection` that shadows the stdlib one, so the module qualifier is mandatory there.

## Scope discipline
- `Open Scope foo_scope.` at file level leaks the scope to all importers. Prefer `Local Open Scope foo_scope.` unless the scope is part of the file's public API.
- Before changing a scope directive, grep for downstream consumers: `grep -rln "foo_scope\|<scope-notations>" theories/`.

## Refactoring proofs with `extensionality_ensembles`
The project-local tactic in [theories/ZornsLemma/EnsemblesTactics.v](../../theories/ZornsLemma/EnsemblesTactics.v) is great for symmetric set-equality proofs, but is brittle when:
- The Ensemble has a non-`In`-headed reduction (e.g. `Complement U` unfolds to `~ U x`, not a `In _ _` constructor — `destruct_ensembles_in` won't fire).
- The two split-branches need asymmetric numbers of destructs (the inner `repeat destruct_ensembles_in` may auto-discharge one side via vacuous case-analysis on `Empty_set`, leaving fewer goals than `[ g1 | g2 ]` expects).
- The conclusion still needs explicit `constructor` interleaving (e.g. `In (inverse_image f T) x` requires its own constructor; a single `repeat constructor; trivial` after the tactic may leave open goals).

When the substitution doesn't go through, revert to the explicit `apply Extensionality_Ensembles; split; red; intros.` skeleton rather than fighting the tactic.
