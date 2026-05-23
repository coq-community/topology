---
applyTo: "theories/**/*.v"
description: "Verifying stdlib lemma and module names before relying on them"
---

# Verify stdlib names before using them

AI suggestions for stdlib lemma names are frequently **plausible but wrong** (e.g. `Included_refl`, `Same_set_refl`, `Included_trans` — none of these exist in `Coq.Sets.Powerset_facts`). Verify any non-obvious name against the *installed* library before adding it to source, hint databases, or `apply`/`rewrite` chains.

## Cheap verification recipes

Check a single name:
```bash
echo 'From Coq Require Import Ensembles. Check Included_refl.' | coqtop 2>&1 | tail -5
```

Search by pattern (best for discovering what *does* exist):
```bash
echo 'From Coq Require Import Ensembles Sets.Powerset_facts. Search "Included".' | coqtop 2>&1 | tail -40
```

Inspect a definition:
```bash
echo 'From Coq Require Import Ensembles. Print Included. Print In.' | coqtop 2>&1 | tail -20
```

## What to do when the suggested name doesn't exist
- Don't guess nearby names. Pick a different strategy:
  - Inline with primitive tactics (`replace … by lra`, `rewrite … by …`, `unfold … in …`).
  - Use a typeclass/order instance if the library provides one (e.g. `Inclusion_is_an_order`, `Transitive (Included U)`).
  - Build the missing lemma locally if it's genuinely absent and broadly useful.
- For hint databases: prefer `Hint Unfold` on verified definitions (e.g. `Hint Unfold In Included : sets.`) over `Hint Resolve` on speculative lemma names.

## Verify across supported versions
A name that exists in Rocq 9 may not exist in Coq 8.16. When in doubt, check the Coq changelog or the `theories/` directory of the older release. If the name is too new, fall back to an inline tactic that works everywhere — see [coq-version-compat.instructions.md](coq-version-compat.instructions.md) for the established migration table.
