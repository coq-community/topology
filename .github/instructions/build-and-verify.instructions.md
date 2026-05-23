---
applyTo: "**"
description: "Building, testing, and warning auditing for this repository"
---

# Build & verify

## Commands
- Clean build: `make clean && make -j$(nproc)` from repo root.
- Drives `coq_makefile`-generated `Makefile.coq`; tools come from the active opam switch (`coqc`, `rocq`, `vsrocqtop`).
- Capture for inspection: `make -j$(nproc) 2>&1 | tee /tmp/build.log`.

## Warning audit
Group warnings by category to see what changed:
```bash
grep -E "^Warning:" /tmp/build.log | sed -E 's/.*\[([^]]+)\].*/\1/' | sort | uniq -c
```
Acceptable noise: `Fin.t` alternative advisory, `coq_makefile` install-doc orphan notice. Anything else should be investigated.

## Suppressions
Project-wide `-w` flags live in [_CoqProject](../../_CoqProject):
```
-arg -w -arg "-deprecated-from-Coq,-deprecated-missing-stdlib,-deprecated-dirpath-Coq"
```
These exist to absorb informational Rocq-9 dirpath/import-syntax noise while staying compatible with Coq 8.16. **Don't** extend this list to mask genuine new deprecations — fix the source if back-compat allows, or open a discussion.

## CI
Matrix defined in [.github/workflows/docker-action.yml](../workflows/docker-action.yml) covers 8.16–8.20, 9.0, 9.1, and `dev`. A green local `make` is necessary but not sufficient — version-specific failures (especially on the 8.16 floor) only surface in CI.

## Devcontainer
- Base: `ocaml/opam:debian-12-ocaml-4.14`, multi-arch.
- First build of the image takes ~15–30 minutes; subsequent ones use the cache.
- No Docker socket is exposed inside the container, so image rebuilds require **VS Code: "Dev Containers: Rebuild Container"** from the host.
