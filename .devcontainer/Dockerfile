# Multi-arch (amd64 + arm64) base image with opam + OCaml preinstalled.
# Maintained by the OCaml team: https://hub.docker.com/r/ocaml/opam
FROM ocaml/opam:debian-12-ocaml-4.14

# System libraries required to build Rocq and common OCaml packages from opam.
RUN sudo apt-get update \
    && sudo apt-get install -y --no-install-recommends \
        libgmp-dev \
        pkg-config \
        m4 \
        ca-certificates \
        git \
    && sudo rm -rf /var/lib/apt/lists/*

# Pin Coq (now "The Rocq Prover") to a version satisfying coq-topology.opam
# (>= 8.16 & < 9.2) and install the language servers used by the VsRocq /
# coq-lsp clients. This step is what takes time on first build (~10-20 min
# on arm64) but it is cached afterwards.
RUN opam update -y \
    && opam install -y -j 4 \
        dune \
        coq.9.1.1 \
        coq-stdlib \
        coq-lsp \
        vsrocq-language-server \
    && opam clean -a -c -s --logs

# Make `opam env` available to non-login shells used by VS Code tasks.
RUN echo 'eval $(opam env --switch=default)' >> /home/opam/.bashrc

WORKDIR /workspaces
