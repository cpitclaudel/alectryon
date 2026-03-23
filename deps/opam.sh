#!/usr/bin/env bash
# Install Rocq and vsrocq-language-server

set -eu

ocaml_version="${1:-}"
rocq_version="${2:-}"
if [ -z "$ocaml_version" ] || [ -z "$rocq_version" ]; then
  echo "Usage: $0 <ocaml_version> <rocq_version>"
  exit 1
fi

switch=alectryon

[ -d ~/.opam/$switch ] || opam switch create $switch $ocaml_version
eval "$(opam env --switch=$switch --set-switch)"

opam repo add rocq-released https://rocq-prover.org/opam/released

opam update
opam pin add -n rocq-core "$rocq_version"
opam pin add -n rocq-runtime "$rocq_version"
opam pin add -n vsrocq-language-server.dev https://github.com/rocq-prover/vsrocq.git --subpath=language-server
opam install --yes rocq-core rocq-stdlib rocq-runtime vsrocq-language-server

opam switch link
