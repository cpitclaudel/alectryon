#!/usr/bin/env bash
# Install Rocq, vsrocq-language-server, and EasyCrypt

set -eu

usage() {
  echo "Usage: $0 <ocaml_version> [--switch NAME] [--rocq-version VERSION] [--easycrypt-version TAG]"
  exit 1
}

ocaml_version="${1:-}"
[ -z "$ocaml_version" ] && usage
shift

switch="alectryon"
rocq_version=""
easycrypt_tag=""

while [ $# -gt 0 ]; do
  case "$1" in
    --switch)            switch="$2"; shift 2 ;;
    --rocq-version)      rocq_version="$2"; shift 2 ;;
    --easycrypt-version) easycrypt_tag="$2"; shift 2 ;;
    *) usage ;;
  esac
done

[ -d ~/.opam/$switch ] || opam switch create $switch $ocaml_version
eval "$(opam env --switch=$switch --set-switch)"

opam repo add rocq-released https://rocq-prover.org/opam/released
opam update

## Rocq

if [ -n "$rocq_version" ]; then
  opam pin add -n rocq-core "$rocq_version"
  opam pin add -n rocq-runtime "$rocq_version"
  opam pin add -n vsrocq-language-server.dev https://github.com/rocq-prover/vsrocq.git --subpath=language-server
  opam install --yes rocq-core rocq-stdlib rocq-runtime vsrocq-language-server
fi

## EasyCrypt

if [ -n "$easycrypt_tag" ]; then
  opam pin add -n easycrypt.dev "https://github.com/EasyCrypt/easycrypt.git#$easycrypt_tag"
  opam install --yes easycrypt alt-ergo
  easycrypt why3config
fi

opam switch link $switch
