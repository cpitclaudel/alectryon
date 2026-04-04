#!/usr/bin/env sh
set -eu
exec docker run --rm -v "$(pwd):/io" -w /io "${ALECTRYON_DOCKER_IMAGE:-alectryon.dev}" "$@"
