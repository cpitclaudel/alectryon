#!/usr/bin/env sh
set -eu
root="${ALECTRYON_DOCKER_ROOT:-$(cd "$(dirname "$0")/.."; pwd)}"
exec docker run --rm -v "$root:/io" -w /io "${ALECTRYON_DOCKER_IMAGE:-alectryon.dev}" "$@"
