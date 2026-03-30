#!/usr/bin/env sh
docker run --rm  -v "$(pwd):/io" -w /io "${ALECTRYON_DOCKER_IMAGE:-alectryon.dev}" "$@"
