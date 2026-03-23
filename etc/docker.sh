#!/usr/bin/env sh
docker run --rm  -v "$(pwd):/io" -w /io alectryon "$@"
