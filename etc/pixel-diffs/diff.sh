#!/usr/bin/env bash
# Usage:
#   diff.sh                    # compare HEAD vs working tree
#   diff.sh <ref>              # compare <ref> vs working tree
#   diff.sh <ref-A> <ref-B>    # compare <ref-A> vs <ref-B>
set -eu -o pipefail
set -x

here="$(cd "$(dirname "$0")"; pwd)"
root="$(cd "$here/../.."; pwd)"

sha() { git -C "$root" rev-parse --short=10 "$1"; }

case $# in
    0) a=$(sha HEAD); b=workdir ;;
    1) a=$(sha "$1"); b=workdir ;;
    2) a=$(sha "$1"); b=$(sha "$2") ;;
    *) echo "Usage: $0 [<ref>|<ref-A> <ref-B>]" >&2; exit 1 ;;
esac

cd "$here"
npm install
./node_modules/.bin/playwright install chromium

work=$(mktemp -d -t alectryon-pixel-diff.XXXXXX)
trap 'rm -rf "$work"' EXIT

prepare() {
    label=$1
    if [ "$label" = workdir ]; then
        src="$root"
    else
        src="$work/src-$label"
        mkdir -p "$src"
        git -C "$root" archive --format=tar "$label" | tar -x -C "$src"
    fi
    echo "=== Building recipes for $label ==="
    ALECTRYON_DOCKER_ROOT="$src" "$root/etc/docker.sh" make -j -k -O test || true
    echo "=== Rendering $label ==="
    rm -rf "_build/$label"
    node render.mjs "$src/recipes/_output" "_build/$label"
}

prepare "$a"
prepare "$b"

echo "=== Comparing ==="
rm -rf _build/report && mkdir -p _build/report
./node_modules/.bin/reg-cli "_build/$b" "_build/$a" _build/report/diff \
    -R _build/report/index.html -J _build/report/summary.json -T 0 || :

echo
echo "Report: file://$here/_build/report/index.html"
