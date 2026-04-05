#!/usr/bin/env sh
# Usage: screenshot.sh <src.html> <dst.pdf>
set -eu
here="$(cd "$(dirname "$0")"; pwd)"
npm --prefix "$here" install
"$here/node_modules/.bin/playwright" install chromium
exec node "$here/screenshot.mjs" "$@"
