#!/usr/bin/env sh
# Run Python test suites.
set -eu

root="$(cd "$(dirname "$0")/../.."; pwd)"
export PYTHONPATH="${root}${PYTHONPATH:+:$PYTHONPATH}"

python recipes/tests/doctests.py
python recipes/tests/unit.py
python recipes/tests/end_to_end.py
