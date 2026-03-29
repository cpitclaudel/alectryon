#!/usr/bin/env sh
# Run all test suites.
set -eu

root="$(cd "$(dirname "$0")/.."; pwd)"
export PYTHONPATH="${root}${PYTHONPATH:+:$PYTHONPATH}"

python recipes/tests/doctests.py
python recipes/tests/unit.py
python recipes/tests/end_to_end.py

emacs --batch -Q -l etc/elisp/alectryon-tests.el -f ert-run-tests-batch-and-exit
