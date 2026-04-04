#!/usr/bin/env sh
# Build a wheel, install it in a fresh venv, and run tests against it.
set -eu

python -m venv /tmp/venv
. /tmp/venv/bin/activate

pip install --quiet build
python -m build --wheel --outdir /tmp/dist .

pip install "$(ls -1 /tmp/dist/alectryon*.whl)[full]"
python recipes/tests/doctests.py
python recipes/tests/unit.py
python recipes/tests/end_to_end.py
