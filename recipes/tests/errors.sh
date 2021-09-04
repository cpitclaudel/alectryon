#!/usr/bin/env bash

# This file tests various fatal errors raised from the command line.
# To run:
#   $ PYTHON="python " ALECTRYON="alectryon " bash errors.sh 2>&1 | sed '/^usage\|^ \{10,\}/d' > errors.sh.out
#     Errors and warnings; produces ‘errors.sh.out’

set -v
$PYTHON -m alectryon.literate -; echo $?
$PYTHON -m alectryon.literate xyz.unsupported; echo $?
$ALECTRYON xyz.unsupported; echo $?
$ALECTRYON xyz.v -o xyz.unsupported; echo $?
$ALECTRYON xyz.v.json -o xyz.rst; echo $?
$ALECTRYON a.v.json b.v.json -o c.v.json; echo $?
$ALECTRYON a.v.json --stdin-filename b.v.json; echo $?
$ALECTRYON a.v.json --mark-point not_an_int ⊙; echo $?
