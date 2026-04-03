#!/usr/bin/env sh
# Run ELisp tests in an isolated Emacs environment.
# Packages get cached in deps/elisp/.
set -eu

root="$(cd "$(dirname "$0")/.."; pwd)"
elisp_dir="$root/deps/elisp"
mkdir -p "$elisp_dir"

exec emacs --batch -Q \
     --eval "(setq user-emacs-directory \"$elisp_dir/\")" \
     -l etc/elisp/alectryon-tests.el \
     -f ert-run-tests-batch-and-exit
