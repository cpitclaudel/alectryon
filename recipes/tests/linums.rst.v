(*|
Line numbers
============

This file checks line and column numbers in Rocq error messages.

To run::

   alectryon linums.rst.v --frontend coq -o /dev/null 2> linums.v.out; \
     echo "exit: $?" >> linums.v.out
       # Plain Coq → HTML + errors; produces ‘linums.v.out’

   alectryon linums.rst.v -o /dev/null 2> linums.rst.v.out; \
     echo "exit: $?" >> linums.rst.v.out
       # Coq+RST → HTML + errors; produces ‘linums.rst.v.out’

.. note:: Rocq

   This block is nested and the ``..coq::`` directive
   is implicit in the reST file:
|*)

Definition n₀ := 0.
Definition αβγ := 1.
Notation "'鳥'" := 0.
Notation "'✗✗✗'" := false.
Infix "∧" := and (at level 80).

(*||*)

Definition warning :=
  n₀ + 鳥 + αβγ = αβγ ∧ forall {ん: nat}, ん >= 0.

(*||*)

Definition error :=
  αβγ - 鳥 + ✗✗✗ = n₀.
