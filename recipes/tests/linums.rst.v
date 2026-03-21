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

.. note::

   This block is nested and the directive is implicit in the reST file:
|*)

Definition warning := forall {a: nat}, a >= 0.

Definition error :=
  1 + false.
