Line numbers
============

This file checks line and column numbers in Rocq error messages.

To run::

   alectryon linums.rst -o /dev/null 2> linums.rst.out; \
     echo "exit: $?" >> linums.rst.out
       # RST → HTML + errors; produces ‘linums.rst.out’

.. note:: Rocq

   .. coq::

      Definition n₀ := 0.
      Definition αβγ := 1.
      Notation "'鳥'" := 0.
      Notation "'✗✗✗'" := false.
      Infix "∧" := and (at level 80).

   .. coq::

      Definition warning :=
        n₀ + 鳥 + αβγ = αβγ ∧ forall {ん: nat}, ん >= 0.

   .. coq::

      Definition error :=
        αβγ - 鳥 + ✗✗✗ = n₀.
