Line numbers
============

This file checks line and column numbers in Rocq error messages.

To run::

   alectryon linums.rst -o /dev/null 2> linums.rst.out; \
     echo "exit: $?" >> linums.rst.out
       # RST → HTML + errors; produces ‘linums.rst.out’

.. note::

   .. coq::

      Definition warning := forall {a: nat}, a >= 0.

   .. coq::

      Definition error :=
        1 + false.
