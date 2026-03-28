========================
 Parsing errors in reST
========================

To run::

   alectryon unterminated.rst -o /dev/null > unterminated.rst.out 2>&1; \
     echo "exit: $?" >> unterminated.rst.out
       # Coq → reST; produces ‘unterminated.rst.out’

.. coq::

   (* "This string is unterminated. *)
