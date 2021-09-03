========================
 Parsing errors in reST
========================

To run::

   alectryon unterminated.rst --coq-driver sertop_noexec > unterminated.rst.out 2>&1; \
     echo "exit: $?" >> unterminated.rst.out
       # Coq → reST; produces ‘unterminated.rst.out’

.. coq::

   (* "This string is unterminated. *)
