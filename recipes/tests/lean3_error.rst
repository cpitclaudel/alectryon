===================
 Errors from Lean3
===================

Lean 3 doesn't support file with errors::

   alectryon lean3_error.rst --backend webpage -o /dev/null 2>&1 | \
       sed 's/^\( *\).*\?\([.]lean:\)/\1...\2/g' > lean3_error.out; \
     echo "exit: $?" >> lean3_error.out
       # ReST → HTML; produces ‘lean3_error.out’

.. lean3::

   #asd 1
