===================
 Errors from Lean3
===================

Lean 3 doesn't support file with errors::

   alectryon --backend webpage -o /dev/null \
       lean3_error.rst > lean3_error.out 2>&1; \
     echo "exit: $?" >> lean3_error.out; \
     sed -i 's/^\( *\).*\?\([.]lean:\)/\1...\2/g' lean3_error.out; \
     sed -i 's|/home/.*/bin/||g' lean3_error.out
       # ReST → HTML; produces ‘lean3_error.out’

.. lean3::

   #asd 1
