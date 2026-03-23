================================
 Rocq flags on the command line
================================

To compile::

   alectryon cli_flags.rst -o /dev/null \
       -I . -R ../recipes/ custom_flag_R \
       -Q ../etc/ custom_flag_Q; \
     echo "exit: $?" > cli_flags.txt
        # reST + assertions; produces ‘cli_flags.txt’

.. massert:: .io#lp

   .s(LoadPath).msg{*custom_flag_R*/recipes*}
   .s(LoadPath).msg{*custom_flag_Q*/etc*}

.. coq::
   :name: lp

   Print LoadPath.
