==================================
 SerAPI flags on the command line
==================================

To compile::

   alectryon cli_flags.rst -o - >/dev/null \
       --debug --traceback --expect-unexpected --long-line-threshold=-1 \
       -I . -R ../recipes/ custom_flag_recipes \
       -Q ../alectryon/ custom_flag_alectryon_tests; \
     echo "exit: $?" > cli_flags.txt
        # reST + assertions; produces ‘cli_flags.txt’

.. massert:: .io#lp

   .s(LoadPath).msg{*custom_flag_recipes*alectryon/recipes*}
   .s(LoadPath).msg{*alectryon*custom_flag_alectryon_tests*}

.. coq::
   :name: lp

   Print LoadPath. (* .in *)
