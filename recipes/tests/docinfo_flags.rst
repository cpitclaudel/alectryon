=========================
 SerAPI flags in docinfo
=========================

To compile::

   alectryon docinfo_flags.rst -o - >/dev/null; echo "exit: $?" > docinfo_flags.txt
     # reST + assertions; produces ‘docinfo_flags.txt’

:date: August 30, 2021
:alectryon/serapi/args: -I . -R ../recipes/ custom_flag_recipes
:alectryon/serapi/args: -Q ../alectryon/ custom_flag_alectryon_tests

.. topic:: Checking for SerAPI flags

   Calling :mquote:`.io#lp.s(Print LoadPath).in` (:mref:`.io#lp.s(Print LoadPath)`) prints all know paths, and the assert below checks that the expected paths are found.

.. massert:: .io#lp

   .s(LoadPath).msg{*custom_flag_recipes*alectryon/recipes*}
   .s(LoadPath).msg{*alectryon*custom_flag_alectryon_tests*}

.. coq::
   :name: lp

   Print LoadPath. (* .in *)

.. coq::

   Check nat.
