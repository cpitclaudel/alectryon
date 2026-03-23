=======================
 Rocq flags in docinfo
=======================

To compile::

   alectryon docinfo_flags.rst -o /dev/null; echo "exit: $?" > docinfo_flags.txt
     # reST + assertions; produces ‘docinfo_flags.txt’

:date: August 30, 2021
:alectryon/rocq/args: -I . -R ../recipes/ custom_flag_R
:alectryon/rocq/args: -Q ../etc/ custom_flag_Q

.. topic:: Checking for Rocq flags

   Calling :mquote:`.io#lp.s(Print LoadPath).in` (:mref:`.io#lp.s(Print LoadPath)`) prints all know paths, and the assert below checks that the expected paths are found.

.. massert:: .io#lp

   .s(LoadPath).msg{*custom_flag_R*/recipes*}
   .s(LoadPath).msg{*custom_flag_Q*/etc*}

.. coq::
   :name: lp

   Print LoadPath. (* .in *)

.. coq::

   Check nat.
