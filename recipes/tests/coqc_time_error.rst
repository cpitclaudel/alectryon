========================
 Errors from coqc -time
========================

An incomplete file is an error with ``coqc -time``.
To compile::

   alectryon --coq-driver=coqc_time coqc_time_error.rst > coqc_time_error.out 2>&1; \
     echo "exit: $?" >> coqc_time_error.out
       # ReST → HTML; produces ‘coqc_time_error.out’

.. coq::

   Goal True.
