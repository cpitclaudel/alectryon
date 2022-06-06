========================
 Errors from coqc -time
========================

An incomplete file is an error with ``coqc -time``.
To compile::

   alectryon --coq-driver=coqc_time --backend webpage -o /dev/null \
       coqc_time_error.rst > coqc_time_error.out 2>&1; \
     echo "exit: $?" >> coqc_time_error.out; \
     sed -i 's/in file [^:]*//' coqc_time_error.out
       # ReST → HTML; produces ‘coqc_time_error.out’

.. coq::

   Goal True.
