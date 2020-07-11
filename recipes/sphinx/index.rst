.. alectryon-demo documentation master file, created by
   sphinx-quickstart on Sat Jul 11 15:24:03 2020.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Welcome to alectryon-demo's documentation!
==========================================

.. toctree::
   :maxdepth: 2
   :caption: Contents:

.. coq::

   Definition example_from_sphinx: nat. (* .unfold *)
   Proof. (*. no-goals *)
     simple apply Nat.add.
     exact 1.
     exact 2.
   Defined.

   Print example_from_sphinx. (* .unfold *)

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
