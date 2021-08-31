===========================================
 Misc commands that don't have other tests
===========================================

To compile::

   alectryon misc.rst # reST → HTML; produces ‘misc.html’

.. exercise:: Commutativity of addition
   :difficulty: 1

   .. coq::

      Goal forall x y: nat, x + y = y + x.
