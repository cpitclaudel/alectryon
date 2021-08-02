==============================
 reST → Coq translation tests
==============================

To compile::

   $ alectryon literate.v --backend rst # Coq → reST; produces ‘literate.rst’

.. coq::

   Goal True /\ True.

The last header is needed (to avoid putting `Goal True` in the ``To compile::`` block) but here we don't need one:

.. coq::

     split.

This one is needed because it includes a ``:name:``:

.. coq::
   :name: exact

     exact I.

.. note:: This note includes two Coq fragments:

   .. coq::

        idtac "This comment is part of the note".

   The last header is needed (to include the comment in the note) but here we don't need one.  The next one (after the note) is needed to exit the note.  The ``(*||*)`` comment is needed too, because otherwise the two blocks would get merged into one):

   .. coq::

        idtac "This comment is part of the note".

.. coq::

     (* This comment isn't part of the note *)

.. coq::

     idtac.

We also want to correctly handle ``.. coq::`` blocks in comments:

.. coq::

   idtac

This can't happen from translating a reST file, but it can happen from a user adding such a block directly.

.. coq::

   Qed.
