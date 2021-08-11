(*|
==============================
 reST → Coq translation tests
==============================

To compile::

   $ alectryon literate.rst --backend coq # reST → Coq; produces ‘literate.v’

Code blocks
===========
|*)

Goal True /\ True.

(*|
The last header is needed (to avoid putting `Goal True` in the ``To compile::`` block) but the next one is superfluous:
|*)

  split.

(*|
This one is needed because it includes a ``:name:``:

.. coq::
   :name: exact
|*)

  exact I.

(*|
.. note:: This note includes two Coq fragments:

   .. coq::
|*)

  idtac "This comment is part of the note".

(*|
   The last header is needed (to include the comment in the note) but the next one is superfluous.  The one after the note is needed, but not the one after that (though a ``(\ *||*\ )`` comment is still needed, because otherwise the two blocks would get merged into one):
|*)

  idtac "This comment is part of the note".

(*|
.. coq::
|*)

  (* This comment isn't part of the note *)

(*||*)

Qed.

(*|
Comments and strings
====================

Coq comment markers that appear within doc comments (\ *like this one*\ ) must be escaped, especially if they aren't well-parenthesized (like *this*\ ) (\ *or this*, for example).
|*)

(* This comment doesn't need "*)" escaping though, even if ProofGeneral mishighlights it *)

(*|
Strings can be tricky too:
|*)

Require Import String.
Open Scope string_scope.

Definition a := "a""b""c\n\n\n".
Print a.
