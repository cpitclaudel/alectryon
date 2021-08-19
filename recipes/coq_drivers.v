(*|
===============================================
 Using ``coqc`` to compile Alectryon documents
===============================================

The normal way to compile Coq documents with Alectryon is to use ``serapi``.
When this is not possible, however, you can use ``coqc`` with (much) reduced
functionality: Alectryon will be able to parse individual sentences and refer to
them, but not to compute goals and messages.  To compile with ``coqc``, pass
``--coq-driver={sertop|sertop_noexec|coqc_time}`` to Alectryon::

   alectryon --coq-driver=sertop coq_drivers.v -o coq_drivers.html
     # Coq+reST → HTML; produces ‘coq_drivers.html’

   alectryon --coq-driver=coqc_time coq_drivers.v -o coq_drivers.coqc.html
     # Coq+reST → HTML; produces ‘coq_drivers.coqc.html’

   alectryon --coq-driver=sertop_noexec coq_drivers.v -o coq_drivers.noexec.html
     # Coq+reST → HTML; produces ‘coq_drivers.noexec.html’

.. coq:: none
|*)

From Coq Require Import List.
Open Scope list_scope.

(*||*)

Lemma fold_left_app : forall {A B} (f: A -> B -> A) (l l': list B) a,
    fold_left f (l ++ l') a = fold_left f l' (fold_left f l a).
Proof.
  induction l; simpl; auto.
Qed.

Goal forall {A B} (f: A -> B -> B) (l: list A) b,
    fold_right f b l = fold_left (fun acc b => f b acc) (rev l) b.
Proof.
  intros.
  induction l; simpl; intros. (* .unfold *)
  - reflexivity.
  - rewrite IHl, fold_left_app; simpl; auto.
Qed.

Check nat.

(*|
Limited reference functionality is still available: :mref:`.s(Proof)`, :mref:`.s(Goal).in`, :mquote:`.s(Goal).in`.
|*)
