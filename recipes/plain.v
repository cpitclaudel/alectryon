(* Converting unannotated Coq files *)

(* Alectryon's default is to treat Coq files as mixed Coq + reStructuredText
   files ‘--frontend coq+rst’, but you can use ‘--frontend coq’ all comment
   processing:

      alectryon --frontend coq plain.v # Coq → HTML; produces ‘plain.v.html’

   Conversion from plain Coq to LaTeX isn't supported yet (use coq+rst):

      # alectryon --frontend coq --backend latex plain.v # Coq → LaTeX; produces ‘plain.v.tex’ *)

Require Import List.

Lemma skipn_app {A}:
  forall (l1 l2: list A) n,
    n <= List.length l1 ->
    skipn n (List.app l1 l2) =
    List.app (skipn n l1) l2.
Proof.
  induction l1.
  - destruct n.
    all: cbn.
    + reflexivity.
    + inversion 1.
  - destruct n. cbn.
    + reflexivity.
    + intros. apply IHl1.
      Check le_S_n.
      apply le_S_n.
      match goal with
      | [ H: _ <= _ |- _ ] => simpl in H
      end.
      assumption.
Qed.
