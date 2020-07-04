(*|
Conjunction
===========

To prove that `P /\ Q` holds, we must present evidence for both `P` and `Q`.  Thus, it makes sense to define a proof object for `P /\ Q` as consisting of a **pair** of two proofs: one for `P` and another one for `Q`. This leads to the following definition.
|*)

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

(*|
Notice the similarity with the definition of the `prod` type, given in chapter `Poly <Poly.html>`_; the only difference is that `prod` takes `Type` arguments, whereas `and` takes `Prop` arguments.
|*)

Print prod. (* .unfold *)

(*|
This similarity should clarify why `destruct` and `intros` patterns can be used on a conjunctive hypothesis.  Case analysis allows us to consider all possible ways in which `P /\ Q` was proved -- here just one (the `conj` constructor). […]
|*)

Lemma and_comm :
  forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - (* → *) intros [HP HQ]. split.
    { apply HQ. } { apply HP. }
  - (* ← *) intros [HP HQ]. split.
    { apply HQ. } { apply HP. }
Qed.

(*|
.. exercise:: conj_fact
   :difficulty: 2
   :optional:

   Construct a *proof of the following proposition:
|*)

Definition conj_fact :
  forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  (* REPLACE THIS LINE WITH ":= …." *).
Admitted.
