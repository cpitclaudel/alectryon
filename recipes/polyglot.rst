========================
 Multi-prover documents
========================

Alectryon documents can use multiple provers.  Inputs for each prover are processed independently.

To compile::

   alectryon polyglot.rst
       # reST+… → HTML;  produces ‘polyglot.html’

.. coq::

   Require Import Arith.

   Lemma mul_comm :
     forall a b: nat, a * b = b * a.
   Proof.
     induction a; simpl.
     - induction b; simpl; congruence.
     - induction b; simpl.
       + rewrite IHa; reflexivity.
       + rewrite <- IHb, IHa.
         simpl. rewrite IHa.
         rewrite !Nat.add_assoc.
         rewrite (Nat.add_comm b a).
         reflexivity.
   Qed.

.. lean3::

   open nat

   def Sum : nat → nat
   | 0        := 0
   | (succ n) := (succ n) + Sum n

   #eval (Sum 10)

   namespace nat
     lemma mul_two: forall n: nat, 2 * n = n + n :=
     begin
       intros n, induction n,
       { refl },
       { rw [← nat.add_one, nat.left_distrib, n_ih],
         change (2 * 1) with (1 + 1),
         simp [nat.add_assoc, nat.add_comm 1], }
     end
   end nat

   lemma gauss: forall n: nat, 2 * Sum n = n * (n + 1) :=
   begin
     intros n,
     induction n with n ih; simp [Sum],
     { refl },
     { simp [nat.left_distrib],
       rw [ih, ← nat.add_one],
       simp [nat.left_distrib, nat.right_distrib,
             nat.mul_one, nat.one_mul, nat.mul_two];
         change (1 * 1) with 1; change (2 * 1) with (1 + 1);
         rw [nat.add_comm]; simp [nat.add_assoc] },
   end
