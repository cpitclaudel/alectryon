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

.. lean4::

  open Nat

  def customSum : Nat -> Nat
    | 0      => 0
    | succ n => succ n + customSum n

  #eval customSum 10

  namespace Nat
    theorem mul_two : ∀ n : Nat, 2 * n = n + n := by
      intros n
      induction n with
      | zero => simp
      | succ n n_ih =>
        rw [← Nat.add_one, Nat.left_distrib, n_ih]
        simp [Nat.add_assoc, Nat.add_comm 1]

    theorem gauss : ∀ n : Nat, 2 * customSum n = n * (n + 1) := by
      intros n
      induction n with
      | zero => simp [customSum]
      | succ n n_ih =>
        simp [customSum]
        simp [Nat.left_distrib]
        rw [n_ih, ← Nat.add_one]
        simp [Nat.left_distrib, Nat.right_distrib,
              Nat.mul_one, Nat.one_mul, Nat.mul_two]
        rw [Nat.add_comm]
        simp [Nat.add_assoc]
        rw [Nat.add_one, Nat.add_comm 1]
  end Nat