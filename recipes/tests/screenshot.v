From Coq Require Import Utf8 ZArith. (* .none *)
Open Scope
(* To compile: alectryon screenshot.v
     # Coq → HTML; produces ‘screenshot.html’ *) (* .none *)
     Z_scope. (* .none *)
Goal forall x y, x + y = x - y -> y = 0. (* .unfold *)
  intros x y Heq. (* .unfold *)
  Search (?x + _ = ?x + _ -> _). (* .unfold .no-goals *)
  apply Z.add_reg_l in Heq. (* .unfold *)
  destruct y; simpl in *.
  all: reflexivity || discriminate.
Qed.
