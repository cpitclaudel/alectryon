(* Tracking goal names: *)

(* To build:
      alectryon --frontend coq goal_names.v # Coq → HTML; produces ‘goal_names.v.html’ *)

Goal forall b: bool, b = b.
  destruct b; [ refine ?[true] | refine ?[false] ].
  all: reflexivity.
Qed.
