(*|
=====================
 Custom highlighting
=====================

:alectryon/pygments/tacn: legacy_highlighting_test
:alectryon/pygments/coq/tacn-solve: highlighting_test
|*)

(* The old syntax didn't require the /coq/ part *)
Ltac legacy_highlighting_test := simpl.
Ltac highlighting_test := trivial.

Goal True.
  legacy_highlighting_test.
  highlighting_test.
Qed.
