(*|
================================
 A chapter stored as a Coq file
================================
|*)

Compute ((fun (n: nat) (opt: option nat) (eq: opt = Some n) => n)
           _ (Some 3) eq_refl).
