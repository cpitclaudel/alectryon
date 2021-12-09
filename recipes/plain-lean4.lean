/- To compile:
     alectryon --frontend lean4 plain-lean4.lean # Lean → HTML; produces ‘plain-lean4.lean.html’ -/

-- Queries:
#check Nat  #check Bool

-- Proofs:
theorem test (p q : Prop) (hp : p) (hq : q): p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact hq
    . exact hp
  . intro h
    apply And.intro
    . exact hp
    . exact hq
