-- Queries:
#check nat  #check bool

-- Proofs:
example (p q r : Prop) : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
  intro H,
  apply and.intro,
  apply (and.elim_right H),
  apply (and.elim_left H),
  intro H,
  apply and.intro,
  apply (and.elim_right H),
  apply (and.elim_left H),
end
