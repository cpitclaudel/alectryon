def test {n : ℕ} : n + n = 2 * n :=
begin
  induction n,
  { refl },
  rw [nat.add_succ, nat.succ_add, nat.mul_succ],
  rwa n_ih
end

#check nat

#print test

#asd 123

def test {n : ℕ} : n + n = 2 * n :=
begin
  induction n,
  { refl },
  rw [nat.add_succ, nat.succ_add, nat.mul_succ],
  rwa n_ih
end

def case_command_test {a b : ℕ} : a + b = b + a :=
begin
  induction a with k hk; induction b with m hm,
  { refl },
  { simp [nat.zero_add] },
  { simp [nat.zero_add] },
  rw nat.add_comm  
end
