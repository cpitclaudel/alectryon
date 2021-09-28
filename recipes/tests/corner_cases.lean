/- To compile:
     alectryon corner_cases.lean -o corner_cases.lean.html
       # Lean → HTML; produces ‘corner_cases.lean.html’ -/

example : true := begin
  trivial

--- asda
end

example : true := begin
    skip, exact by trivial, done
end

example : true :=
begin
  exact by {
    skip,
    by_contra,
    apply h,
    exact trivial
  },
  skip
end

#check 1
#check (1 +
        1 +
        1)

theorem t0 : true -> true :=
  by { intro, exact true.intro }

theorem t1 : true -> true :=
  begin
    -- ⊢ true → true
    intro,
    -- ᾰ : true ⊢ true
    exact true.intro
  end

-- theorem x : "a" = 1.

theorem t2 : true -> true -> true :=
  begin
    repeat { intro } ,
    sorry
  end

theorem t3 : true -> true -> true :=
  begin
    exact by { repeat { intro }, assumption }
  end

theorem t4 : true -> true -> true :=
  by { repeat { intro }, admit }

example : true := by exact true.intro
example : true := by trivial

example (a b c : ℕ) (H1 : a = b + 1) (H2 : b = c) : a = c + 1 :=
calc a = b + 1 : by exact H1
...    = c + 1 : by rw [ by exact H2 ]

example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
  conv
  begin          -- | a * (b * c) = a * (c * b)
    to_lhs,      -- | a * (b * c)
    congr,       -- 2 goals : | a and | b * c
    skip,        -- | b * c
    rw nat.mul_comm -- | c * b
  end
end

example : true := begin
    skip <|> skip, /- Second skip not executed -/
    done <|> skip,
    trivial
end

example (n : ℕ) : n = n := by {
    induction n,
    simp,
    simp
}

example (n : ℕ) : n = n :=
begin
  induction n,
  simp,
  simp
end

example (n : ℕ) : n = n := by induction n ; simp

-- grouped as (((skip ; skip) ; induction n) ; skip) ; simp
example (n : ℕ) : n = n :=
  by skip ; skip ; induction n ; skip ; simp

example (n : ℕ) : n = n := begin
    induction n, { simp },
    simp
end

example : ∀ (n a : ℕ), n = n := begin
    repeat { intro }, simp
end

example : true := begin
    try { done }, try { trivial }
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
  { have hpq : p ∧ q,
      split ; assumption ,
    left, exact hpq },
  have hpr : p ∧ r,
    split ; assumption,
  right,
  exact hpr
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
begin
  split,
  all_goals { try { split } },
  all_goals { assumption }
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
begin
  repeat { all_goals { split <|> assumption } }
end

example :true := begin
  skip, skip; trivial
end

example (n m k : ℕ) (h1 : n = m) (h2 : m = k): (n = k) :=
begin
    rw [show n = m, by assumption, show m = k, by assumption]
end

theorem sub_le_sub_left {n m : ℕ} (k) (h : n ≤ m) : k - m ≤ k - n :=
begin
  induction h; [refl, exact le_trans (nat.pred_le _) h_ih]
end


example : true := by {
  try { trivial }
}

example : true := by begin
  try begin trivial end
end

-- grouped as done <|> (done <|> trivial)
example : true := by done <|> done <|> trivial

-- unexecuted tactic at end
example : true := by { trivial ; done }

-- special notation
example (n : nat) : true :=
   by induction n ; [skip, skip]; [trivial, trivial]

example : true := begin
skip,
trivial, -- trailing comma
end

-- trailing comma
example : true := by { skip ; trivial, }

example : true := by { { skip ; [skip, skip] } <|> trivial}

example : true := by { {{{{ skip ; [skip, skip] }}}} <|> trivial}


-- { } block with no executed children
-- there is no first goal to focus on
example : true := begin { trivial , { skip, skip } } <|> trivial end


-- trailing comma
example : true := begin { skip ; trivial, } end

example : true := begin { { skip ; [skip, skip] } <|> trivial} end

example : true := begin { {{{{ skip ; [skip, skip] }}}} <|> trivial} end
