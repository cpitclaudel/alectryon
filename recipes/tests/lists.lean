/- To compile:
     alectryon lists.lean -o lists.lean.html
       # Lean → HTML; produces ‘lists.lean.html’ -/

variables {α β : Type*}

open list

theorem mem_map_of_mem (f : α → β)
  {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
begin
  induction l with b l' ih,
  {cases h},
  {cases h with h,
    {apply or.inl, rw h},
    {exact or.inr (ih h)}}
end

theorem exists_of_mem_map {f : α → β}
  {b : β} {l : list α} (h : b ∈ map f l) :
    ∃ a, a ∈ l ∧ f a = b :=
begin
  induction l with c l' ih,
  { cases h },
  { cases (eq_or_mem_of_mem_cons h) with h h,
    { exact ⟨c, mem_cons_self _ _, h.symm⟩ },
    { cases ih h with a ha₁,
      exact ⟨a, mem_cons_of_mem _ ha₁.1, ha₁.2⟩ }}
end

@[simp] theorem mem_map {f : α → β} {b : β} {l : list α}
  : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
⟨exists_of_mem_map,
 λ ⟨a, la, h⟩, by rw [← h]; exact mem_map_of_mem f la⟩

lemma forall_mem_map_iff {f : α → β} {l : list α} {P : β → Prop} :
  (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) :=
begin
  split,
  { assume H j hj,
    exact H (f j) (mem_map_of_mem f hj) },
  { assume H i hi,
    cases mem_map.1 hi with j hj,
    rw ← hj.2,
    exact H j hj.1 }
end
