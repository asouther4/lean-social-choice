import basic
import data.list.chain

open list
variables {α : Type*}
variables {r : α → α → Prop} {a b : α}

lemma chain.induction' (p : α → Prop)
  (l : list α) (h : chain r a l)
  (hb : last (a :: l) (cons_ne_nil _ _) = b)
  (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (first : p a) : ∀ i ∈ a :: l, p i :=
begin
  induction l generalizing a,
  { cases hb,
    simp [first] },
  { rw chain_cons at h,
    rintro _ (rfl | _), { exact first, },
    exact l_ih h.2 hb (carries h.1 first) _ H, }
end

lemma chain.induction_head' (p : α → Prop)
  (l : list α) (h : chain r a l)
  (hb : last (a :: l) (cons_ne_nil _ _) = b)
  (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (first : p a) : p b :=
begin
  apply (chain.induction' p l h hb carries first) b,
  rw ← hb, 
  exact list.last_mem (cons_ne_nil _ _),
end 

lemma exists_chain_of_relation_trans_gen (h : relation.trans_gen r a b) :
  ∃ l ≠ list.nil, chain r a l ∧ last (a :: l) (cons_ne_nil _ _) = b :=
begin
  apply relation.trans_gen.head_induction_on h,
  { intros c hcb,
    refine ⟨[b], cons_ne_nil _ _, _, rfl⟩,
    simpa only [and_true, chain_cons, chain.nil], },
  { intros c d e t ih,
    obtain ⟨l, hl₁, hl₂, hl₃⟩ := ih,
    refine ⟨d :: l, cons_ne_nil _ _, chain.cons e hl₂, _⟩,
    rwa last_cons_cons, }
end

/-
lemma relation_trans_gen_of_exists_chain {l} (hl₁ : l ≠ list.nil)
  (hl₂ : chain r a l) (hl₃ : last (a :: l) (cons_ne_nil _ _) = b)  :
  relation.trans_gen r a b :=
begin
  -- refine chain.induction_head' _ l hl₁ hl₂ _ _,
end
-/