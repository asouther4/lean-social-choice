import data.set.finite
import tactic

section

/-! ### General lemmas about finsets; don't involve social choice theory -/

variables {α : Type*} {s : finset α} {a b : α}

namespace finset

lemma exists_second_distinct_mem (hs : 2 ≤ s.card) (ha : a ∈ s) :
  ∃ b ∈ s, b ≠ a :=
begin
  classical,
  have hpos : 0 < (s.erase a).card,
  { rw card_erase_of_mem ha,
    exact zero_lt_one.trans_le (nat.pred_le_pred hs) },
  cases card_pos.mp hpos with b hb,
  cases mem_erase.mp hb with hne H,
  exact ⟨b, H, hne⟩,
end

lemma exists_third_distinct_mem (hs : 2 < s.card) (ha : a ∈ s) (hb : b ∈ s) (h : a ≠ b) : 
  ∃ c ∈ s, c ≠ a ∧ c ≠ b :=
begin
  classical,
  have hpos : 0 < ((s.erase b).erase a).card,
  { simpa only [card_erase_of_mem, mem_erase_of_ne_of_mem h ha, hb]
      using nat.pred_le_pred (nat.pred_le_pred hs) }, 
  cases card_pos.mp hpos with c hc,
  simp_rw mem_erase at hc,
  exact ⟨c, hc.2.2, hc.1, hc.2.1⟩,
end

lemma nonempty_of_mem (ha : a ∈ s) : s.nonempty := 
nonempty_of_ne_empty $ ne_empty_of_mem ha

end finset

namespace relation

lemma forall_exists_trans_gen (R : α → α → Prop) (hR : ∀ a ∈ s, ∃ b ∈ s, R b a) :
  ∀ a ∈ s, ∃ b ∈ s, trans_gen R b a :=
λ a ha, let ⟨b, hb, h⟩ := hR a ha in ⟨b, hb, trans_gen.single h⟩

end relation

end

open relation finset

-- We think of social states as type `σ` and inidividuals as type `ι`
variables {σ ι : Type*} {x y x' y' z a b : σ} {R R' : σ → σ → Prop}

/-! ### Basic definitions and properties -/

--now, we have to define the 'strict' preference relation P
def P (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ ¬R y x -- accepts a relation and two social states

lemma P_iff_of_iff (h₁ : R a b ↔ R' a b) (h₂ : R b a ↔ R' b a) : 
  (P R a b ↔ P R' a b) ∧ (P R b a ↔ P R' b a) :=
by simp_rw [P, h₁, h₂, iff_self, and_self]

-- 'indifference' I
def I (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ R y x

-- Sen lemma 1*a, (i) - (iv)
lemma I_trans (htrans : transitive R) (h1 : I R x y) (h2 : I R y z) : I R x z :=
⟨htrans h1.1 h2.1, htrans h2.2 h1.2⟩

lemma P_trans_I (htrans : transitive R) (h1 : P R x y) (h2 : I R y z) : P R x z :=
⟨htrans h1.1 h2.1, λ h, h1.2 (htrans h2.1 h)⟩

lemma I_trans_P (htrans : transitive R) (h1 : I R x y) (h2 : P R y z) : P R x z :=
⟨htrans h1.1 h2.1, λ h, h2.2 (htrans h h1.1)⟩

lemma P_trans (htrans : transitive R) (h1 : P R x y) (h2 : P R y z) : P R x z :=
⟨htrans h1.1 h2.1, λ h, h2.2 (htrans h h1.1)⟩

def acyclical (R : σ → σ → Prop) : Prop := 
∀ x : σ, ¬trans_gen (P R) x x

lemma R_of_nP_total (htot : total R) (h : ¬P R y x) : R x y :=
by { cases htot x y with hR hR, exacts [hR, not_and_not_right.mp h hR] }

lemma nP_of_reverseP (h : P R x y) : ¬P R y x :=
not_and_not_right.mpr $ λ n, h.1

example (p : Prop) : false → p := false.rec p

lemma nP_of_nR (h : ¬ R x y) : ¬ P R x y := 
begin
  simp only [P, not_and, not_not],
  intro hyp,
  exact false.rec _ (h hyp),
end


lemma false_of_P_self (h : P R x x) : false := 
(and_not_self _).mp h

--what it means for social states to have the "same order" with respect to two relations
def same_order (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧ (P R x y ↔ P R' x' y') ∧ (P R y x ↔ P R' y' x')

/- Alternate defintion of `same_order`. Can be interchanged with the original, as 
`P_iff_of_iff` shows. -/ -- I'm not certain this is true. I'll explain next time we meet. -Ben
def same_order' (r r' : σ → σ → Prop) (s₁ s₂ s₃ s₄ : σ) : Prop :=
(P r s₁ s₂ ↔ P r' s₃ s₄) ∧ (P r s₂ s₁ ↔ P r' s₄ s₃)

lemma same_order_iff_same_order' (hR : total R) (hR' : total R') : 
  same_order R R' x y x y ↔ same_order' R R' x y x y :=
begin
  refine ⟨λ h, h.2, λ h, ⟨⟨⟨λ hxy, _ , λ hxy, _⟩, ⟨λ hyx, _, λ hyx, _⟩⟩, h⟩⟩;
    obtain ⟨h₁, h₂⟩ := ⟨h.1, h.2⟩; erw [← not_iff_not, not_and, not_not, not_and, not_not] at h₁ h₂,
  { by_cases hyx : R y x,
    { cases hR' x y with hR' hR', { exact hR' },
      exact h₂.mp (imp_intro hxy) hR' },
    { exact (h.1.mp ⟨hxy, hyx⟩).1 } },
  { by_cases hyx : R' y x,
    { cases hR x y with hR hR, { exact hR },
      exact h₂.mpr (imp_intro hxy) hR },
    { exact (h.1.mpr ⟨hxy, hyx⟩).1 } },
  { by_cases hxy : R x y,
    { cases hR' y x with hR' hR', { exact hR' },  
      exact h₁.mp (imp_intro hyx) hR' },
    { exact (h.2.mp ⟨hyx, hxy⟩).1 } },
  { by_cases hxy : R' x y,
    { cases hR y x with hR hR, { exact hR },
      exact h₁.mpr (imp_intro hyx) hR },
    { exact (h.2.mpr ⟨hyx, hxy⟩).1 } }, -- these subproofs are so similar - is there a way we might combine them? -Ben
end

lemma same_order_of_P_P' (hR : P R x y) (hR' : P R' x y) : same_order R R' x y x y := 
⟨⟨⟨λ h, hR'.1, λ h, hR.1⟩, ⟨hR.2.elim, hR'.2.elim⟩⟩, 
  ⟨⟨λ h, hR', λ h, hR⟩, ⟨(nP_of_reverseP hR).elim, (nP_of_reverseP hR').elim⟩⟩⟩

lemma same_order_of_reverseP_P' (hR : P R y x) (hR' : P R' y x) : same_order R R' x y x y :=
⟨⟨⟨hR.2.elim, hR'.2.elim⟩, ⟨λ h, hR'.1, λ h, hR.1⟩⟩, 
  ⟨⟨(nP_of_reverseP hR).elim, (nP_of_reverseP hR').elim⟩, ⟨λ h, hR', λ h, hR⟩⟩⟩

lemma same_order'_comm : same_order' R R' x y x y ↔ same_order' R R' y x y x :=
and.comm

def is_maximal_element (x : σ) (S : finset σ) (R : σ → σ → Prop) : Prop :=
∀ y ∈ S, ¬P R y x

def is_best_element (x : σ) (S : finset σ) (R : σ → σ → Prop) : Prop :=
∀ y ∈ S, R x y

noncomputable def maximal_set (S : finset σ) (R: σ → σ → Prop) : finset σ := 
{x ∈ S | is_maximal_element x S R}

noncomputable def choice_set (S : finset σ) (R: σ → σ → Prop) : finset σ := 
{x ∈ S | is_best_element x S R}

lemma maximal_element_of_maximal_set {r : σ → σ → Prop} {s : finset σ} {x : σ}
  (h : x ∈ maximal_set s r) : 
  is_maximal_element x s r := 
  by simp only [maximal_set, sep_def, mem_filter] at h; exact h.2

lemma maximal_set_of_maximal_element {r: σ → σ → Prop} {s : finset σ} {x : σ}
  (x_in : x ∈ s) (h : is_maximal_element x s r) : 
  x ∈ maximal_set s r := by simp only [maximal_set, sep_def, mem_filter]; exact ⟨x_in, h⟩ 


lemma maximal_subset (s : finset σ) (r : σ → σ → Prop) : 
  maximal_set s r ⊆ s := 
by simp only [maximal_set, sep_def, filter_subset]

lemma is_maximal_of_singleton {R : σ → σ → Prop} (hR : reflexive R )(x : σ) : 
  is_maximal_element x {x} R :=
begin
  intros b b_in,
  simp only [mem_singleton] at b_in,
  rw b_in,
  simp only [P, not_false_iff, and_not_self],
end

lemma maximal_eq_empty_of_empty (R : σ → σ → Prop) :
  maximal_set ∅ R = ∅ := 
by simp only [maximal_set, sep_def, forall_false_left, 
  filter_true_of_mem, implies_true_iff, not_mem_empty]

lemma choice_eq_empty_of_empty (R : σ → σ → Prop) :
  choice_set ∅ R = ∅ := 
by simp only [choice_set, sep_def, forall_false_left, 
  filter_true_of_mem, implies_true_iff, not_mem_empty]

/- For any finite set of alternatives and for any ordering, 
   the choice set is a subset of the maximal set. -/
lemma choice_subset_maximal (S : finset σ) (R : σ → σ → Prop) : 
  choice_set S R ⊆ maximal_set S R := 
begin
  intros a a_in,
  simp only [choice_set, maximal_set, is_best_element, P,
    is_maximal_element, sep_def, mem_filter, not_and, not_not] at *,
  exact ⟨a_in.1, (λ y y_in hy, a_in.2 y y_in)⟩,
end

lemma test_lemma {R : σ → σ → Prop} {S : finset σ} 
  (hS : S.nonempty) (hR : ∀a ∈ S, ∃b ∈ S, R b a) :
  ∃ c ∈ S, trans_gen R c c :=
begin
  replace hR : ∀a ∈ S, ∃b ∈ S, trans_gen R b a :=
    λ a ha, let ⟨b, hb, h⟩ := hR a ha in ⟨b, hb, trans_gen.single h⟩,
  classical, refine finset.induction_on S (by rintro ⟨_, ⟨⟩⟩) _ hS hR,
  rintro a s - IH - hR,
  obtain ⟨b, hb', ba⟩ := hR a (by simp),
  obtain rfl | hb := finset.mem_insert.1 hb', {exact ⟨_, by simp, ba⟩},
  obtain ⟨c, hc, h⟩ := IH ⟨_, hb⟩ (λ d hd, _), {exact ⟨c, by simp [hc], h⟩},
  obtain ⟨e, he, ed⟩ := hR d (by simp [hd]),
  obtain rfl | he := finset.mem_insert.1 he,
  {exact ⟨_, hb, ba.trans ed⟩}, {exact ⟨_, he, ed⟩}
end


lemma cyclical_of_no_highest {R : σ → σ → Prop} {S : finset σ} (hS : S.nonempty) 
  (hR : ∀ a ∈ S, ∃ b ∈ S, trans_gen R b a) :
  ∃ c ∈ S, trans_gen R c c :=
begin
  classical,
  refine finset.induction_on S _ _ hS hR, { rintro ⟨_, ⟨⟩⟩ },
  rintro a s - IH - hR',
  obtain ⟨b, hb', ba⟩ := hR' a (mem_insert_self a s),
  obtain rfl | hb := mem_insert.1 hb', 
  { exact ⟨_, mem_insert_self b s, ba⟩ },
  { obtain ⟨c, hc, h⟩ := IH ⟨_, hb⟩ (λ d hd, _), 
    { exact ⟨c, mem_insert_of_mem hc, h⟩ },
    { obtain ⟨e, he, ed⟩ := hR' d (mem_insert_of_mem hd),
      obtain rfl | he := mem_insert.1 he,
      { exact ⟨_, hb, ba.trans ed⟩ }, 
      { exact ⟨_, he, ed⟩ } } },
end

lemma unknown_name {R : σ → σ → Prop} {S : finset σ} (hS : )

/- Sen's Theorem on the existence of a choice function, from 
  *Social Choice and Collective Welfare* (1970). 

  If a relation is reflexive and total, then acyclicality is a necessary 
  and sufficient condition for a choice function to be defined on every finset `X`. -/
theorem best_elem_iff_acyclical [fintype σ] 
  (htot : total R) : 
  (∀ X : finset σ, X.nonempty → ∃ b ∈ X, is_best_element b X R) ↔ acyclical R := 
begin
  refine ⟨λ h x hx, _, λ h_acyc X X_ne, _⟩,
  { obtain ⟨b, b_in, hb⟩ := h {a ∈ univ | trans_gen (P R) a x ∧ trans_gen (P R) x a} ⟨x, by simpa⟩, -- can we maybe pull this sort of thing out into its own general lemma?
    simp only [true_and, sep_def, mem_filter, mem_univ] at b_in,
    obtain ⟨c, hc₁, hc₂⟩ := trans_gen.tail'_iff.mp b_in.2,
    refine hc₂.2 (hb c _),
    simp [b_in.1.head hc₂, hx.trans_left hc₁] },
  { by_contra h, 
    suffices : ∃ c ∈ X, trans_gen (P R) c c, from let ⟨c, _, hc⟩ := this in h_acyc c hc,
    refine cyclical_of_no_highest X_ne (forall_exists_trans_gen _ (λ a a_in, _)),
    simp only [is_best_element, not_exists, not_forall] at h,
    obtain ⟨b, b_in, hb⟩ := h a a_in,
    exact ⟨b, b_in, ⟨(htot a b).resolve_left hb, hb⟩⟩ },
end

/-! ### Some results about quasi-ordering -/

/-- Quasi-ordering as a structure -/
structure quasi_order (α : Type*) := 
(rel : α → α → Prop)
(refl : reflexive rel)
(trans : transitive rel)

instance (α : Type*) : has_coe_to_fun (quasi_order α) (λ _,  α → α → Prop) := 
  ⟨ λ r, r.rel⟩

lemma quasi_order.eq_coe {α : Type*} (r : quasi_order α) : r.rel = r := rfl


/- Any nonempty, finite set of alternatives has a maximal element 
   with respec to a quasi-order `r`. 
   Sen refers to this as lemma 1*b.  -/
lemma maximal_of_finite_quasi_ordered {α : Type*} (r : quasi_order α) 
  (S : finset α) (hS : S.nonempty) :
  ∃ x ∈ S, is_maximal_element x S r := -- needs golfing!!!
begin
  classical,
  refine finset.induction_on S _ _ hS, { rintro ⟨_, ⟨⟩⟩ },
  rintro a s - IH -,
  by_cases h : s.nonempty,
  { obtain ⟨x, hx⟩ := IH h,
    by_cases hP : P r a x,
    { use a,
      refine ⟨by simp only [mem_insert, true_or, eq_self_iff_true], _⟩,
      intros b b_in,
      by_contra,
      have b_neq : b ≠ a,
      { by_contra h_eq,
        rw h_eq at h,
        exact h.2 (r.refl a), },
      cases hx with x_in hx,
      exact (hx b (mem_of_mem_insert_of_ne b_in b_neq))
        (P_trans r.trans h hP), },
    { use x,
      cases hx with x_in hx,
      refine ⟨mem_insert_of_mem x_in, _⟩,
      intros b b_in,
      by_cases hb : b = a, { rw hb, exact hP, },
      have b_in_s : b ∈ s := mem_of_mem_insert_of_ne b_in hb,
      exact hx b b_in_s, }, },
  { suffices : {a} = insert a s,
    { rw ← this,
      exact ⟨a, mem_singleton_self a, is_maximal_of_singleton r.refl a⟩, },
    simp only [not_nonempty_iff_eq_empty] at h,
    rw h,
    refl, },
end

lemma choice_set_of_singleton {r : σ → σ → Prop} (hr: reflexive r) (x : σ) :
  choice_set {x} r = {x} := 
begin
  ext,
  simp only [choice_set, is_best_element, 
    sep_def, mem_filter, forall_eq, and_iff_left_iff_imp, mem_singleton],
  intro hyp,
  rw hyp,
  exact hr x,
end


/- Suppose `r` is a reflexive relation. Let `x` and `y` be distinct alternatives. 
   Then `x` is strictly better than `y` if an only if `{x}` is the choice set 
   of `{x,y}` with respect to `r`. 
   Sen refers to this as lemma 1*c.  -/
lemma singleton_choice_set [decidable_eq σ] {r : σ → σ → Prop} 
  (x y : σ) (not_eq : x ≠ y) (hR : reflexive r) :
  P r x y ↔ {x} = choice_set {x,y} r :=
begin -- golfing needed
  split,
  { intro h,
    unfold choice_set,
    unfold is_best_element,
    ext, split,
    { intro a_in,
      simp only [sep_def, mem_filter, mem_insert, forall_eq_or_imp, 
        forall_eq, mem_singleton],
      refine ⟨or.inl (mem_singleton.1 a_in), _⟩,
      rw mem_singleton.1 a_in,
      exact ⟨hR x, h.1⟩, },
    { simp only [and_imp, sep_def, mem_filter, mem_insert, 
        forall_eq_or_imp, forall_eq, mem_singleton],
      intro hyp,
      cases hyp,
      { intros hax hay,
        exact hyp, },
      { rw hyp,
        intro hyx,
        exfalso,
        exact h.2 hyx, }, }, },
  { intro hyp,
    split;
    rw ext_iff at hyp,
    { have x_in := (hyp x).1 (mem_singleton_self x),
      simp only [choice_set, is_best_element, sep_def, mem_filter] at x_in,
      refine x_in.2 y _,
      simp only [mem_insert],
      exact or.inr (mem_singleton_self y), }, 
    { have y_not_in := (not_congr (hyp y)).1
        (not_mem_singleton.2 (ne_comm.mp not_eq)),
      simp only [choice_set, is_best_element, sep_def, 
        mem_filter, not_and, mem_insert] at y_not_in,
      specialize y_not_in (by right; exact mem_singleton_self y),
      push_neg at y_not_in,
      rcases y_not_in with ⟨a, ha₁, ha₂⟩,
      cases ha₁,
      { rw ha₁ at ha₂,
        exact ha₂, },
      { exfalso,
        simp only [mem_singleton] at ha₁,
        rw ha₁ at ha₂,
        exact ha₂ (hR y), }, }, },
end

/- Suppose `r` is a quasi-ordering and `S` is a finite set of alternatives.
   Then if the choice set of `S` is nonempty with respect to `R`,
   the choice set is equal to the maximal set. 
   Sen refers to this as lemma 1*d. -/
lemma choice_eq_maximal_of_quasi {r : quasi_order σ}
  (S : finset σ) (hS: (choice_set S r).nonempty) : 
  choice_set S r = maximal_set S r :=
begin
  cases hS with x x_in,
  apply subset.antisymm (choice_subset_maximal S r),
  intros z z_in,
  simp only [choice_set, maximal_set, is_best_element, is_maximal_element,
    sep_def, mem_filter, P, not_and, not_not] at *,
  refine ⟨z_in.1, λ y y_in, _⟩,
  exact r.trans (z_in.2 x x_in.1 (x_in.2 z z_in.1)) (x_in.2 y y_in),
end 

lemma is_maximal_insert_of_nP [decidable_eq σ] 
  {r : σ → σ → Prop} {b x : σ} {s : finset σ}
  (b_not_in : b ∉ s) (hb : ¬ P r b x) :
  x ∈ maximal_set s r → x ∈ maximal_set (insert b s) r :=
begin
  intro x_in,
  simp only [maximal_set, sep_def, mem_filter, mem_insert] at *, 
  refine ⟨or.inr x_in.1, _⟩,
  intros a a_in,
  cases (mem_insert.1 a_in),
  { rw h,
    exact hb },
  { exact x_in.2 a h, },
end

lemma maximal_of_insert_not_maximal [decidable_eq σ] 
  {r : σ → σ → Prop} {b : σ} {s : finset σ}
  (hr : transitive r) (b_not_in : b ∉ s) (hb : b ∉ maximal_set (insert b s) r):
  maximal_set s r = maximal_set (insert b s) r := 
begin
  have : ∃ c ∈ s, P r c b,
    { simp only [maximal_set, is_maximal_element, true_and, 
        sep_def, exists_prop, mem_filter, mem_insert, forall_eq_or_imp, not_and,
        not_not, true_or, eq_self_iff_true, not_forall] at hb,
      have foo : ¬ P r b b,
      { by_contra h,
        exact h.2 h.1, },
      rcases hb foo with ⟨c, c_in, hc⟩,
      exact ⟨c, c_in, hc⟩, },
  rcases this with ⟨c, c_in, hc⟩,
  ext,
  simp only [maximal_set, is_maximal_element, sep_def, mem_filter, 
    mem_insert, forall_eq_or_imp],
  split,
  { intro ha,
    refine ⟨or.inr ha.1, _, ha.2⟩,
    by_contra,
    exact (ha.2 c c_in) (P_trans hr hc h), },
  { intro hyp,
    rcases hyp with ⟨a_in, hba, ha⟩,
    have h_neq : ¬ a = b,
    { by_contra h_eq,
      rw ← h_eq at hc,
      exact (ha c c_in) hc, }, 
    exact ⟨a_in.resolve_left h_neq, ha⟩, },
end

lemma exists_maximal_of_quasi [decidable_eq σ] 
  {a : σ} {S : finset σ} (r : quasi_order σ) (a_in : a ∈ S) : 
  ∃ b ∈ maximal_set S r, r b a := 
begin
  by_cases ha : a ∈ maximal_set S r, { exact ⟨a, ha, r.refl a⟩, },
  by_contra hb,
  push_neg at hb,
  have : ∀ c ∈ {x ∈ S | r x a ∧ x ∉ maximal_set S r}, 
    ∃ d ∈ {x ∈ S | r x a ∧ x ∉ maximal_set S r}, P r d c,
  { intros c c_in,
    simp only [maximal_set, is_maximal_element, 
      sep_def, exists_prop, mem_filter, not_and, not_not, not_forall] at c_in,
    obtain ⟨d, d_in, hdc⟩ := c_in.2.2 c_in.1,
    refine ⟨d, _, hdc⟩,
    simp only [sep_def, mem_filter],
    refine ⟨d_in, r.trans hdc.1 c_in.2.1, _ ⟩,
    by_contra hyp,
    exact (hb d hyp) (r.trans hdc.1 c_in.2.1), },
  have hy : ∃ y ∈ {x ∈ S | r x a ∧ x ∉ maximal_set S r}, trans_gen (P r) y y,
  { replace this : ∀ c ∈ {x ∈ S | r x a ∧ x ∉ maximal_set S r}, 
      ∃ d ∈ {x ∈ S | r x a ∧ x ∉ maximal_set S r}, trans_gen (P r) d c:=
    λ a ha, let ⟨b, hb, h⟩ := this a ha in ⟨b, hb, trans_gen.single h⟩,
    refine cyclical_of_no_highest _ this,
    use a,
    simp only [sep_def, mem_filter],
    exact ⟨a_in, r.refl a, ha⟩, },
  rcases hy with ⟨y, y_in, hy⟩,
  have hP : transitive (P r) := λ x₁ x₂ x₃ h₁ h₂, (P_trans r.trans h₁ h₂),
  rw (trans_gen_eq_self hP) at hy,
  exact false_of_P_self hy,
end

/- Lemma 1*e according to Sen -/
lemma maximal_indiff_iff_choice_eq_maximal' (r : quasi_order σ)
  (S : finset σ) (hS : S.nonempty) : 
  (∀ x y ∈ maximal_set S r, I r x y) ↔ choice_set S r = maximal_set S r :=
begin
  classical,
  split,
  { intro hyp,
    by_contra sets_neq,
    have choice_empty : choice_set S r = ∅,
      { by_contra,
        have sets_eq := choice_eq_maximal_of_quasi S (nonempty_of_ne_empty h),
        exact sets_neq sets_eq }, 
  obtain ⟨x₀, x₀_in, hx₀⟩ := maximal_of_finite_quasi_ordered r S hS,
  have x₀_not_in : x₀ ∉ choice_set S r := by rw choice_empty; exact not_mem_empty x₀,
  simp only [choice_set, is_best_element, sep_def,
   exists_prop, mem_filter, not_and, not_forall] at x₀_not_in,
  obtain ⟨x₁, x₁_in, hx₁⟩ := x₀_not_in x₀_in,
  have x₁_not_in : x₁ ∉ maximal_set S r,
  { by_contra x₁_in_max,
    refine hx₁ (hyp x₀ x₁ _ x₁_in_max).1,
    simp only [maximal_set, sep_def, mem_filter],
    exact ⟨x₀_in, hx₀⟩,},
  have h_no_max : ¬ (∃ x ∈ {z ∈ S | P r z x₁ ∧ z ∉ maximal_set S r }, 
    is_maximal_element x {z ∈ S | P r z x₁ ∧ z ∉ maximal_set S r } r),
  { unfold is_maximal_element,
    push_neg,
    intros x x_in,
    simp only [maximal_set, is_maximal_element, sep_def, 
      mem_filter, not_and, exists_prop, not_not, not_forall] at x_in,
    simp only [sep_def, exists_prop, mem_filter],
    obtain ⟨y, y_in, hy⟩ := (x_in.2.2 x_in.1),
    refine ⟨y, ⟨y_in, (P_trans r.trans hy x_in.2.1),_⟩, hy⟩,
    by_contra y_max, apply hx₁,
    exact (I_trans_P r.trans (hyp x₀ y (maximal_set_of_maximal_element x₀_in hx₀) y_max) 
      (P_trans r.trans hy x_in.2.1)).1, },
  refine h_no_max (maximal_of_finite_quasi_ordered r {z ∈ S | P r z x₁ ∧ z ∉ maximal_set S r } _),
  simp only [maximal_set, is_maximal_element, sep_def, 
    exists_prop, mem_filter, not_and, not_not, not_forall] at x₁_not_in,
  obtain ⟨x₂, x₂_in, hx₂⟩ := x₁_not_in x₁_in,
  use x₂,
  simp only [sep_def, mem_filter],
  refine ⟨x₂_in, hx₂, _⟩,
  by_contra x₂_in_max, apply hx₁,
  refine r.trans (hyp x₀ x₂ (maximal_set_of_maximal_element x₀_in hx₀) x₂_in_max).1 hx₂.1, }, 
  { intro hyp,
    rw ← hyp,
    intros x y x_in y_in,
    simp only [choice_set, sep_def, mem_filter] at *,
    exact ⟨x_in.2 y y_in.1, y_in.2 x x_in.1⟩, },
end

/- Lemma 1*e according to Sen -/
lemma maximal_indiff_iff_choice_eq_maximal (r : quasi_order σ)
  (S : finset σ) (hS : S.nonempty) : 
  (∀ x y ∈ maximal_set S r, I r x y) ↔ choice_set S r = maximal_set S r :=
begin
  classical,
  split,
  { refine finset.induction_on S _ _,
    { intro h,
      rw [maximal_eq_empty_of_empty r, choice_eq_empty_of_empty r] },
    { intros a s a_not_in IH h,
      by_contra sets_neq,
      have choice_empty : choice_set (insert a s) r = ∅,
      { by_contra,
        have sets_eq := choice_eq_maximal_of_quasi (insert a s) (nonempty_of_ne_empty h),
        exact sets_neq sets_eq }, 
      by_cases ha : a ∈ maximal_set (insert a s) r,
      { have h_insert : maximal_set (insert a s) r = insert a (maximal_set s r),
        { ext y,
          split,
          { simp only [maximal_set, is_maximal_element, 
              sep_def, mem_filter, mem_insert, forall_eq_or_imp],
            intro hyp,
            cases hyp.1 with y_eq y_in, 
            left, exact y_eq,
            right, exact ⟨y_in, hyp.2.2⟩, },
          { intro hyp,
            by_cases y_eq : y = a,
            { simp only [maximal_set, is_maximal_element, 
                sep_def, mem_filter, mem_insert, forall_eq_or_imp],
              refine ⟨or.inl y_eq, _ ⟩,
              rw y_eq,
              simp only [maximal_set, is_maximal_element, 
                true_and, sep_def, mem_filter, mem_insert, forall_eq_or_imp, true_or,
                eq_self_iff_true] at ha,
              exact ha, },
            { simp only [maximal_set, sep_def, mem_filter, mem_insert],
              have y_in : y ∈ maximal_set s r := (mem_insert.1 hyp).resolve_left y_eq,
              split, right, exact (maximal_subset s r y_in),
              intros z z_in,
              cases (mem_insert.1 z_in) with hz hz,
              { rw hz,
                by_contra hay,
                by_cases h_all : ∀ b ∈ maximal_set s r, P r a b,
                { suffices : a ∈ choice_set (insert a s) r, -- finish handles the following sorry
                  { sorry, },
                  simp only [choice_set, is_best_element, 
                    true_and, sep_def, mem_filter, mem_insert,
                     forall_eq_or_imp, true_or, eq_self_iff_true],
                  refine ⟨r.refl a, λ b b_in, _ ⟩,
                  obtain ⟨c, c_in, hcb⟩ := exists_maximal_of_quasi r b_in,
                  exact r.trans (h_all c c_in).1 hcb, },
                { push_neg at h_all,
                  rcases h_all with ⟨b, b_in, hb⟩,
                  have b_in' := is_maximal_insert_of_nP a_not_in hb b_in,
                  have foo := I_trans_P r.trans (h b a b_in' ha) hay,
                  exact ((maximal_element_of_maximal_set y_in) b (maximal_subset s r b_in)) foo, }, }, 
              { exact (maximal_element_of_maximal_set y_in) z hz, }, }, }, },
        have IH_assumption : ∀ x y ∈ maximal_set s r, I r x y,
        { rw h_insert at h,
          intros x y x_in y_in,
          exact h x y ((subset_insert a _ ) x_in) ((subset_insert a _) y_in), },
        have h_empty' : choice_set s r = ∅,
        { by_contra ne_empty,
          obtain ⟨y, hy⟩:= nonempty_of_ne_empty ne_empty,
          have hya : r y a,
          { rw h_insert at h,
            refine (h y a (mem_insert_of_mem _) (mem_insert_self a (maximal_set s r))).1,
            exact choice_subset_maximal s r hy, },
          have y_in' : y ∈ choice_set (insert a s) r,
          { simp only [choice_set, is_best_element,
              sep_def, mem_filter, mem_insert, forall_eq_or_imp],
            simp only [choice_set, sep_def, mem_filter] at hy,
            exact ⟨or.inr hy.1, hya, hy.2⟩, }, -- finish handles the next sorry,
          sorry },
        rw IH IH_assumption at h_empty',
        rw h_empty' at h_insert,
        by_cases s_empty : s = ∅,
        { rw [s_empty, insert_emptyc_eq, ←r.eq_coe, 
            (choice_set_of_singleton r.refl a)] at choice_empty, -- finish fills in the next line
          sorry, },
        { have := (nonempty_of_ne_empty s_empty),
          have := maximal_of_finite_quasi_ordered r s this,
          suffices : (maximal_set s r).nonempty,
          { finish, },
          simp only [maximal_set],
          have bla := maximal_of_finite_quasi_ordered r s (nonempty_of_ne_empty s_empty),
          rcases bla with ⟨x, x_in, hx⟩,
          use x,
          simp only [sep_def, mem_filter],
          exact ⟨x_in, hx⟩, }, },
      { rw [← r.eq_coe, maximal_of_insert_not_maximal r.trans a_not_in ha, 
          r.eq_coe] at IH,
        specialize IH h,
        have choice_eq : choice_set s r = choice_set (insert a s) r,
        { ext c,
          simp only [choice_set, is_best_element, sep_def, 
            mem_filter, mem_insert, forall_eq_or_imp], 
          have : ∃ x ∈ s, P r x a,
          { simp only [maximal_set, is_maximal_element, true_and, 
              sep_def, exists_prop, mem_filter, mem_insert, forall_eq_or_imp, not_and,
              not_not, true_or, eq_self_iff_true, not_forall] at ha,
            have foo : ¬ P r a a,
            { by_contra h,
            exact h.2 h.1, },
            rcases ha foo with ⟨x, x_in, hx⟩,
            exact ⟨x, x_in, hx⟩, },
          rcases this with ⟨x, x_in, hx⟩,
          split,
          { intro hc,
            refine ⟨or.inr hc.1, _ , hc.2⟩,
            exact r.trans (hc.2 x x_in) hx.1, },
          { intro hc,
            have h_neq : ¬ c = a,
            { by_contra,
              rw h at hc,
              exact hx.2 (hc.2.2 x x_in), },
              exact ⟨hc.1.resolve_left h_neq, hc.2.2⟩, }, },
        rw choice_eq at IH,
        exact sets_neq IH, }, },   },
  { intro hyp,
    rw ← hyp,
    intros x y x_in y_in,
    simp only [choice_set, sep_def, mem_filter] at *,
    exact ⟨x_in.2 y y_in.1, y_in.2 x x_in.1⟩, },
end

/-! ### Definition of a preference ordering -/
    
/-- Preference ordering as a structure, used extensively in `arrows_theorem`. -/
structure pref_order (α : Type*) := 
(rel : α → α → Prop)
(refl : reflexive rel)
(total : total rel)
(trans : transitive rel)

instance (α : Type*) : has_coe_to_fun (pref_order α) (λ _,  α → α → Prop) := 
  ⟨ λ r, r.rel⟩

lemma pref_order.eq_coe {α : Type*} (r : pref_order α) : r.rel = r := rfl

lemma pref_order.reverse {α : Type*} {r : pref_order α} {a b : α} (h : ¬r a b) : r b a :=
(r.total a b).resolve_left h