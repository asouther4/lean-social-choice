import data.set.finite

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

/-! ### Definition of a preference ordering -/
    
/-- Preference ordering as a structure, used in `arrows_ordinal_prefs`. -/
structure pref_order (α : Type*) := 
(rel : α → α → Prop)
(refl : reflexive rel)
(total : total rel)
(trans : transitive rel)

instance (α : Type*) : has_coe_to_fun (pref_order α) := ⟨_, λ r, r.rel⟩

lemma pref_order.eq_coe {α : Type*} (r : pref_order α) : r.rel = r := rfl

lemma pref_order.reverse {α : Type*} {r : pref_order α} {a b : α} (h : ¬r a b) : r b a :=
(r.total a b).resolve_left h

-- We think of social states as type `σ` and inidividuals as type `ι`
variables {σ ι : Type*} {x y x' y' z a b : σ} {R R' : σ → σ → Prop}

/-- "Old" defintion of a preference ordering, used throughout the rest of this file. -/
def is_pref_ordering (R : σ → σ → Prop) : Prop :=
reflexive R ∧ total R ∧ transitive R

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

lemma R_of_nP_total (hR : total R) (h : ¬P R y x) : R x y :=
begin
  by_cases hyp : R y x,
  exacts [not_and_not_right.mp h hyp, or_iff_not_imp_right.mp (hR x y) hyp],
end

lemma nP_of_reverseP (h : P R x y) : ¬P R y x :=
not_and_not_right.mpr $ λ n, h.1

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

lemma cyclical_of_no_highest (R : σ → σ → Prop) {S : finset σ} (hS : S.nonempty) 
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
    refine cyclical_of_no_highest (P R) X_ne (forall_exists_trans_gen _ (λ a a_in, _)),
    simp only [is_best_element, not_exists, not_forall] at h,
    obtain ⟨b, b_in, hb⟩ := h a a_in,
    exact ⟨b, b_in, ⟨(htot a b).resolve_left hb, hb⟩⟩ },
end
