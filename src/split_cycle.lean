import for_mathlib
import data.list.basic

/------- Definitions -------/

def restrict {χ : Type*} (q : χ → χ → Prop) (s : finset χ) : χ → χ → Prop := 
λ a b, q a b ∧ a ∈ s ∧ b ∈ s  

instance {α β: Type*} (s : finset α) (Q : β → α → α → Prop) 
  [decidable_eq α] [∀ b, decidable_rel (Q b)] : 
  ∀ b, decidable_rel (restrict (Q b) s) :=
begin
  intro b,
  unfold restrict,
  apply_instance,
end

def cyclical {χ : Type*} (q : χ → χ → Prop) : Prop := 
∃ x, relation.trans_gen q x x 

def is_cycle' {χ : Type*} (P : χ → χ → Prop) (c : list χ) := 
  ∃ (e : c ≠ list.nil), list.chain P (c.last e) c

def cyclical' {χ : Type*} (q : χ → χ → Prop) : Prop := 
∃ l, is_cycle' q l

def acyclical' {χ : Type*} (q : χ → χ → Prop) : Prop :=
∀ l, ¬ is_cycle' q l

def acyclical_in' {χ : Type*} (q : χ → χ → Prop) (s : finset χ): Prop := 
∀ l : list χ, (∀ x ∈ l, x ∈ s) → ¬ is_cycle' q l

def margin {χ υ : Type*} (voters : finset υ) (Q : υ → χ → χ → Prop) (c c' : χ) 
  [∀ v, decidable_rel (Q v)] : ℤ :=
(voters.filter (λ v, Q v c c')).card - (voters.filter (λ v, Q v c' c)).card

def margin_pos {χ υ : Type*} (voters : finset υ) (Q : υ → χ → χ → Prop)
  [∀ v, decidable_rel (Q v)] (c c' : χ) : Prop :=  0 < margin voters Q c c'

def defeats {χ υ : Type*} (voters : finset υ) (cands: finset χ) (Q : υ → χ → χ → Prop) 
  [∀ v, decidable_rel (Q v)] [decidable_eq χ] --[∀ k : list χ, decidable (k ≠ list.nil)] 
  (x y: χ) := 
let Q' : υ → χ → χ → Prop := λ i, restrict (Q i) cands in
0 < margin voters Q x y ∧ ¬ (∃ l : list χ, (∀ c ∈ l, c ∈ cands) ∧ x ∈ l ∧ y ∈ l ∧
    is_cycle' (λ a b, margin voters Q x y ≤ margin voters Q a b) l)

/------- Lemmas -------/

lemma succ_pred {i : ℕ} (e : 0 < i) : i - 1 + 1 = i := by omega

lemma ineq5 (i n : ℕ) (e : i < n) (z: ¬i = n - 1) : i < n - 1 := by omega

lemma dominate_ineq3 {a b : ℕ} (e : 0 < b) : a < b - 1 → a + 1 < b := by omega

/- TODO: other side of the iff -/
lemma cyclical'_of_cyclical {χ : Type*} (q : χ → χ → Prop) (s : finset χ)  : 
  cyclical q → cyclical' q :=
begin
  simp only [cyclical, cyclical', is_cycle'],
  rintros ⟨x, hx⟩,
  obtain ⟨l, hl₁, hl₂, hl₃⟩ := exists_chain_of_relation_trans_gen hx,
  have l_last : l.last hl₁ = x := by rw ← hl₃;
    exact (list.last_cons (list.cons_ne_nil _ _) hl₁).symm,
  rw ← l_last at hl₂, 
  exact ⟨l, hl₁, hl₂⟩,
end

/- TODO: GOLF-/
lemma nonempty_ico {X : Type*} (c : list X) (e : 0 < c.length) : (finset.Ico 0 c.length).nonempty  :=
begin
    fconstructor,
    use 0,
    simp at *,
    omega,
end

def length_cycle_pos {χ : Type*} {l : list χ} {P : χ → χ → Prop} 
  (c : is_cycle' P l) : 0 < l.length :=
begin
    cases c with a b,
    exact list.length_pos_of_ne_nil a,
end

lemma dominates_of_cycle_index {χ : Type*} (P : χ → χ → Prop) (l : list χ) (hl : is_cycle' P l)
  (i : ℕ) (i_bound : i < l.length) : 
  P (l.nth_le i i_bound) (l.nth_le ((i + 1) % l.length) (nat.mod_lt (i + 1) (length_cycle_pos hl))) :=
begin
    unfold is_cycle' at hl,
    cases hl with e c,
    rw list.chain_iff_nth_le at c,
    cases c with c_left c_right,
    by_cases z : i = l.length - 1,
        {simp_rw z, rw ←list.last_eq_nth_le l e,
        specialize c_left (list.length_pos_of_ne_nil e),
        simp_rw succ_pred (list.length_pos_of_ne_nil e),
        simp_rw nat.mod_self,
        exact c_left,},
    specialize c_right i,
    have i_bound2 := ineq5 i l.length i_bound z,
    specialize c_right i_bound2,
    have underflow : (i + 1) % l.length = (i + 1),
    rw nat.mod_eq_of_lt,
    exact dominate_ineq3 (list.length_pos_of_ne_nil e) i_bound2,
    simp_rw underflow,
    exact c_right,
end

lemma split_cycle_to_margin_cycle {χ υ : Type*} 
  (voters : finset υ) (cands: finset χ) (Q : υ → χ → χ → Prop) (c : list χ)
  [∀ v, decidable_rel (Q v)] [decidable_eq χ] /-[∀ k : list χ, decidable (k ≠ list.nil)]-/ : 
  is_cycle' (defeats voters cands Q) c → is_cycle' (margin_pos voters Q) c :=
begin
    intro chain,
    unfold is_cycle' at chain,
    cases chain with witness chain,
    use witness,
    refine list.chain_of_chain_map id _ _, 
    exact (defeats voters cands Q),
    intros a b s,
    exact and.left s,
    simp,
    exact chain,
end

theorem defeat_acyclical_in' {χ υ : Type*} (voters : finset υ) (cands: finset χ) (Q : υ → χ → χ → Prop) 
  [decidable_eq χ] [∀ v, decidable_rel (Q v)] /-[∀ k : list χ, decidable (k ≠ list.nil)]-/ :
  acyclical_in' (defeats voters cands Q) cands :=
begin
  rintros c hcs ⟨c_ne_nil, hc⟩,
  have ico_nonempty := nonempty_ico c (list.length_pos_of_ne_nil c_ne_nil),
  have margin_pos_cyc := split_cycle_to_margin_cycle voters cands Q c ⟨c_ne_nil, hc⟩,
  obtain ⟨mini_idx, bounds, mini_req⟩ := 
    finset.exists_min_image (finset.Ico 0 c.length) (λ x, (margin voters Q) 
    (c.nth_le (x % c.length) (nat.mod_lt x (list.length_pos_of_ne_nil c_ne_nil))) 
    (c.nth_le ((x+1) % c.length) (nat.mod_lt (x+1) (list.length_pos_of_ne_nil c_ne_nil)))) 
    ico_nonempty,
  simp only [nat.Ico_zero_eq_range, finset.mem_range] at bounds,
  let mini := (c.nth_le mini_idx bounds),
  have mini_mem := list.nth_le_mem c mini_idx bounds,
  obtain ⟨defeated, defeats⟩ := 
    dominates_of_cycle_index (defeats voters cands Q) c ⟨c_ne_nil, hc⟩ mini_idx bounds,
  simp only [nat.Ico_zero_eq_range, finset.mem_range] at mini_req,
  contrapose defeats,
  push_neg,
  refine ⟨c, hcs ,mini_mem, _, _⟩,
  { exact list.nth_le_mem c ((mini_idx + 1) % c.length) 
      (nat.mod_lt (mini_idx + 1) (list.length_pos_of_ne_nil c_ne_nil)) },
  unfold is_cycle',
  use c_ne_nil,
  rw list.chain_iff_nth_le,
  split,
  { intro h,
    specialize mini_req (c.length - 1),
    have o : ∀ (n : ℕ), (0 < n) → n - 1 < n := by omega,
    { specialize mini_req (o c.length h),
      have cal : (c.length-1) % c.length = c.length-1,
      { apply nat.mod_eq_of_lt,
      exact o c.length h },
      simp_rw cal at mini_req,
      have cal : (c.length - 1 + 1) % c.length = 0,
      { rw succ_pred h,
        exact nat.mod_self c.length, },
      simp_rw cal at mini_req,
      rw ←list.last_eq_nth_le c c_ne_nil at mini_req,  
      have test : (margin voters Q (c.nth_le (mini_idx % c.length) (mini_idx.mod_lt (list.length_pos_of_ne_nil c_ne_nil))) (c.nth_le ((mini_idx + 1) % c.length) ((mini_idx + 1).mod_lt (list.length_pos_of_ne_nil c_ne_nil))) ≤ margin voters Q (c.last c_ne_nil) (c.nth_le 0 (eq.rec ((c.length - 1 + 1).mod_lt (list.length_pos_of_ne_nil c_ne_nil)) cal))) = (margin voters Q (c.nth_le mini_idx bounds) (c.nth_le ((mini_idx + 1) % c.length) ((mini_idx + 1).mod_lt (length_cycle_pos ⟨c_ne_nil,hc⟩))) ≤ margin voters Q (c.last c_ne_nil) (c.nth_le 0 h)),
        { congr,
        exact nat.mod_eq_of_lt bounds, },
      rw ←test,
      exact mini_req } },
  { intros i h,
    specialize mini_req i,
    specialize mini_req (nat.lt_of_lt_pred h),
    simp_rw (nat.mod_eq_of_lt bounds) at mini_req,
    simp_rw (nat.mod_eq_of_lt (nat.lt_of_lt_pred h)) at mini_req,
    have o : ∀ i n, i < n - 1 → 0 < n → (i + 1) < n := by omega,
    simp_rw (nat.mod_eq_of_lt (o i c.length h (list.length_pos_of_ne_nil c_ne_nil))) at mini_req,
    exact mini_req },
end 

/-
theorem defeat_acyclical' {χ υ : Type*} (voters : finset υ) (cands: finset χ) (Q : υ → χ → χ → Prop) 
  [decidable_eq χ] [∀ v, decidable_rel (Q v)] /-[∀ k : list χ, decidable (k ≠ list.nil)]-/ :
  acyclical' (defeats voters cands Q) :=
begin
  rintros c ⟨c_ne_nil, hc⟩,
  have ico_nonempty := nonempty_ico c (list.length_pos_of_ne_nil c_ne_nil),
  have margin_pos_cyc := split_cycle_to_margin_cycle voters cands Q c ⟨c_ne_nil, hc⟩,
  obtain ⟨mini_idx, bounds, mini_req⟩ := 
    finset.exists_min_image (finset.Ico 0 c.length) (λ x, (margin voters Q) 
    (c.nth_le (x % c.length) (nat.mod_lt x (list.length_pos_of_ne_nil c_ne_nil))) 
    (c.nth_le ((x+1) % c.length) (nat.mod_lt (x+1) (list.length_pos_of_ne_nil c_ne_nil)))) 
    ico_nonempty,
  simp only [nat.Ico_zero_eq_range, finset.mem_range] at bounds,
  let mini := (c.nth_le mini_idx bounds),
  have mini_mem := list.nth_le_mem c mini_idx bounds,
  obtain ⟨defeated, defeats⟩ := 
    dominates_of_cycle_index (defeats voters cands Q) c ⟨c_ne_nil, hc⟩ mini_idx bounds,
  simp only [nat.Ico_zero_eq_range, finset.mem_range] at mini_req,
  contrapose defeats,
  push_neg,
  refine ⟨c, _,mini_mem, _, _⟩,
  { sorry, },
  { exact list.nth_le_mem c ((mini_idx + 1) % c.length) 
      (nat.mod_lt (mini_idx + 1) (list.length_pos_of_ne_nil c_ne_nil)) },
  unfold is_cycle',
  use c_ne_nil,
  rw list.chain_iff_nth_le,
  split,
  { intro h,
    specialize mini_req (c.length - 1),
    have o : ∀ (n : ℕ), (0 < n) → n - 1 < n := by omega,
    { specialize mini_req (o c.length h),
      have cal : (c.length-1) % c.length = c.length-1,
      { apply nat.mod_eq_of_lt,
      exact o c.length h },
      simp_rw cal at mini_req,
      have cal : (c.length - 1 + 1) % c.length = 0,
      { rw succ_pred h,
        exact nat.mod_self c.length, },
      simp_rw cal at mini_req,
      rw ←list.last_eq_nth_le c c_ne_nil at mini_req,  
      have test : (margin voters Q (c.nth_le (mini_idx % c.length) (mini_idx.mod_lt (list.length_pos_of_ne_nil c_ne_nil))) (c.nth_le ((mini_idx + 1) % c.length) ((mini_idx + 1).mod_lt (list.length_pos_of_ne_nil c_ne_nil))) ≤ margin voters Q (c.last c_ne_nil) (c.nth_le 0 (eq.rec ((c.length - 1 + 1).mod_lt (list.length_pos_of_ne_nil c_ne_nil)) cal))) = (margin voters Q (c.nth_le mini_idx bounds) (c.nth_le ((mini_idx + 1) % c.length) ((mini_idx + 1).mod_lt (length_cycle_pos ⟨c_ne_nil,hc⟩))) ≤ margin voters Q (c.last c_ne_nil) (c.nth_le 0 h)),
        { congr,
        exact nat.mod_eq_of_lt bounds, },
      rw ←test,
      exact mini_req } },
  { intros i h,
    specialize mini_req i,
    specialize mini_req (nat.lt_of_lt_pred h),
    simp_rw (nat.mod_eq_of_lt bounds) at mini_req,
    simp_rw (nat.mod_eq_of_lt (nat.lt_of_lt_pred h)) at mini_req,
    have o : ∀ i n, i < n - 1 → 0 < n → (i + 1) < n := by omega,
    simp_rw (nat.mod_eq_of_lt (o i c.length h (list.length_pos_of_ne_nil c_ne_nil))) at mini_req,
    exact mini_req },
end 
-/