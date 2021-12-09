import basic
import for_mathlib
import data.list.basic

structure election_profile (χ υ : Type*) :=
(cands : finset χ)
(cpos : 0 < cands.card)
(voters : finset υ)
(vpos : 0 < voters.card)
(Q : υ → χ → χ → Prop)

/-  N "removing b from N" 
    a : (N.remove b)  -/

instance {α : Type*} (s : finset α) : decidable s.nonempty :=
begin
  rw ←finset.card_pos,
  apply_instance,
end

/-
def is_cycle {χ : Type*} (q : χ → χ → Prop) (l : list χ) [decidable (l ≠ list.nil)] :=
if hl : l ≠ list.nil then list.chain q (l.last hl) l else false -/

def is_cycle {χ : Type*} (P : χ → χ → Prop) (c : list χ) := 
  ∃ (e : c ≠ list.nil), list.chain P (c.last e) c

def restrict {χ : Type*} (q : χ → χ → Prop) (s : finset χ) : χ → χ → Prop := 
λ a b, q a b ∧ a ∈ s ∧ b ∈ s  

lemma restrict_of_subset {χ : Type*} {q : χ → χ → Prop} {s t : finset χ} {a b : χ}
  (hst : s ⊆ t) (hq : (restrict q s) a b) : (restrict q t) a b := 
⟨hq.1, hst hq.2.1, hst hq.2.2⟩ 

lemma restrict_restrict_eq_restrict {χ : Type*} (q : χ → χ → Prop) (s : finset χ) :
  restrict (restrict q s) s = restrict q s :=
begin
  ext x y, split,
  { rintros ⟨⟨hxy, x_in, y_in⟩, -, -⟩,
    exact ⟨hxy, x_in, y_in⟩, },
  { rintros ⟨hxy, x_in, y_in⟩,
    exact ⟨⟨hxy,x_in,y_in⟩,x_in, y_in⟩, },
end

def cyclical {χ : Type*} (q : χ → χ → Prop) : Prop := 
  ∃ x, relation.trans_gen q x x 

def cyclical' {χ : Type*} (q : χ → χ → Prop) : Prop := 
∃ l, is_cycle q l

/- TODO: other side of the iff -/
lemma cyclical'_of_cyclical {χ : Type*} (q : χ → χ → Prop) (s : finset χ)  : 
  cyclical q → cyclical' q :=
begin
  simp only [cyclical, cyclical', is_cycle],
  rintros ⟨x, hx⟩,
  obtain ⟨l, hl₁, hl₂, hl₃⟩ := exists_chain_of_relation_trans_gen hx,
  have l_last : l.last hl₁ = x := by rw ← hl₃;
    exact (list.last_cons (list.cons_ne_nil _ _) hl₁).symm,
  rw ← l_last at hl₂, 
  exact ⟨l, hl₁, hl₂⟩,
end


def margin {χ υ : Type*} (voters : finset υ) (Q : υ → χ → χ → Prop) (c c' : χ) 
  [∀ v, decidable_rel (Q v)] : ℤ :=
(voters.filter (λ v, Q v c c')).card - (voters.filter (λ v, Q v c' c)).card

def defeats {χ υ : Type*} (voters : finset υ) (cands: finset χ) (Q : υ → χ → χ → Prop) 
  (x y: χ) [∀ v, decidable_rel (Q v)] [∀ k : list χ, decidable (k ≠ list.nil)] :=
0 < margin voters Q x y ∧ ¬ (∃ l : list χ, (∀ c ∈ l, c ∈ cands) ∧ x ∈ l ∧ y ∈ l ∧
    is_cycle (λ a b, margin voters Q x y ≤ margin voters Q a b) l)

def is_undefeated {χ υ : Type*} (voters : finset υ) (cands: finset χ) (Q : υ → χ → χ → Prop) 
  (x : χ) [∀ v, decidable_rel (Q v)] [∀ k : list χ, decidable (k ≠ list.nil)] := 
  ∀ y ∈ cands, ¬ defeats voters cands Q y x

def best_margin {χ υ : Type*} (voters : finset υ) (s : finset (χ × χ)) (Q : υ → χ → χ → Prop) 
  [∀ v, decidable_rel (Q v)] : ℤ :=
  if hn : s.nonempty
    then s.sup' hn (λ p, margin voters Q p.1 p.2) 
  else 0

def uniquely_weighted {χ υ : Type*} -- 
  (voters : finset υ) (cands : finset χ) (Q : υ → χ → χ → Prop) 
  [∀ v, decidable_rel (Q v)] : Prop := 
∀ a b a' b' ∈ cands, a ≠ b → a' ≠ b' → ((a ≠ a' ) ∨ (b ≠ b')) → 
margin voters Q a b ≠ margin voters Q a' b'

open_locale classical

noncomputable def stable_voting' {χ υ : Type*} (voters : finset υ) (Q : υ → χ → χ → Prop) :
  Π (n : ℕ) (cands : finset χ) (hn : cands.card = n) (cpos : 0 < n), finset χ
| 0 _ _ cpos := (nat.not_lt_zero _ cpos).elim
| 1 cands _ _ := cands
| (n+2) cands hn cpos :=
let
  -- whether c wins when candidate rem is removed
  still_wins (c rem : χ) : Prop :=
    if rem_prop : rem ∈ cands 
      then c ∈ stable_voting' (n+1) (cands.erase rem)
          (by { rw [finset.card_erase_of_mem, hn]; simp [rem_prop], })
          (by omega)
    else false,
  viable : finset (χ × χ) := (cands.product cands).filter 
      (λ p, still_wins p.1 p.2 ∧ ¬ defeats voters cands Q p.2 p.1)
in finset.image prod.fst $ viable.filter (λ p, (margin voters Q p.1 p.2 = best_margin voters viable Q))

noncomputable def stable_voting {χ υ : Type*} (prof : election_profile χ υ)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] : finset χ :=
stable_voting' prof.voters prof.Q prof.cands.card prof.cands rfl prof.cpos

lemma sv_singleton {χ υ : Type*} (prof : election_profile χ υ) (hcands : prof.cands.card = 1) : 
  stable_voting prof = prof.cands :=
by simp only [stable_voting, stable_voting', hcands]

lemma exists_best_margin {χ υ : Type*} {s : finset (χ × χ)} (voters : finset υ) (Q : υ → χ → χ → Prop) 
  (hs : s.nonempty) :
  ∃ p : χ × χ, p ∈ s ∧ margin voters Q p.1 p.2 = best_margin voters s Q :=
begin
  obtain ⟨b, b_in, hb⟩ := finset.exists_mem_eq_sup' hs 
    (λ (p : χ × χ), margin voters Q p.fst p.snd),
  unfold best_margin,
  simp only [hs, dif_pos],
  exact ⟨b, b_in, hb.symm⟩, 
end 

section trans_gen

lemma trans_gen_of_imp {χ : Type*} {Q R : χ → χ → Prop} 
  (hyp : ∀ a b, Q a b → R a b) : 
  ∀ {a b}, relation.trans_gen Q a b → relation.trans_gen R a b := 
begin
  intros a b hab,
  refine relation.trans_gen.trans_induction_on hab 
    (λ x y hxy, relation.trans_gen.single $ hyp x y hxy) _,
  intros x y z hxy hyz hxy' hyz',
  exact relation.transitive_trans_gen hxy' hyz',
end

end trans_gen

lemma cyclical_of_subset_cyclical {χ : Type*} {R : χ → χ → Prop} {s t : finset χ} 
  (hst : s ⊆ t) (h_cyc : cyclical (restrict R s)) : cyclical (restrict R t) := 
begin
  rcases h_cyc with ⟨x, hx⟩,
  use x, refine (trans_gen_of_imp (λ a b hab, _ ) hx),
  exact restrict_of_subset hst hab,
end

example {χ : Type*} {s t : finset χ} (h : t ⊂ s) : t.card < s.card := by refine finset.card_lt_card h
example {m n : ℕ} (h : m < n.succ) : m ≤ n := nat.lt_succ_iff.mp h

lemma cylical_of_serial' {χ : Type*} :
  ∀ (n : ℕ) (s : finset χ) (R : χ → χ → Prop), n = s.card → s.nonempty →
    (∀ x ∈ s, ∃ y ∈ s, R x y) → cyclical (restrict R s) :=
begin
  intro a, refine nat.case_strong_induction_on a _ _,
  { intros s h R hs, linarith [finset.card_pos.2 hs] },
  { intros n IH s R s_card hs₁ hs₂,
    obtain ⟨x, x_in⟩ := hs₁,
    obtain ⟨y, y_in, hxy⟩ := hs₂ x x_in,
    by_cases x_eq_y : x = y,
    { use x,
      apply relation.trans_gen.single, 
      rw ← x_eq_y at hxy,
      exact ⟨hxy, ⟨x_in, x_in⟩⟩, },
    set t : finset χ := s.filter (λ z, relation.trans_gen (restrict R s) y z)
      with ht,
    by_cases x_in' : x ∈ t,
    { use x, simp only [finset.mem_filter] at x_in',
      exact relation.trans_gen.head ⟨hxy,x_in,y_in⟩ x_in'.2, },
    have t_nonempty : t.nonempty,
    { obtain ⟨z, z_in, hyz⟩ := hs₂ y y_in, use z,
      simp only [finset.mem_filter],
      exact ⟨z_in, relation.trans_gen.single ⟨hyz,y_in,z_in⟩⟩, },
    have t_ss : t ⊂ s,
    { rw finset.ssubset_iff_of_subset (finset.filter_subset _ s), 
      exact ⟨x, x_in, x_in'⟩, },
    have t_card : t.card ≤ n := 
      by rw [← nat.lt_succ_iff, s_card]; exact finset.card_lt_card t_ss,
    have := IH t.card t_card t (restrict R t) rfl t_nonempty,
    rw restrict_restrict_eq_restrict R t at this,
    refine cyclical_of_subset_cyclical 
      (by simp only [finset.filter_subset]) 
      (this _),
    intros a a_in,
    obtain ⟨b, b_in, hab⟩ := hs₂ a (finset.filter_subset _ s a_in),
    have b_in : b ∈ t,
    { simp only [finset.mem_filter] at ⊢ a_in,
      exact ⟨b_in, relation.trans_gen.tail a_in.2 ⟨hab,a_in.1,b_in⟩⟩, },
    exact ⟨b, b_in, ⟨hab, a_in, b_in⟩⟩,
  },
end

/- Random lemmas for natural numbers -/
lemma exists_eq_plus_two (n : ℕ) (hn₀ : ¬ n = 0) (hn₁ : ¬ n = 1) : 
  ∃ m, n = m + 2 :=
begin
  cases n with d, { exact (hn₀ nat.nat_zero_eq_zero).elim, },
  induction d with d hd, {exact (hn₁ rfl).elim, },
  use d,
end

lemma ge_two_of_ne_zero_ne_one {n : ℕ} (hn₀ : ¬ n = 0) (hn₁ : ¬ n = 1) :
  2 ≤ n :=
begin
  cases n with d, { exact (hn₀ nat.nat_zero_eq_zero).elim, },
  induction d with d hd, {exact (hn₁ rfl).elim, },
  rw nat.succ_le_iff,
  exact nat.one_lt_succ_succ d,  
end

lemma mem_cands_of_mem_sv {χ υ : Type*} (prof : election_profile χ υ) (a : χ) : 
  a ∈ stable_voting prof → a ∈ prof.cands := 
begin
  intro a_in,
  by_cases hcands : prof.cands.card = 1, 
  { rwa (sv_singleton prof hcands) at a_in },
  obtain ⟨n, hn⟩ := exists_eq_plus_two prof.cands.card 
    (by linarith [prof.cpos]) hcands, 
  simp only [stable_voting, stable_voting', hn, exists_prop, 
    exists_and_distrib_right, exists_eq_right, finset.mem_image,
    finset.mem_filter, finset.filter_congr_decidable, 
    prod.exists, finset.mem_product] at a_in,
  rcases a_in with ⟨b,⟨⟨p_in,hp⟩,ha⟩⟩,
  exact p_in.1,
end

lemma false_iff_filter_empty {α : Type* } (s : finset α) (p : α → Prop) : 
  (∀ x ∈ s, ¬ p x) ↔ s.filter p = ∅ := 
begin
  refine ⟨λ h, finset.filter_false_of_mem h, λ h x x_in, _⟩,
  rw ← finset.not_nonempty_iff_eq_empty at h,
  by_contradiction hx,
  refine h _,
  use x,
  simp only [finset.mem_filter],
  exact ⟨x_in, hx⟩,
end

lemma exists_sv_winner' {χ υ : Type*} :
  ∀ (n : ℕ) (prof : election_profile χ υ), prof.cands.card = n → 
  ∃ a, a ∈ stable_voting prof :=
begin
  intro n,
  cases n with d, 
  { intros prof hn,
    linarith [hn, prof.cpos], },
  induction d with d IH,
  { intros prof hn,
    rw sv_singleton prof hn,
    exact finset.card_pos.1 prof.cpos, },
  intros prof hm,
  set m := d.succ with m_succ,
  obtain ⟨b, b_in⟩ := finset.card_pos.1 prof.cpos,
  have h_erase_card : ∀ z ∈ prof.cands, finset.card (prof.cands.erase z) = m,
  { intros z z_in,
    rw finset.card_erase_of_mem z_in,
    exact nat.pred_eq_of_eq_succ hm, },
  set prof' : election_profile χ υ := 
    ⟨(prof.cands.erase b), 
     (by rw (h_erase_card b b_in); omega), 
     prof.voters, prof.vpos, prof.Q⟩ with h_prof', 
  obtain ⟨a, a_in⟩ := IH prof' (by rw ← h_erase_card b b_in),
  have card_eq_d : prof.cands.card = d + 2 := by rw hm,
  simp only [stable_voting, stable_voting', card_eq_d, 
    exists_prop, exists_and_distrib_right, exists_eq_right, 
    finset.mem_image, finset.mem_filter, finset.filter_congr_decidable, 
    prod.exists, finset.mem_product],
  let still_wins : χ → χ → Prop := λ x₁ x₂,
    if x₂_in : x₂ ∈ prof.cands 
      then x₁ ∈ stable_voting' prof.voters prof.Q d.succ 
          (prof.cands.erase x₂)
          (by rwa h_erase_card x₂ x₂_in) (nat.succ_pos d)
    else false,
  set viable_set : finset (χ × χ) := (prof.cands.product prof.cands).filter
    (λ p, still_wins p.1 p.2 ∧ ¬ defeats prof.voters prof.cands prof.Q p.2 p.1) with hvs,
  have viable_nonempty : viable_set.nonempty,
  { by_contra h,
    have foo : (∀ (x : χ × χ),
       x ∈ prof.cands.product prof.cands →
       ¬(λ (p : χ × χ), still_wins p.fst p.snd ∧ 
          ¬defeats prof.voters prof.cands prof.Q p.snd p.fst) x) := sorry,
    simp only [and_imp, prod.forall, not_and, not_not, finset.mem_product] at foo,
    have : ∀ x ∈ prof.cands, ∃ y ∈ prof.cands, 
      defeats prof.voters prof.cands prof.Q y x,
    { intros x x_in,
      set prof_rem_x : election_profile χ υ := 
      ⟨(prof.cands.erase x), 
       (by rw (h_erase_card x x_in); exact nat.succ_pos d), 
       prof.voters, prof.vpos, prof.Q⟩ with h_prof_rem_x,
      obtain ⟨y, y_in⟩ := IH prof_rem_x (by rw ← h_erase_card x x_in),
      suffices : still_wins y x,
      { --refine ⟨y, _, foo y x _ x_in this⟩,
        sorry,

      },
      sorry,

    },

  },
  sorry,

  /-
  simp only [simple_stable_voting, simple_stable_voting', 
    card_eq_d, exists_prop, exists_and_distrib_right, exists_eq_right,
    finset.mem_image, finset.mem_filter, finset.filter_congr_decidable,
    prod.exists, finset.mem_product],
  set viable_set : finset (χ × χ) := (prof.cands.product prof.cands).filter
    (λ p, if p2_in : p.2 ∈ prof.cands 
      then p.1 ∈ simple_stable_voting' prof.voters prof.Q d.succ 
           (prof.cands.erase p.2)
           (by rwa h_erase_card p.snd p2_in) (nat.succ_pos d)
      else false) with hvs,
  have viable_nonempty : viable_set.nonempty,
  { use ⟨a,b⟩,
    have : a ∈ (prof.cands.erase b) := 
      by simp only [mem_cands_of_mem_winners prof' a a_in],
    simp only [simple_stable_voting, h_prof', h_erase_card b b_in, m_succ] at a_in,
    simp only [finset.mem_filter, finset.mem_product, b_in, 
      dif_pos, dif_pos, and_true, finset.mem_filter, finset.mem_product],
    exact ⟨(finset.mem_erase.1 this).2, a_in⟩, },  
  obtain ⟨p, p_in, hp⟩ := exists_best_margin prof.voters prof.Q viable_nonempty,
  refine ⟨p.1, p.2, ⟨_,(by rw hp)⟩⟩,
  rw [hvs, finset.mem_filter] at p_in,
  cases p_in with hp₁ hp₂,
  refine ⟨finset.mem_product.1 hp₁, _⟩,
  simpa only [(finset.mem_product.mp hp₁).right, dif_pos, finset.mem_product,
    true_and, dif_pos, finset.mem_product, true_and,
    dif_pos, finset.mem_product] using hp₂, -/
end