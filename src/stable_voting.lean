import for_mathlib
import split_cycle
import data.list.basic

structure election_profile (χ υ : Type*) :=
(cands : finset χ)
(cpos : 0 < cands.card)
(voters : finset υ)
(vpos : 0 < voters.card)
(Q : υ → χ → χ → Prop)


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

instance {α : Type*} (s : finset α) : decidable s.nonempty :=
begin
  rw ←finset.card_pos,
  apply_instance,
end

def best_margin {χ υ : Type*} (voters : finset υ) (s : finset (χ × χ)) (Q : υ → χ → χ → Prop) 
  [∀ v, decidable_rel (Q v)] : ℤ :=
  if hn : s.nonempty
    then s.sup' hn (λ p, margin voters Q p.1 p.2) 
  else 0

def uniquely_weighted {χ υ : Type*} 
  (voters : finset υ) (cands : finset χ) (Q : υ → χ → χ → Prop) 
  [∀ v, decidable_rel (Q v)] : Prop := 
∀ a b a' b' ∈ cands, a ≠ b → a' ≠ b' → (a ≠ a' ∨ b ≠ b') → 
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

lemma cyclical_of_serial' {χ : Type*} :
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
    exact ⟨b, b_in, ⟨hab, a_in, b_in⟩⟩ }
end

lemma cyclical_of_serial {χ : Type*} {s : finset χ} {R : χ → χ → Prop} 
  (hs₁ : s.nonempty) (hs₂ : ∀ x ∈ s, ∃ y ∈ s, R x y) :
  cyclical (restrict R s) :=
cyclical_of_serial' s.card s R rfl hs₁ hs₂

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

lemma mem_cands_of_mem_sv {χ υ : Type*} {prof : election_profile χ υ} {a : χ}  
  (a_in : a ∈ stable_voting prof) : a ∈ prof.cands := 
begin
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
  { intros z  z_in,
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
          ¬defeats prof.voters prof.cands prof.Q p.snd p.fst) x),
    { push_neg,
      intros x x_in hx₁, by_contra hx₂,
      apply h, use x,
      simp only [hvs,finset.mem_filter],
      exact ⟨x_in, hx₁, hx₂⟩ },
    simp only [and_imp, prod.forall, not_and, not_not, finset.mem_product] at foo,
    have h_ser : ∀ x ∈ prof.cands, ∃ y ∈ prof.cands, 
      defeats prof.voters prof.cands prof.Q x y,
    { intros x x_in,
      set prof_rem_x : election_profile χ υ := 
      ⟨(prof.cands.erase x), 
       (by rw (h_erase_card x x_in); exact nat.succ_pos d), 
       prof.voters, prof.vpos, prof.Q⟩ with h_prof_rem_x,
      obtain ⟨y, y_in⟩ := IH prof_rem_x (by rw ← h_erase_card x x_in),
      have y_in' : y ∈ prof.cands := 
        (finset.mem_erase.1 (mem_cands_of_mem_sv y_in)).2,
      suffices : still_wins y x, { exact ⟨y, y_in', foo y x y_in' x_in this⟩, },
      simp only [still_wins, x_in, dif_pos],
      convert y_in,
      rwa h_erase_card x x_in, },
    apply not_acyclical_in'_of_cyclical'_restrict (cyclical'_of_cyclical 
      (cyclical_of_serial (finset.card_pos.1 prof.cpos) h_ser)),
    exact defeat_acyclical_in' prof.voters prof.cands prof.Q, },
  obtain ⟨p, p_in, hp⟩ := exists_best_margin prof.voters prof.Q viable_nonempty,
  refine ⟨p.1,p.2, ⟨_, (by rw hp)⟩⟩,
  rw [hvs, finset.mem_filter] at p_in,
  rcases p_in with ⟨hp₁, hp₂, hp₃⟩,
  refine ⟨finset.mem_product.1 hp₁, ⟨ _,hp₃⟩⟩,
  simp only [(finset.mem_product.mp hp₁).right, dif_pos, 
    finset.mem_product, still_wins] at hp₂ ⊢,
  exact hp₂,
end

lemma exists_sv_winner {χ υ : Type*} (prof : election_profile χ υ) :
  ∃ a, a ∈ stable_voting prof := exists_sv_winner' prof.cands.card prof rfl

lemma sv_winner_undefeated' {χ υ : Type*} :
  ∀ (n : ℕ) (prof : election_profile χ υ), prof.cands.card = n → 
  ∀ a ∈ stable_voting prof, is_undefeated prof.voters prof.cands prof.Q a :=
begin
  intro n,
  cases n with d, 
  { intros prof hn,
    linarith [hn, prof.cpos], },
  induction d with d IH,
  { intros prof hn a a_in y y_in,
    rw finset.card_le_one.1 (le_of_eq hn) 
      a (mem_cands_of_mem_sv a_in) y y_in,
    exact defeat_irreflexive prof.voters prof.cands prof.Q y },
  intros prof cands_card a a_in,
  simp only [stable_voting, stable_voting', cands_card, exists_prop, 
    exists_and_distrib_right, exists_eq_right, finset.mem_image,
    finset.mem_filter, finset.filter_congr_decidable, prod.exists, 
    finset.mem_product] at a_in, 
  rcases a_in with ⟨x,⟨⟨p_in,hp⟩,ha⟩⟩,
  have p_in' : (a,x).snd ∈ prof.cands := by simp only; exact p_in.2,
  rw dif_pos p_in' at hp,
  have h_erase_card : (prof.cands.erase x).card = d.succ := 
    by simpa [finset.card_erase_of_mem p_in.2] using nat.pred_eq_of_eq_succ cands_card,
  set prof' : election_profile χ υ := 
    ⟨(prof.cands.erase x), 
     (by rw h_erase_card; exact nat.zero_lt_succ d), 
     prof.voters, prof.vpos, prof.Q⟩ with h_prof', 
  have a_in' : a ∈ stable_voting prof',
  { simp only [stable_voting], convert hp.1 },
  refine undefeated_erase _ hp.2,
  simpa using (IH prof' (by convert h_erase_card) a a_in'),
end

lemma sv_winner_undefeated {χ υ : Type*} {prof : election_profile χ υ} :
  ∀ a ∈ stable_voting prof, is_undefeated prof.voters prof.cands prof.Q a :=
sv_winner_undefeated' prof.cands.card prof rfl

lemma sv_winner_unique' {χ υ : Type*} :
  ∀ (n : ℕ) (prof : election_profile χ υ), prof.cands.card = n → 
  uniquely_weighted prof.voters prof.cands prof.Q → 
  (stable_voting prof).card = 1 :=
begin
  intro n,
  cases n with d, 
  { intros prof hn,
    linarith [hn, prof.cpos], },
  induction d with d IH,
  { intros prof hn _,
    rwa sv_singleton prof hn, },
  set m := d.succ with m_succ,
  intros prof hm h_uniq,
  have card_eq_d : prof.cands.card = d + 2 := by rw hm,
  by_contradiction h_card,
  have hab : ∃ a b ∈ (stable_voting prof), a ≠ b,
  { obtain ⟨a, a_in⟩ := exists_sv_winner prof,
    suffices : 2 ≤ (stable_voting prof).card,
    { obtain ⟨b, b_in, hb⟩ := finset.exists_second_distinct_mem this a_in,
      use ⟨a, b, a_in, b_in, hb.symm⟩, },
    exact ge_two_of_ne_zero_ne_one 
      (ne_of_gt (finset.card_pos.2 (exists_sv_winner prof))) h_card, },
  rcases hab with ⟨a, b, a_in, b_in, a_neq_b⟩,
  simp only [stable_voting, stable_voting', 
    card_eq_d, exists_prop, exists_and_distrib_right, exists_eq_right,
    finset.mem_image, finset.mem_filter, finset.filter_congr_decidable, 
    prod.exists, finset.mem_product] at a_in b_in,
  rcases a_in with ⟨x,⟨⟨p_in,hp⟩,ha⟩⟩, rcases b_in with ⟨y,⟨⟨q_in,hq⟩,hb⟩⟩,
  rw ← ha at hb,
  have h_erase_card : ∀ z ∈ prof.cands, finset.card (prof.cands.erase z) = m,
  { intros z  z_in,
    rw finset.card_erase_of_mem z_in,
    exact nat.pred_eq_of_eq_succ hm, },
  suffices : b ≠ y ∧ a ≠ x, 
  { exact (h_uniq b y a x q_in.1 q_in.2 p_in.1 p_in.2 this.1 this.2 
      (or.inl a_neq_b.symm)) hb },
  split,
  { have y_in' : (b, y).snd ∈ prof.cands := by simp only; exact q_in.2,
    rw dif_pos y_in' at hq,
    set prof' : election_profile χ υ := 
    ⟨(prof.cands.erase y), 
     (by rw [h_erase_card y q_in.2, m_succ]; exact nat.zero_lt_succ d), 
     prof.voters, prof.vpos, prof.Q⟩ with h_prof', 
    have b_in' : b ∈ stable_voting prof':= 
      by simpa [stable_voting, h_erase_card y q_in.2] using hq.1,
    exact (finset.mem_erase.1 (mem_cands_of_mem_sv b_in')).1, },
  { have x_in' : (a, x).snd ∈ prof.cands := by simp only; exact p_in.2,
    rw dif_pos x_in' at hp,
    set prof' : election_profile χ υ := 
    ⟨(prof.cands.erase x), 
     (by rw [h_erase_card x p_in.2, m_succ]; exact nat.zero_lt_succ d), 
     prof.voters, prof.vpos, prof.Q⟩ with h_prof', 
    have a_in' : a ∈ stable_voting prof':= 
      by simpa [stable_voting, h_erase_card x p_in.2] using hp.1,
    exact (finset.mem_erase.1 (mem_cands_of_mem_sv a_in')).1, },  
end

lemma sv_winner_unique {χ υ : Type*} (prof : election_profile χ υ) 
  (h : uniquely_weighted prof.voters prof.cands prof.Q) :
  (stable_voting prof).card = 1 :=
sv_winner_unique' prof.cands.card prof rfl h

noncomputable def stable_voting_alt' {χ υ : Type*} (voters : finset υ) (Q : υ → χ → χ → Prop) :
  Π (n : ℕ) (cands : finset χ) (hn : cands.card = n) (cpos : 0 < n), finset χ
| 0 _ _ cpos := (nat.not_lt_zero _ cpos).elim
| 1 cands _ _ := cands
| (n+2) cands hn cpos :=
let
  -- whether c wins when candidate rem is removed
  still_wins (c rem : χ) : Prop :=
    if rem_prop : rem ∈ cands 
      then c ∈ stable_voting_alt' (n+1) (cands.erase rem)
          (by { rw [finset.card_erase_of_mem, hn]; simp [rem_prop], })
          (by omega)
    else false,
  viable : finset (χ × χ) := (cands.product cands).filter 
      (λ p, still_wins p.1 p.2 ∧ is_undefeated voters cands Q p.1)
in finset.image prod.fst $ viable.filter (λ p, (margin voters Q p.1 p.2 = best_margin voters viable Q))

noncomputable def stable_voting_alt {χ υ : Type*} (prof : election_profile χ υ)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] : finset χ :=
stable_voting_alt' prof.voters prof.Q prof.cands.card prof.cands rfl prof.cpos

lemma sv_alt_singleton {χ υ : Type*} (prof : election_profile χ υ) (hcands : prof.cands.card = 1) : 
  stable_voting_alt prof = prof.cands :=
by simp only [stable_voting_alt, stable_voting_alt', hcands]

/-
lemma stable_voting_eq_stable_voting_alt' {χ υ : Type*} :
  ∀ (n : ℕ) (prof : election_profile χ υ), prof.cands.card = n →
  stable_voting prof = stable_voting_alt prof := 
begin
  intro n,
  cases n with d, 
  { intros prof hn, exfalso,
    linarith [hn, prof.cpos], },
  induction d with d IH,
  { intros prof hn,
    rwa [sv_singleton prof hn, sv_alt_singleton prof hn], },
  set m := d.succ with m_succ,
  intros prof hm,
  have card_eq_d : prof.cands.card = d + 2 := by rw hm,
  have h_erase_card : ∀ z ∈ prof.cands, finset.card (prof.cands.erase z) = m,
  { intros z  z_in,
    rw finset.card_erase_of_mem z_in,
    exact nat.pred_eq_of_eq_succ hm, },
  ext a, split,
  { intro a_in,
    have a_undefeated := sv_winner_undefeated a a_in,
    simp only [stable_voting, stable_voting', stable_voting_alt, 
      stable_voting_alt', card_eq_d, finset.filter_congr_decidable,
      exists_prop, exists_and_distrib_right, exists_eq_right, 
      finset.mem_image, finset.mem_filter, prod.exists, finset.mem_product] at ⊢ a_in,
    rcases a_in with ⟨x,⟨⟨p_in,hp⟩,ha⟩⟩,
    refine ⟨x,⟨⟨p_in,⟨_,a_undefeated⟩⟩,_⟩⟩,
    { have x_in' : (a, x).snd ∈ prof.cands := by simp only; exact p_in.2,
      simp only [x_in', dif_pos] at ⊢ hp,
      set prof' : election_profile χ υ := 
        ⟨(prof.cands.erase x), 
         (by rw [h_erase_card x p_in.2, m_succ]; exact nat.zero_lt_succ d), 
         prof.voters, prof.vpos, prof.Q⟩ with h_prof', 
      suffices : a ∈ stable_voting_alt prof',
      { simp only [stable_voting_alt, h_erase_card x p_in.right] at this,
        exact this, },
      have prof'_card : prof'.cands.card = m 
        := by simp only [h_erase_card x p_in.2],
      simpa only [← IH prof' prof'_card, 
        stable_voting, h_erase_card x p_in.2] using hp.1, },
    { convert ha, ext p,
      simp only [eq_self_iff_true] at *,
      sorry, }, },
  { sorry, },
end

def is_stable {χ υ : Type*} (M : election_profile χ υ → finset χ) 
  (prof : election_profile χ υ)  [∀ v, decidable_rel (prof.Q v)] (a: χ) : Prop :=
true
-/