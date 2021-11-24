import data.set.finite
import tactic

structure election_profile (χ υ : Type*) :=
(candidates : finset χ)
(cpos : 0 < candidates.card)
(voters : finset υ)
(vpos : 0 < voters.card)
(Q : υ → χ → χ → Prop)

instance {α : Type*} (s : finset α) : decidable s.nonempty :=
begin
  rw ←finset.card_pos,
  apply_instance,
end

def margin {χ υ : Type*} (voters : finset υ) (Q : υ → χ → χ → Prop) (c c' : χ) 
  [∀ v, decidable_rel (Q v)] : ℤ :=
(voters.filter (λ v, Q v c c')).card - (voters.filter (λ v, Q v c' c)).card

def best_margin {χ υ : Type*} (voters : finset υ) (s : finset (χ × χ)) (Q : υ → χ → χ → Prop) 
  [∀ v, decidable_rel (Q v)] : ℤ :=
  if hn : s.nonempty
    then s.sup' hn (λ p, margin voters Q p.1 p.2) 
  else 0

def simple_stable_voting' {χ υ : Type*} (voters : finset υ) (Q : υ → χ → χ → Prop)
  [decidable_eq χ] 
  [∀ v, decidable_rel (Q v)] :
  Π (n : ℕ) (candidates : finset χ) (hn : candidates.card = n) (cpos : 0 < n), finset χ
| 0 _ _ cpos := (nat.not_lt_zero _ cpos).elim
| 1 candidates _ _ := candidates
| (n+2) cands hn cpos :=
let
  -- whether c wins when candidate rem is removed
  still_wins (c rem : χ) : Prop :=
    if rem_prop : rem ∈ cands 
      then c ∈ simple_stable_voting' (n+1) (cands.erase rem)
          (by { rw [finset.card_erase_of_mem, hn]; simp [rem_prop], })
          (by omega)
    else false,
  viable : finset (χ × χ) := (cands.product cands).filter 
      (λ p, /-p.2 ∈ cands ∧ -/ still_wins p.1 p.2 )
in finset.image prod.fst $ viable.filter (λ p, (margin voters Q p.1 p.2 = best_margin voters viable Q))

def simple_stable_voting {χ υ : Type*} (prof : election_profile χ υ)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] : finset χ :=
simple_stable_voting' prof.voters prof.Q prof.candidates.card prof.candidates rfl prof.cpos

lemma ssv_singleton {χ υ : Type*} (prof : election_profile χ υ) (hcands : prof.candidates.card = 1)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] : 
  simple_stable_voting prof = prof.candidates :=
by simp only [simple_stable_voting, simple_stable_voting', hcands]

lemma exists_best_margin {χ υ : Type*} {s : finset (χ × χ)} (voters : finset υ) (Q : υ → χ → χ → Prop) 
  [∀ v, decidable_rel (Q v)] (hs : s.nonempty) :
  ∃ p : χ × χ, p ∈ s ∧ margin voters Q p.1 p.2 = best_margin voters s Q :=
begin
  unfold best_margin,
  simp only [hs, dif_pos],
  obtain ⟨b, b_in, hb⟩ := finset.exists_mem_eq_sup' hs (λ (p : χ × χ), margin voters Q p.fst p.snd),
  use ⟨b, b_in, hb.symm⟩, 
end 

open_locale classical

lemma exists_eq_plus_two (n : ℕ) (hn₀ : ¬ n = 0) (hn₁ : ¬ n = 1) : 
  ∃ m, n = m + 2 :=
begin
  cases n with d, { exact (hn₀ nat.nat_zero_eq_zero).elim, },
  induction d with d hd, {exact (hn₁ rfl).elim, },
  use d,
end

lemma mem_cands_of_mem_winners {χ υ : Type*} (prof : election_profile χ υ) (a : χ)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] : 
  a ∈ simple_stable_voting prof → a ∈ prof.candidates := 
begin
  intro a_in,
  by_cases hcands : prof.candidates.card = 1, 
  { rwa ssv_singleton prof hcands at a_in, },
  obtain ⟨n, hn⟩ := exists_eq_plus_two prof.candidates.card (by linarith [prof.cpos]) hcands, 
  simp only [simple_stable_voting, simple_stable_voting', hn, 
    exists_prop, exists_and_distrib_right, exists_eq_right,
    finset.mem_image, finset.mem_filter, finset.filter_congr_decidable, 
    prod.exists, finset.mem_product] at a_in,
  rcases a_in with ⟨b,⟨⟨p_in,hp⟩,ha⟩⟩,
  exact p_in.1,
end

lemma exists_ssv_winner' {χ υ : Type*} :
  ∀ (n : ℕ) (prof : election_profile χ υ), prof.candidates.card = n → 
  ∃ a, a ∈ simple_stable_voting prof :=
begin
  intro n,
  cases n with d, 
  { intros prof hn,
    linarith [hn, prof.cpos], },
  induction d with d IH,
  { intros prof hn,
    rw ssv_singleton prof hn,
    exact finset.card_pos.1 prof.cpos, },
  intros prof hm,
  set m := d.succ with m_succ,
  obtain ⟨b, b_in⟩ := finset.card_pos.1 prof.cpos,
  have h_erase_card : ∀ z ∈ prof.candidates, finset.card (prof.candidates.erase z) = m,
    { intros z z_in,
      rw finset.card_erase_of_mem z_in,
      exact nat.pred_eq_of_eq_succ hm, },
  set prof' : election_profile χ υ := 
    ⟨(prof.candidates.erase b), 
     (by rw (h_erase_card b b_in); omega), 
     prof.voters, prof.vpos, prof.Q⟩ with h_prof',
  have prof'_cands : prof'.candidates.card = m := by rw ← h_erase_card b b_in, 
  obtain ⟨a, a_in⟩ := IH prof' prof'_cands,
  have card_eq_d : prof.candidates.card = d + 2 := by rw hm,
  simp only [simple_stable_voting, simple_stable_voting', card_eq_d, 
    exists_prop, exists_and_distrib_right, exists_eq_right,
    finset.mem_image, finset.mem_filter, finset.filter_congr_decidable,
    prod.exists, finset.mem_product],
  set viable_set : finset (χ × χ) := (prof.candidates.product prof.candidates).filter
    (λ p, if p2_in : p.2 ∈ prof.candidates 
      then p.1 ∈ simple_stable_voting' prof.voters prof.Q d.succ (prof.candidates.erase p.2)
          ( by rwa h_erase_card p.snd p2_in) (nat.succ_pos d)
      else false)
    with hvs,
  have viable_nonempty : viable_set.nonempty,
  { use ⟨a,b⟩,
    have : a ∈ (prof.candidates.erase b) := 
      by simp only [mem_cands_of_mem_winners prof' a a_in],
    simp only [simple_stable_voting, h_prof', h_erase_card b b_in, m_succ] at a_in,
    simp only [finset.mem_filter, finset.mem_product, b_in, 
      dif_pos, dif_pos, and_true, finset.mem_filter, finset.mem_product],
    exact ⟨(finset.mem_erase.1 this).2, a_in⟩, },  
  obtain ⟨p, p_in, hp⟩ := exists_best_margin prof.voters prof.Q viable_nonempty,
  refine ⟨p.1, p.2, ⟨_,_⟩⟩,
  { rw hvs at p_in,
    simp only [finset.mem_filter] at p_in,
    cases p_in with hp₁ hp₂,
    refine ⟨finset.mem_product.1 hp₁, _⟩,
    simp only [(finset.mem_product.mp hp₁).right, dif_pos, finset.mem_product,
      true_and, dif_pos, finset.mem_product, true_and,
      dif_pos, finset.mem_product] at *,
    exact hp₂, },
  { convert hp, },
end

lemma exists_ssv_winner {χ υ : Type*} (prof : election_profile χ υ) :
  ∃ a, a ∈ simple_stable_voting prof := exists_ssv_winner' prof.candidates.card prof rfl 