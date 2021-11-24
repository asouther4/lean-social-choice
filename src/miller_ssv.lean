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
  still_wins (c rem : χ) (rem_prop : rem ∈ cands) : Prop :=
    c ∈ simple_stable_voting' (n+1) (cands.erase rem)
          (by { rw [finset.card_erase_of_mem, hn]; simp [rem_prop], })
          (by omega),
  viable : finset (χ × χ) := finset.image coe $
    (cands.product cands).attach.filter (λ (p : cands.product cands),
      still_wins p.1.1 p.1.2 (by { cases p, simp at p_property, exact p_property.2, }))
in finset.image prod.fst $ viable.filter (λ p, (margin voters Q p.1 p.2 = best_margin voters viable Q))

def simple_stable_voting {χ υ : Type*} (prof : election_profile χ υ)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] : finset χ :=
simple_stable_voting' prof.voters prof.Q prof.candidates.card prof.candidates rfl prof.cpos

lemma ssv_singleton {χ υ : Type*} (prof : election_profile χ υ) (hcands : prof.candidates.card = 1)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] : 
  simple_stable_voting prof = prof.candidates :=
by simp only [simple_stable_voting, simple_stable_voting', hcands]

lemma ssv_singleton' {χ υ : Type*} (prof : election_profile χ υ) (hcands : prof.candidates.card = 1)
  [decidable_eq χ] [∀ v, decidable_rel (prof.Q v)] :
  simple_stable_voting prof = prof.candidates :=
begin
  unfold simple_stable_voting,
  convert simple_stable_voting'._main.equations._eqn_2 prof.voters prof.Q _ hcands (dec_trivial),
  simp only [hcands],
  congr',
end

open_locale classical

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
  have h_erase_b : finset.card (prof.candidates.erase b) = m,
    { rw finset.card_erase_of_mem b_in,
      exact nat.pred_eq_of_eq_succ hm, },
  set prof' : election_profile χ υ := 
    ⟨(prof.candidates.erase b), 
     (by rw h_erase_b; omega), 
     prof.voters, prof.vpos, prof.Q⟩ with h_prof',
  have prof'_cands : prof'.candidates.card = m := by rw ← h_erase_b, 
  obtain ⟨a, a_in⟩ := IH prof' prof'_cands,
  use a,
  have card_eq_d : prof.candidates.card = d + 2 := sorry, 
  simp only [simple_stable_voting, simple_stable_voting', card_eq_d, true_and, 
    finset.mem_attach, exists_prop,
    exists_and_distrib_right, prod.mk.inj_iff, exists_eq_right_right, 
    exists_eq_right, finset.mem_image, subtype.exists,
    finset.mem_filter, finset.filter_congr_decidable, subtype.coe_mk, 
    subtype.val_eq_coe, prod.exists, finset.mem_product],
  sorry,

end

lemma exists_ssv_winner {χ υ : Type*} (prof : election_profile χ υ) :
  ∃ a, a ∈ simple_stable_voting prof := exists_ssv_winner' prof.candidates.card prof rfl 

#print prefix simple_stable_voting'