import data.set.finite
import tactic
open finset
/- 
   We think about candidates as type `χ` and voters as type `υ`.

   We say that an "ordering" of candidates is a binary relation `χ → χ → Prop`. 
   Then, an "individual ordering" maps each voter to their own ordering. 
   Therefore, we can express an individual ordering as type `υ → χ → χ → Prop` 
   You can think about an individual ordering as a pile of ballots, where each 
   voter has ranked all candidates against each other. 

   Finally, think about a voting system. The basic inputs of voting system are a 
   finite set of voters, a finite set of candidates, and an inidividual ordering 
   (or a ballot) from each voter to rank each candidate. 
-/
structure election_profile (χ υ : Type*) :=
(cands : finset χ)
(voters : finset υ)
(Q : υ → χ → χ → Prop)

noncomputable def margin {χ υ : Type*} : election_profile χ υ → χ → χ → ℤ := 
λ prof x y, { i ∈ prof.voters | prof.Q i x y }.card 
- { i ∈ prof.voters | prof.Q i y x }.card

example (s : finset ℤ) (hs: s.nonempty) : ∃ b, b = max' s hs := exists_eq

/- We think of the output in this voting system as a finite set because we 
  accept that possibility of multiple "tied" winners. -/
noncomputable def simple_stable_voting {χ υ : Type*} [decidable_eq χ] 
  : election_profile χ υ → finset χ := λ prof,
begin
  obtain ⟨X, V, Q⟩ := prof,
  generalize h : X.card = n,
  cases n with d, { use ∅, },
  induction d with d hd generalizing X, {use X, },
  set m := d.succ with hm,
  have hcard : ∀ b ∈ X, card (erase X b) = m,
  { intros b b_in,
    rw card_erase_of_mem b_in,
    exact nat.pred_eq_of_eq_succ h, },
  let winners_remove : χ → finset χ := λ b,
    if b_in : b ∈ X then hd (erase X b) (hcard b b_in) else ∅,
  let possible_margins := 
    { k : ℤ | ∃ a b ∈ X, k = margin ⟨X, V, Q⟩ a b ∧ a ∈ winners_remove b },
  have h_margins : possible_margins.finite := sorry,
  have margins_nonempty : h_margins.to_finset.nonempty := sorry,
  let max_margin : ℤ := max' h_margins.to_finset margins_nonempty, 
  use { a ∈ X | ∃ b ∈ X, a ∈ winners_remove b ∧ margin ⟨X, V, Q⟩ a b = max_margin },
end