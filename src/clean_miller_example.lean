import data.set.finite
import tactic

structure election_profile (χ υ : Type*) :=
(candidates : finset χ)
(cpos : 0 < candidates.card)
(voters : finset υ)
(ballots : υ → χ → χ → Prop)

instance {α : Type*} (s : finset α) : decidable s.nonempty :=
begin
  rw ←finset.card_pos,
  apply_instance,
end

def simple_stable_voting' {χ υ : Type*} (voters : finset υ) (ballots : υ → χ → χ → Prop)
  [decidable_eq χ]
  [∀ v, decidable_rel (ballots v)] :
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
  -- the margin for candidate c vs c'
  margin (c c' : χ) : ℤ :=
    (voters.filter (λ v, ballots v c c')).card - (voters.filter (λ v, ballots v c' c)).card,
  -- the set of pairs (c, c') of candidates such that when c' is removed, c is a winner.
  viable : finset (χ × χ) := finset.image coe $
    (cands.product cands).attach.filter (λ (p : cands.product cands),
      still_wins p.1.1 p.1.2 (by { cases p, simp at p_property, exact p_property.2, })),
  -- find the maximal margin (using 0 if viable is somehow empty)
  best_margin : ℤ := if hn : viable.nonempty then viable.sup' hn (λ p, margin p.1 p.2) else 0
in finset.image prod.fst $ viable.filter (λ p, margin p.1 p.2 = best_margin)

def simple_stable_voting {χ υ : Type*} (prof : election_profile χ υ)
  [decidable_eq χ] [∀ v, decidable_rel (prof.ballots v)] : finset χ :=
simple_stable_voting' prof.voters prof.ballots prof.candidates.card prof.candidates rfl prof.cpos
