import data.set.finite
import data.set.basic 
import tactic

open relation vector finset

--we think of social states as type σ and inidividuals as type ι
variables {σ ι : Type} [decidable_eq σ] [decidable_eq ι]

variables {x y x' y' a b : σ} 
          {R R' : σ → σ → Prop} 

----------------------------------------------
--Some Basic Definitions and Lemmas
----------------------------------------------

--Definition of a preference ordering
def is_pref_ordering (R : σ → σ → Prop) : Prop :=
reflexive R ∧ total R ∧ transitive R

--now, we have to define the 'strict' preference relation P
def P (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ ¬ R y x -- accepts a relation and two social states

def acyclical (R : σ → σ → Prop) : Prop := 
¬ ∃ x : σ, trans_gen (P R) x x

lemma R_of_nP_total (hR: total R) (h : ¬ P R y x) : R x y :=
begin
  by_cases hyp : R y x,
  exacts [not_and_not_right.mp h hyp, or_iff_not_imp_right.mp (hR x y) hyp],
end

lemma nP_of_reverseP (h : P R x y) : ¬ P R y x :=
not_and_not_right.mpr $ λ n, h.1

lemma false_of_P_self (h : P R x x) : false := 
(and_not_self _).mp h


--what it means for social states to have the "same order" with respect to two relations
def same_order (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧ (P R x y ↔ P R' x' y') ∧ (P R y x ↔ P R' y' x')

lemma same_order_of_P_P' (hR : P R x y) (hR' : P R' x y) : same_order R R' x y x y := 
⟨⟨⟨λ h, hR'.1, λ h, hR.1⟩, ⟨hR.2.elim, hR'.2.elim⟩⟩, 
  ⟨⟨λ h, hR', λ h, hR⟩, ⟨(nP_of_reverseP hR).elim, (nP_of_reverseP hR').elim⟩⟩⟩

lemma same_order_of_reverseP_P' (hR : P R y x) (hR' : P R' y x) : same_order R R' x y x y :=
⟨⟨⟨hR.2.elim, hR'.2.elim⟩, ⟨λ h, hR'.1, λ h, hR.1⟩⟩, 
  ⟨⟨(nP_of_reverseP hR).elim, (nP_of_reverseP hR').elim⟩, ⟨λ h, hR', λ h, hR⟩⟩⟩


def is_maximal_element (x : σ) (S : finset σ) (R : σ → σ → Prop) : Prop :=
¬ ∃ y ∈ S, P R y x

def is_best_element (x : σ) (S : finset σ) (R : σ → σ → Prop) : Prop :=
∀ y ∈ S, R y x

noncomputable def maximal_set (S : finset σ) (R: σ → σ → Prop) : finset σ := 
{ x ∈ S | is_maximal_element x S R }

noncomputable def choice_set (S : finset σ) (R: σ → σ → Prop) : finset σ := 
{ x ∈ S | is_best_element x S R }


lemma cyclical_of_no_highest (R : σ → σ → Prop) (S : finset σ) (hS : S.nonempty) 
  (hR : ∀a ∈ S, ∃b ∈ S, R b a) :
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


theorem best_elem_iff_acyclical [fintype σ] 
(hrfl : reflexive R) (htot : total R) : 
(∀ X : finset σ, X.nonempty → ∃ b ∈ X, is_best_element b X R) ↔ (acyclical R) := 
begin
  split,
  { /-
    intro h_best,
    unfold acyclical, 
    by_contradiction h,
    rcases h with ⟨x, hx⟩,
    let S : finset σ := {a ∈ univ | trans_gen (P R) a a },
    specialize h_best S,
    rcases h_best with ⟨b, b_in, hb⟩,
    have x_in : x ∈ S := by simp only [S, true_and, sep_def, mem_filter, mem_univ];
      exact hx, 
    simp only [S, true_and, sep_def, mem_filter, mem_univ] at b_in,
    rw trans_gen.tail'_iff at b_in,
    rcases b_in with ⟨c, hc₁, hc₂⟩,
    specialize hb,-/
    sorry,  },
  { by_cases h : ∀ a c : σ, R a c ∧ R c a,
    { intros h_acyc X X_ne,
      rcases X_ne with ⟨b, b_in⟩,
      refine ⟨b, b_in, _⟩,
      

    },
    { sorry, }, },
end