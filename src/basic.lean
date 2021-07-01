import data.set.finite
import tactic

open relation vector finset

--we think of social states as type σ and inidividuals as type ι
variables {σ ι : Type} {x y x' y' a b : σ} {R R' : σ → σ → Prop} 

----------------------------------------------
--Some Basic Definitions and Lemmas
----------------------------------------------

--Definition of a preference ordering
def is_pref_ordering (R : σ → σ → Prop) : Prop :=
reflexive R ∧ total R ∧ transitive R

--now, we have to define the 'strict' preference relation P
def P (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ ¬ R y x -- accepts a relation and two social states

def acyclical (R : σ → σ → Prop) : Prop := 
∀ x : σ, ¬trans_gen (P R) x x

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
∀ y ∈ S, ¬P R y x

def is_best_element (x : σ) (S : finset σ) (R : σ → σ → Prop) : Prop :=
∀ y ∈ S, R x y

noncomputable def maximal_set (S : finset σ) (R: σ → σ → Prop) : finset σ := 
{x ∈ S | is_maximal_element x S R}

noncomputable def choice_set (S : finset σ) (R: σ → σ → Prop) : finset σ := 
{x ∈ S | is_best_element x S R}


lemma cyclical_of_no_highest (R : σ → σ → Prop) {S : finset σ} (hS : S.nonempty) 
  (hR : ∀ a ∈ S, ∃ b ∈ S, R b a) :
  ∃ c ∈ S, trans_gen R c c :=
begin
  classical,
  replace hR : ∀ a ∈ S, ∃ b ∈ S, trans_gen R b a :=
    λ a ha, let ⟨b, hb, h⟩ := hR a ha in ⟨b, hb, trans_gen.single h⟩, -- maybe just make this the assumption istead of `hR`?
  refine finset.induction_on S (by rintro ⟨_, ⟨⟩⟩) _ hS hR,
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
and sufficient condition for a choice function to be defined on every finset `X`. 
-/
theorem best_elem_iff_acyclical [fintype σ] 
  (htot : total R) : 
  (∀ X : finset σ, X.nonempty → ∃ b ∈ X, is_best_element b X R) ↔ acyclical R := 
begin
  classical,
  refine ⟨λ h x hx, _, λ h_acyc X X_ne, _⟩,
  { obtain ⟨b, b_in, hb⟩ := h {a ∈ univ | trans_gen (P R) a x ∧ trans_gen (P R) x a} ⟨x, by simpa⟩, -- can we maybe pull this sort of thing out into its own general lemma?
    simp only [true_and, sep_def, mem_filter, mem_univ] at b_in,
    rcases trans_gen.tail'_iff.mp b_in.2 with ⟨c, hc₁, hc₂⟩,
    refine hc₂.2 (hb c _),
    simp [b_in.1.head hc₂, hx.trans_left hc₁] },
  { by_contra h,
    suffices : ∃ c ∈ X, trans_gen (P R) c c, from let ⟨c, _, hc⟩ := this in h_acyc c hc,
    refine cyclical_of_no_highest (P R) X_ne (λ a a_in, _),
    simp only [is_best_element, not_exists, not_forall] at h,
    obtain ⟨b, b_in, hb⟩ := h a a_in,
    exact ⟨b, b_in, ⟨(htot a b).resolve_left hb, hb⟩⟩ },
end
