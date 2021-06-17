import logic.relation
import data.finset.basic
import data.set.finite

open relation
open vector
open finset

--we think of social states as type σ and inidividuals as type ι
variables {σ ι : Type}


variables [decidable_eq σ]
variables [decidable_eq ι]
variables {X : finset σ} {N : finset ι}


----------------------------------------------
--Some Basic Definitions and Lemmas
----------------------------------------------

--Definition of a preference ordering
def is_pref_ordering (R :  σ → σ → Prop) : Prop :=
    reflexive R ∧ total R ∧ transitive R

--now, we have to define the 'strict' preference relation P
def P (R  : σ → σ → Prop) (x y : σ) : Prop := (R x y) ∧ ¬ (R y x)

lemma R_of_nP_total {R : σ → σ → Prop} (hR: total R) (x y : σ) : ¬ (P R y x) → R x y :=
begin
    intro h,
    unfold P at h, 
    specialize hR x y,
    push_neg at h,
    by_cases hyp : R y x, exact h hyp,
    rw or_iff_not_imp_right at hR, exact hR hyp,
end

lemma nP_of_reverseP {R : σ → σ → Prop} (x y : σ) (h : P R x y): ¬(P R y x) :=
begin
    unfold P, push_neg,
    intro n, 
    exact h.1,
end 

--what it means for social states to have the "same order" with respect to two relations
def same_order (R R': σ → σ → Prop) (x y x' y' : σ) : Prop :=
    ((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧
    (P R x y ↔ P R' x' y') ∧  (P R y x ↔ P R' y' x')


lemma same_order_of_P_P' {R R': σ → σ → Prop} {x y : σ} (hR : P R x y) (hR' : P R' x y) : 
    same_order R R' x y x y := 
begin
    split, split,
    exact ⟨ (λ h, hR'.1), (λ h, hR.1)⟩,
    split,
    intro h, exfalso, exact hR.2 h,
    intro h, exfalso, exact hR'.2 h,
    split,
    exact ⟨ (λ h, hR'), (λ h, hR)⟩,
    split,
    intro h, exfalso, exact (nP_of_reverseP x y hR) h,
    intro h, exfalso, exact (nP_of_reverseP x y hR') h,
end

lemma same_order_of_reverseP_P' {R R': σ → σ → Prop} {x y : σ} (hR : P R y x) (hR' : P R' y x) : 
    same_order R R' x y x y := 
begin
    split, split, split,
    intro h, exfalso, exact hR.2 h,
    intro h, exfalso, exact hR'.2 h,
    exact ⟨ (λ h, hR'.1), (λ h, hR.1)⟩,
    split, split,
    intro h, exfalso, exact (nP_of_reverseP x y hR) h,
    intro h, exfalso, exact (nP_of_reverseP x y hR') h,
    exact ⟨ (λ h, hR'), (λ h, hR)⟩,
end


/- a social state is extremal with respect to a relation and a set of individuals
if every individual ranks that social state either highest or lowest -/
def is_extremal (R  : σ → σ → Prop) (X : finset σ) (s : σ) : Prop := 
    s ∈ X ∧ ((∀ t ∈ X, t ≠ s → P R t s) ∨ (∀ t ∈ X,  t ≠ s → P R s t))


----------------------------
--The important part!!!!!!
-----------------------------


/-We think of a preference as a relation of type σ → σ → Prop. 
We think of an individual preference as a mapping from each individual of type ι to a preference.
A choice function is a mapping from an individual preference to a preference. 

That is, a choice function has this type: 
(ι → σ → σ → Prop) → (σ → σ → Prop)

-/

---TODO: not sure if I've defined this one right
def unrestricted_domain (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) : Prop := 
    (∀ (m : ℕ) (n : fin (m+1) ) (V : vector (finset ι) n) (T : vector (vector σ m) n),
    ∃Rᵢ  : ι → (σ → σ → Prop), ∀ (i : ι) (j : fin n) (k k': fin m), i ∈ nth V j → k > k' →
        P (Rᵢ i) (nth (nth T j) k) (nth (nth T j) k') )

def weak_pareto (f : (ι → σ → σ → Prop) → σ → σ → Prop) (X : finset σ) (N : finset ι) : Prop 
    := ∀ (x y ∈ X) (Rᵢ : ι → (σ → σ → Prop)), (∀i ∈ N,  P (Rᵢ i) x y) → P (f Rᵢ) x y

def ind_of_irr_alts (f : (ι → σ → σ → Prop) → (σ → σ → Prop) ) (X : finset σ) (N : finset ι) : Prop :=
    ∀ (Rᵢ Rᵢ' : ι → (σ → σ → Prop)) (x y ∈ X), (∀i ∈ N, same_order (Rᵢ i) (Rᵢ' i) x y x y)
    → same_order (f Rᵢ) (f Rᵢ') x y x y

def is_arrovian (f : (ι → σ → σ → Prop) → (σ → σ → Prop) ) (X : finset σ) (N : finset ι): Prop :=
    unrestricted_domain f ∧ weak_pareto f X N ∧ ind_of_irr_alts f X N
    ∧ ∀ (Rᵢ : (ι → σ → σ → Prop)), is_pref_ordering (f Rᵢ)




--First step of Arrow's theorem!
--If every individual in society places a social state at the top or bottom of their social preferences,
--then society must place that social state at the top or bottom of its social preference. 
-------------------------------------------
lemma extremal_soc_of_extremal_indiv {f : (ι → σ → σ → Prop) → (σ → σ → Prop)}
    (hf : is_arrovian f X N)
    (hX : finset.card X ≥ 3)
    (b : σ) (b_in : b ∈ X ) (R : (ι → σ → σ → Prop) )
    (hyp : ∀ i ∈ N, is_extremal (R i) X b ) :
    is_extremal (f R) X b :=
begin
    by_contradiction h,
    unfold is_extremal at h,
    push_neg at h,
    specialize h b_in,
    cases h with hc ha,
    rcases ha with ⟨a, a_in, a_ne, ha⟩, rcases hc with ⟨c, c_in, c_ne, hc⟩,
    replace ha : (f R) a b := R_of_nP_total (hf.2.2.2 R).2.1 a b ha,
    replace hc : (f R) b c := R_of_nP_total (hf.2.2.2 R).2.1 b c hc,
    have hR₂ : ∃ (R₂ : ι → σ → σ → Prop), ∀ i ∈ N, P (R₂ i) c a ∧
        same_order (R i) (R₂ i) b a b a ∧ same_order (R i) (R₂ i) b c b c,

        let I₁ := { i ∈ N | P (R i) c b ∧ P (R i) a b },
        let I₂ := { i ∈ N | P (R i) b c ∧ P (R i) b a },
        let I := [I₁, I₂],
        have I_length : I.length = 2 := by simp,
        let T₁ := [b, a, c], let T₂ := [a, c, b],
        have T₁_length : T₁.length = 3 := by simp, have T₂_length : T₂.length = 3 := by simp,
        let T₁_vec : vector σ 3 := ⟨T₁, T₁_length⟩, let T₂_vec : vector σ 3 := ⟨T₂, T₂_length⟩,
        let T := [T₁_vec, T₂_vec],
        have T_length : T.length = 2 := by simp,
        obtain ⟨R₂, hR₂ ⟩ := hf.1 3 2 ⟨I, I_length⟩ ⟨T, T_length⟩,
        use R₂,
        intros i i_in,
        specialize hyp i i_in, unfold is_extremal at hyp,
        by_cases h : ∀ t ∈ X, t ≠ b → P (R i) b t,

            {have i_and : P (R i) b c ∧ P (R i) b a := ⟨h c c_in c_ne, h a a_in a_ne⟩,
            have i_in' : i ∈ I₂ := by tidy,
            have hI₂ : I₂ = nth ⟨I, I_length⟩ 1 := rfl, rw hI₂ at i_in',
            have R₂a : ((nth ⟨T, T_length⟩ 1).nth 0) = a := rfl,
            have R₂b : ((nth ⟨T, T_length⟩ 1).nth 2) = b := rfl,
            have R₂c : ((nth ⟨T, T_length⟩ 1).nth 1) = c := rfl,
            have R₂ba := hR₂ i  (1 : fin 2) 2 0 i_in' dec_trivial, rw [R₂b, R₂a] at R₂ba,
            have R₂bc := hR₂ i  (1 : fin 2) 2 1 i_in' dec_trivial, rw [R₂b, R₂c] at R₂bc,
            have R₂ca := hR₂ i  (1 : fin 2) 1 0 i_in' dec_trivial, rw [R₂c, R₂a] at R₂ca,
            exact ⟨R₂ca, same_order_of_P_P' (h a a_in a_ne) R₂ba,  
                         same_order_of_P_P' (h c c_in c_ne) R₂bc⟩},

            {rw or_iff_not_imp_right at hyp,
            replace h:= hyp.2 h,
            have i_and : P (R i) c b ∧ P (R i) a b := ⟨h c c_in c_ne, h a a_in a_ne⟩,
            have i_in' : i ∈ I₁ := by tidy,
            have hI₁ : I₁ = nth ⟨I, I_length⟩ 0 := rfl, rw hI₁ at i_in',
            have R₂a : ((nth ⟨T, T_length⟩ 0).nth 1) = a := rfl,
            have R₂b : ((nth ⟨T, T_length⟩ 0).nth 0) = b := rfl,
            have R₂c : ((nth ⟨T, T_length⟩ 0).nth 2) = c := rfl,
            have R₂ab := hR₂ i  (0 : fin 2) 1 0 i_in' dec_trivial, rw [R₂a, R₂b] at R₂ab,
            have R₂cb := hR₂ i  (0 : fin 2) 2 0 i_in' dec_trivial, rw [R₂c, R₂b] at R₂cb,
            have R₂ca := hR₂ i  (0 : fin 2) 2 1 i_in' dec_trivial, rw [R₂c, R₂a] at R₂ca,
            exact ⟨R₂ca, same_order_of_reverseP_P' (h a a_in a_ne) R₂ab,  
                         same_order_of_reverseP_P' (h c c_in c_ne) R₂cb⟩},

    cases hR₂ with R₂ hR₂,
    have h_pareto := hf.2.1 c a c_in a_in R₂ (λ i i_in, (hR₂ i i_in).1),
    have same_order_ba := hf.2.2.1 R R₂ b a b_in a_in (λ i i_in, (hR₂ i i_in).2.1), 
    have same_order_bc := hf.2.2.1 R R₂ b c b_in c_in (λ i i_in, (hR₂ i i_in).2.2), 
    have h_trans := (hf.2.2.2 (R₂)).2.2 (same_order_ba.1.2.1 ha) (same_order_bc.1.1.1 hc),
    exact h_pareto.2 h_trans,
end
