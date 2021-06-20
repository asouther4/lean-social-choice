import logic.relation
import data.set.finite
import tactic

open relation vector finset

--we think of social states as type σ and inidividuals as type ι
variables {σ ι : Type} [decidable_eq σ] [decidable_eq ι]

variables {x y x' y' a b : σ} -- social states
					{R R' : σ → σ → Prop} --relations between social states (Andrew did I get this right?)

----------------------------------------------
--Some Basic Definitions and Lemmas
----------------------------------------------

--Definition of a preference ordering
def is_pref_ordering (R : σ → σ → Prop) : Prop :=
reflexive R ∧ total R ∧ transitive R

--now, we have to define the 'strict' preference relation P
def P (R  : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ ¬ R y x

lemma R_of_nP_total (hR: total R) (h : ¬ P R y x) : R x y :=
begin
	unfold P at h, 
	specialize hR x y,
	push_neg at h,
	by_cases hyp : R y x, exact h hyp,
	rw or_iff_not_imp_right at hR, exact hR hyp,
end

lemma nP_of_reverseP (h : P R x y) : ¬ P R y x :=
begin
	unfold P, push_neg,
	intro n, 
	exact h.1,
end 

lemma false_of_P_self (h : P R x x) : false := 
by simpa only [P, and_not_self] using h


--what it means for social states to have the "same order" with respect to two relations
def same_order (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧ (P R x y ↔ P R' x' y') ∧ (P R y x ↔ P R' y' x')


lemma same_order_of_P_P' (hR : P R x y) (hR' : P R' x y) : same_order R R' x y x y := 
begin
	split, split,
	exact ⟨(λ h, hR'.1), (λ h, hR.1)⟩,
	split,
	intro h, exfalso, exact hR.2 h,
	intro h, exfalso, exact hR'.2 h,
	split,
	exact ⟨ (λ h, hR'), (λ h, hR)⟩,
	split,
	intro h, exfalso, exact (nP_of_reverseP hR) h,
	intro h, exfalso, exact (nP_of_reverseP hR') h,
end

lemma same_order_of_reverseP_P' (hR : P R y x) (hR' : P R' y x) : same_order R R' x y x y := 
begin
	split, split, split,
	intro h, exfalso, exact hR.2 h,
	intro h, exfalso, exact hR'.2 h,
	exact ⟨(λ h, hR'.1), (λ h, hR.1)⟩,
	split, split,
	intro h, exfalso, exact (nP_of_reverseP hR) h,
	intro h, exfalso, exact (nP_of_reverseP hR') h,
	exact ⟨(λ h, hR'), (λ h, hR)⟩,
end


/- a social state is extremal with respect to a relation and a set of individuals
if every individual ranks that social state either highest or lowest -/
def is_extremal (R  : σ → σ → Prop) (X : finset σ) (s : σ) : Prop := 
s ∈ X ∧ ((∀ t ∈ X, t ≠ s → P R t s) ∨ (∀ t ∈ X,  t ≠ s → P R s t))


----------------------------
--The important part!!!!!!
-----------------------------


/- We think of a preference as a relation of type σ → σ → Prop. 
We think of an individual preference as a mapping from each individual of type ι to a preference.
A choice function is a mapping from an individual preference to a preference. 

That is, a choice function has this type: 
(ι → σ → σ → Prop) → (σ → σ → Prop)
-/
variables {f : (ι → σ → σ → Prop) → (σ → σ → Prop)} -- our "election process"
					{Rᵢ : ι → (σ → σ → Prop)} --so I think of this as a function which accepts an individual and outputs a relation R but I'm not sure how to describe it using the proper vocablary - Ben
					{X : finset σ} --a finite set of social states
					{N : finset ι} --a finite set of individuals

---TODO: not sure if I've defined this one right
def unrestricted_domain (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) : Prop := 
(∀ (m : ℕ) (n : fin (m+1)) (V : vector (finset ι) n) (T : vector (vector σ m) n),
  ∃ Rᵢ : ι → (σ → σ → Prop), ∀ (i : ι) (j : fin n) (k k': fin m), i ∈ nth V j → k > k' →
    P (Rᵢ i) (nth (nth T j) k) (nth (nth T j) k') )

def weak_pareto (f : (ι → σ → σ → Prop) → σ → σ → Prop) (X : finset σ) (N : finset ι) : Prop := 
∀ (x y ∈ X) (Rᵢ : ι → (σ → σ → Prop)), (∀i ∈ N,  P (Rᵢ i) x y) → P (f Rᵢ) x y

def ind_of_irr_alts (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (X : finset σ) (N : finset ι) : Prop :=
∀ (Rᵢ Rᵢ' : ι → (σ → σ → Prop)) (x y ∈ X), (∀i ∈ N, same_order (Rᵢ i) (Rᵢ' i) x y x y) → 
	same_order (f Rᵢ) (f Rᵢ') x y x y

def is_arrovian (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (X : finset σ) (N : finset ι) : Prop :=
unrestricted_domain f ∧ weak_pareto f X N ∧ ind_of_irr_alts f X N ∧ ∀ (Rᵢ : (ι → σ → σ → Prop)), is_pref_ordering (f Rᵢ)

def is_dictatorship (f : (ι → σ → σ → Prop) → (σ → σ → Prop) ) (X : finset σ) (N : finset ι) : Prop :=
∃ i ∈ N, ∀ (x y ∈ X) (Rᵢ : ι → (σ → σ → Prop)), P (Rᵢ i) x y → P (f Rᵢ) x y




--First step of Arrow's theorem!
--If every individual in society places a social state at the top or bottom of their social preferences,
--then society must place that social state at the top or bottom of its social preference. 
-------------------------------------------
lemma first_step (hf : is_arrovian f X N) (hX : card X ≥ 3) (b : σ) (b_in : b ∈ X ) (R : (ι → σ → σ → Prop))
	(hyp : ∀ i ∈ N, is_extremal (R i) X b) :
	is_extremal (f R) X b :=
begin
	by_contradiction h,
	unfold is_extremal at h,
	push_neg at h,
	specialize h b_in,
	cases h with hc ha,
	rcases ha with ⟨a, a_in, a_ne, ha⟩, rcases hc with ⟨c, c_in, c_ne, hc⟩,
	replace ha : (f R) a b := R_of_nP_total (hf.2.2.2 R).2.1 ha,
	replace hc : (f R) b c := R_of_nP_total (hf.2.2.2 R).2.1 hc,
	have hR₂ : ∃ (R₂ : ι → σ → σ → Prop), ∀ i ∈ N, 
							P (R₂ i) c a ∧ same_order (R i) (R₂ i) b a b a ∧ same_order (R i) (R₂ i) b c b c,
 	{ let I₁ := {i ∈ N | P (R i) c b ∧ P (R i) a b},
		let I₂ := {i ∈ N | P (R i) b c ∧ P (R i) b a},
		let I := [I₁, I₂],
		have I_length : I.length = 2 := by simp,
		let T₁ := [b, a, c], let T₂ := [a, c, b],
		have T₁_length : T₁.length = 3 := by simp, have T₂_length : T₂.length = 3 := by simp,
		let T₁_vec : vector σ 3 := ⟨T₁, T₁_length⟩, let T₂_vec : vector σ 3 := ⟨T₂, T₂_length⟩,
		let T := [T₁_vec, T₂_vec],
		have T_length : T.length = 2 := by simp,
		obtain ⟨R₂, hR₂⟩ := hf.1 3 2 ⟨I, I_length⟩ ⟨T, T_length⟩,
		use R₂,
		intros i i_in,
		specialize hyp i i_in, unfold is_extremal at hyp,
		by_cases h : ∀ t ∈ X, t ≠ b → P (R i) b t,
		{ have i_and : P (R i) b c ∧ P (R i) b a := ⟨h c c_in c_ne, h a a_in a_ne⟩,
			have i_in' : i ∈ I₂ := by tidy,
			have hI₂ : I₂ = nth ⟨I, I_length⟩ 1 := rfl, rw hI₂ at i_in',
			have R₂a : ((nth ⟨T, T_length⟩ 1).nth 0) = a := rfl,
			have R₂b : ((nth ⟨T, T_length⟩ 1).nth 2) = b := rfl,
			have R₂c : ((nth ⟨T, T_length⟩ 1).nth 1) = c := rfl,
			have R₂ba := hR₂ i (1 : fin 2) 2 0 i_in' dec_trivial, rw [R₂b, R₂a] at R₂ba,
			have R₂bc := hR₂ i (1 : fin 2) 2 1 i_in' dec_trivial, rw [R₂b, R₂c] at R₂bc,
			have R₂ca := hR₂ i (1 : fin 2) 1 0 i_in' dec_trivial, rw [R₂c, R₂a] at R₂ca,
			exact ⟨R₂ca, same_order_of_P_P' (h a a_in a_ne) R₂ba, same_order_of_P_P' (h c c_in c_ne) R₂bc⟩ },
		{ rw or_iff_not_imp_right at hyp,
			replace h:= hyp.2 h,
			have i_and : P (R i) c b ∧ P (R i) a b := ⟨h c c_in c_ne, h a a_in a_ne⟩,
			have i_in' : i ∈ I₁ := by tidy,
			have hI₁ : I₁ = nth ⟨I, I_length⟩ 0 := rfl, rw hI₁ at i_in',
			have R₂a : ((nth ⟨T, T_length⟩ 0).nth 1) = a := rfl,
			have R₂b : ((nth ⟨T, T_length⟩ 0).nth 0) = b := rfl,
			have R₂c : ((nth ⟨T, T_length⟩ 0).nth 2) = c := rfl,
			have R₂ab := hR₂ i (0 : fin 2) 1 0 i_in' dec_trivial, rw [R₂a, R₂b] at R₂ab,
			have R₂cb := hR₂ i (0 : fin 2) 2 0 i_in' dec_trivial, rw [R₂c, R₂b] at R₂cb,
			have R₂ca := hR₂ i (0 : fin 2) 2 1 i_in' dec_trivial, rw [R₂c, R₂a] at R₂ca,
			exact ⟨R₂ca, same_order_of_reverseP_P' (h a a_in a_ne) R₂ab, same_order_of_reverseP_P' (h c c_in c_ne) R₂cb⟩ } },
	cases hR₂ with R₂ hR₂,
	have h_pareto := hf.2.1 c a c_in a_in R₂ (λ i i_in, (hR₂ i i_in).1),
	have same_order_ba := hf.2.2.1 R R₂ b a b_in a_in (λ i i_in, (hR₂ i i_in).2.1), 
	have same_order_bc := hf.2.2.1 R R₂ b c b_in c_in (λ i i_in, (hR₂ i i_in).2.2), 
	have h_trans := (hf.2.2.2 (R₂)).2.2 (same_order_ba.1.2.1 ha) (same_order_bc.1.1.1 hc),
	exact h_pareto.2 h_trans,
end

lemma vector_of_finset {α : Type} {n : ℕ} (S : finset α) (h : card S = n) :
  ∃ v : vector α n, ∀ a ∈ S, ∃ k : fin n, vector.nth v k = a :=
begin
  rcases S with ⟨⟨l⟩, (hl : l.nodup)⟩,
  change l.length = n at h,
  refine ⟨⟨l, h⟩, λ a ha, _⟩,
  rcases list.nth_le_of_mem ha with ⟨k, hk, e⟩,
  refine ⟨⟨k, by rwa ← h⟩, e⟩,
end

def is_pivotal (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (N : finset ι) (X : finset σ) (n : ι) (b : σ) : Prop := 
∃ (R₁ R₂ : ι → σ → σ → Prop),
	(∀ i ∈ N, i ≠ n → ∀ x y ∈ X, same_order (R₁ i) (R₂ i) x y x y) ∧ 
		(∀ i ∈ N, is_extremal (R₁ i) X b) ∧ (∀ i ∈ N, is_extremal (R₂ i) X b) ∧
			(∀ a ∈ X, a ≠ b → P (R₁ n) a b) ∧ (∀ a ∈ X, a ≠ b → P (R₂ n) b a) ∧
				(∀ a ∈ X, a ≠ b → P (f R₁) a b) ∧ (∀ a ∈ X, a ≠ b → P (f R₂) b a)

lemma second_step (hf : is_arrovian f X N) (hX : card X ≥ 3) (hN : card N ≥ 2) :
	∀ b ∈ X, ∃ n' ∈ N, is_pivotal f N X n' b := 
begin
  sorry,
end

def is_dictator_except (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (N : finset ι) (X : finset σ) (n : ι) (b : σ) : Prop := 
∀ a ∈ X, ∀ c ∈ X, a ≠ b → c ≠ b → ∀ Rᵢ : ι → σ → σ → Prop, P (Rᵢ n) c a → P (f Rᵢ) c a

lemma third_step (hf : is_arrovian f X N) (hX : card X ≥ 3) (hN : card N ≥ 2) :
	∀ b ∈ X, ∀ n' ∈ N, is_pivotal f N X n' b → is_dictator_except f N X n' b :=
begin
  sorry,
end


lemma third_distinct_mem (hX : card X ≥ 3)(a_in : a ∈ X) (b_in : b ∈ X) (h : a ≠ b) : 
  ∃ c ∈ X, c ≠ a ∧ c ≠ b :=
begin
	have h₁ := card_erase_of_mem b_in,
	have h₂ := mem_erase_of_ne_of_mem h a_in,
	have h₃ := card_erase_of_mem h₂,
	rw h₁ at h₃,
	have h₄ := nat.pred_le_pred hX,
	simp at h₄,
	have h₅ := nat.pred_le_pred h₄,
	rw ← h₃ at h₅,
	simp at h₅,
	have h₆ : 0 < ((X.erase b).erase a).card := by linarith,
	rw card_pos at h₆,
	cases h₆ with c hc,
	simp only [mem_erase, ne.def] at hc,
	use c,
	rw [← ne.def, ← ne.def] at hc,
	exact ⟨hc.2.2, hc.1, hc.2.1⟩,
end


lemma fourth_step (hf : is_arrovian f X N) (hX : card X ≥ 3) (hN : card N ≥ 2)
	(h : ∀ b ∈ X, ∃ (n' ∈ N), is_pivotal f N X n' b) : 
	is_dictatorship f X N := 
begin
	have X_pos : 0 < finset.card X := by linarith,
	obtain ⟨b, b_in⟩ := (card_pos.1 X_pos).bex,
	obtain ⟨i, i_in, i_piv⟩ := h b b_in,
	have i_dict := third_step hf hX hN b b_in i i_in i_piv,
	rcases i_piv with ⟨R, R', hi₁, hi₂, hi₃, hi₄, hi₅, hi₆, hi₇⟩,
	have : ∀ a ∈ X, a ≠ b → ∀ Rᵢ : (ι → σ → σ → Prop), 
					(P (Rᵢ i) a b → P (f Rᵢ) a b) ∧ (P (Rᵢ i) b a → P (f Rᵢ) b a),
	{ intros a a_in ha Rᵢ,
		obtain ⟨c, c_in, not_a, not_b⟩ : ∃ c ∈ X, c ≠ a ∧ c ≠ b := third_distinct_mem hX a_in b_in ha,
		obtain ⟨j, j_in, j_piv⟩ := h c c_in,
		have j_dict := third_step hf hX hN c c_in j j_in j_piv, 
		have hij : i = j,
		{ by_contradiction hij,
			have jab : P (R j) a b,
			{ by_contradiction bla,
				have foo := or.resolve_left (hi₂ j j_in).2,
				simp only [and_imp, exists_prop, ne, exists_imp_distrib, not_forall] at foo,
				specialize foo a a_in ha bla a a_in ha,
				specialize j_dict a a_in b b_in (ne_comm.1 not_a) (ne_comm.1 not_b) R foo,
				specialize hi₆ a a_in ha,
				apply nP_of_reverseP hi₆,
				exact j_dict }, 
			specialize hi₁ j j_in (ne_comm.1 hij) a b a_in b_in,
			specialize hi₇ a a_in ha,
			specialize j_dict b b_in a a_in (ne_comm.1 not_b) (ne_comm.1 not_a) R' (hi₁.2.1.1 jab),
			apply nP_of_reverseP hi₇,
			exact j_dict },
		split,
		{ rw ← hij at j_dict,
			exact j_dict b b_in a a_in (ne_comm.1 not_b) (ne_comm.1 not_a) Rᵢ },
		{ rw hij,
			exact j_dict a a_in b b_in (ne_comm.1 not_a) (ne_comm.1 not_b) Rᵢ } },
	use i, split, exact i_in,
	intros x y x_in y_in Rᵢ hyp,
	by_cases hx : x = b,
	{ by_cases hy : y = b,
		{ rw [hx,hy] at hyp,
			exfalso,
			exact false_of_P_self hyp },
		{ rw ← hx at *, rw ← ne.def at hy,
			exact (this y y_in hy Rᵢ).2 hyp } },
	{ by_cases hy : y = b,
		{ rw ← ne.def at hx, rw ← hy at *,
			exact (this x x_in hx Rᵢ).1 hyp },
		{ exact i_dict y y_in x x_in hy hx Rᵢ hyp } },
end


lemma arrows_theorem (hf : is_arrovian f X N) (hX : card X ≥ 3) (hN : card N ≥ 2):
  is_dictatorship f X N := 
fourth_step hf hX hN $ second_step hf hX hN