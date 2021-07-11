import data.set.finite
import tactic

open relation vector finset

/- # Andrew says: 
IGNORE first_step and IGNORE the `unrestriced_domain` definition -/

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
def P (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ ¬ R y x -- accepts a relation and two social states

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



/- a social state is extremal with respect to a relation and a set of individuals
if every individual ranks that social state either highest or lowest -/
def is_extremal (R  : σ → σ → Prop) (X : finset σ) (s : σ) : Prop := 
s ∈ X ∧ ((∀ t ∈ X, t ≠ s → P R t s) ∨ (∀ t ∈ X, t ≠ s → P R s t))


----------------------------
--The important part!!!!!!
-----------------------------


/- We think of a preference as a relation of type σ → σ → Prop. 
We think of an individual preference as a mapping from each individual of type ι to a preference.
A choice function is a mapping from an individual preference to a preference. 

That is, a choice function has this type: 
(ι → σ → σ → Prop) → (σ → σ → Prop)
-/
variables {f : (ι → σ → σ → Prop) → (σ → σ → Prop)} -- our "election process" (see above)
          {Rᵢ : ι → (σ → σ → Prop)} --so I think of this as a function which accepts an individual and outputs a relation R but I'm not sure how to describe it using the proper vocabulary - Ben
          {X : finset σ} --a finite set of social states
          {N : finset ι} --a finite set of individuals

---TODO: not sure if I've defined this one right - Andrew
def unrestricted_domain (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) : Prop := 
(∀ (m : ℕ) (n : fin (m+1)) (V : vector (finset ι) n) (T : vector (vector σ m) n),
  ∃ Rᵢ : ι → (σ → σ → Prop), ∀ (i : ι) (j : fin n) (k k': fin m), i ∈ nth V j → k > k' →
    P (Rᵢ i) (nth (nth T j) k) (nth (nth T j) k'))

def weak_pareto (f : (ι → σ → σ → Prop) → σ → σ → Prop) (X : finset σ) (N : finset ι) : Prop := 
∀ (x y ∈ X) (Rᵢ : ι → (σ → σ → Prop)), (∀ i ∈ N, P (Rᵢ i) x y) → P (f Rᵢ) x y

def ind_of_irr_alts (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (X : finset σ) (N : finset ι) : Prop :=
∀ (Rᵢ Rᵢ' : ι → (σ → σ → Prop)) (x y ∈ X), (∀ i ∈ N, same_order (Rᵢ i) (Rᵢ' i) x y x y) → 
  same_order (f Rᵢ) (f Rᵢ') x y x y

def is_arrovian (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (X : finset σ) (N : finset ι) : Prop :=
unrestricted_domain f ∧ weak_pareto f X N ∧ ind_of_irr_alts f X N ∧ ∀ (Rᵢ : (ι → σ → σ → Prop)), is_pref_ordering (f Rᵢ)

def is_dictatorship (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (X : finset σ) (N : finset ι) : Prop :=
∃ i ∈ N, ∀ (x y ∈ X) (Rᵢ : ι → (σ → σ → Prop)), P (Rᵢ i) x y → P (f Rᵢ) x y


def maketop [decidable_eq σ] (p : σ → σ → Prop) (b : σ) : σ → σ → Prop := 
λ x y, if x = b then true else p x y

def makebot [decidable_eq σ] (p : σ → σ → Prop) (b : σ) : σ → σ → Prop := 
λ x y, if y = b then true else p x y

/-- NOTE: I think this only makes sense if `p a c` is true (`a` is ranked higher than `c` in `p`). -Ben -/
def makebetween [decidable_eq σ] (p : σ → σ → Prop) (a b c : σ) : σ → σ → Prop := 
λ x y, if x = a ∨ y = c then true else p x y


/- Some tests/exercises: -/

lemma test1 [decidable_eq σ] (p : σ → σ → Prop) (b a : σ) : 
  maketop p b b a :=
by simp only [maketop, true_or, eq_self_iff_true, if_true_left_eq_or]

-- I don't think we have enough infrastructure yet to show this one
lemma test2 [decidable_eq σ] (p : σ → σ → Prop) (hp : is_pref_ordering p) (b a : σ) (hne : a ≠ b) : 
  ¬ maketop p b a b :=
begin
  -- have hmp : is_pref_ordering (maketop p b), sorry,
  -- have := test1 p b a,
  -- have := nP_of_reverseP _ hmp this,
  -- intro h,
  -- simp only [maketop, hne, false_or, eq_self_iff_true, if_true_left_eq_or] at this h,
  sorry,
end




--First step of Arrow's theorem!
--If every individual in society places a social state at the top or bottom of their social preferences,
--then society must place that social state at the top or bottom of its social preference. 
-------------------------------------------
lemma first_step (hf : is_arrovian f X N) (hX : 3 ≤ card X) (b : σ) (b_in : b ∈ X) (R : (ι → σ → σ → Prop))
  (hyp : ∀ i ∈ N, is_extremal (R i) X b) :
  is_extremal (f R) X b :=
begin
  by_contradiction hnot,
  unfold is_extremal at hnot,
  push_neg at hnot,
  rcases ⟨hnot b_in⟩ with ⟨⟨c, c_in, c_ne, hc⟩, ⟨a, a_in, a_ne, ha⟩⟩,
  replace ha : (f R) a b := R_of_nP_total (hf.2.2.2 R).2.1 ha,
  replace hc : (f R) b c := R_of_nP_total (hf.2.2.2 R).2.1 hc,
  have hR₂ : ∃ (R₂ : ι → σ → σ → Prop), ∀ i ∈ N, 
              P (R₂ i) c a ∧ same_order (R i) (R₂ i) b a b a ∧ same_order (R i) (R₂ i) b c b c,
  { let I₁ := {i ∈ N | P (R i) c b ∧ P (R i) a b},
    let I₂ := {i ∈ N | P (R i) b c ∧ P (R i) b a},
    let I := [I₁, I₂],
    have I_length : I.length = 2 := eq.refl I.length,
    let T₁ := [b, a, c], let T₂ := [a, c, b],
    have T₁_length : T₁.length = 3 := eq.refl T₁.length, have T₂_length : T₂.length = 3 := eq.refl T₂.length,
    let T₁_vec : vector σ 3 := ⟨T₁, T₁_length⟩, let T₂_vec : vector σ 3 := ⟨T₂, T₂_length⟩,
    let T := [T₁_vec, T₂_vec],
    have T_length : T.length = 2 := eq.refl T.length,
    obtain ⟨R₂, hR₂⟩ := hf.1 3 2 ⟨I, I_length⟩ ⟨T, T_length⟩,
    use R₂,
    intros i i_in,
    by_cases h : ∀ t ∈ X, t ≠ b → P (R i) b t, 
    { --have i_and : P (R i) b c ∧ P (R i) b a := ⟨h c c_in c_ne, h a a_in a_ne⟩,
      obtain ⟨h1, h2⟩ := ⟨h a a_in a_ne, h c c_in c_ne⟩,
      have i_in' : i ∈ I₂ := by simp [I₂, i_in, h1, h2],
      --have hI₂ : I₂ = nth ⟨I, I_length⟩ 1 := rfl,
      --rw hI₂ at i_in',
      --have R₂a : (nth ⟨T, T_length⟩ 1).nth 0 = a := rfl,
      --have R₂b : (nth ⟨T, T_length⟩ 1).nth 2 = b := rfl,
      --have R₂c : (nth ⟨T, T_length⟩ 1).nth 1 = c := rfl,
      have R₂ba := hR₂ i (1 : fin 2) 2 0 i_in' dec_trivial,
      have R₂bc := hR₂ i (1 : fin 2) 2 1 i_in' dec_trivial,
      have R₂ca := hR₂ i (1 : fin 2) 1 0 i_in' dec_trivial,
      exact ⟨R₂ca, same_order_of_P_P' h1 R₂ba, same_order_of_P_P' h2 R₂bc⟩ },
    { specialize hyp i i_in, 
      rw [is_extremal, or_iff_not_imp_right] at hyp,
      replace h := hyp.2 h,
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
  ∃ v : vector α n, ∀ a ∈ S, ∃ k : fin n, nth v k = a :=
begin
  rcases S with ⟨⟨l⟩, hl : l.nodup⟩,
  change l.length = n at h,
  refine ⟨⟨l, h⟩, λ a ha, _⟩,
  rcases list.nth_le_of_mem ha with ⟨k, hk, e⟩,
  exact ⟨⟨k, by rwa ← h⟩, e⟩,
end

def is_pivotal (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (N : finset ι) (X : finset σ) (n : ι) (b : σ) : Prop := 
∃ (R₁ R₂ : ι → σ → σ → Prop),
  (∀ i ∈ N, i ≠ n → ∀ x y ∈ X, same_order (R₁ i) (R₂ i) x y x y) ∧ 
    (∀ i ∈ N, is_extremal (R₁ i) X b) ∧ (∀ i ∈ N, is_extremal (R₂ i) X b) ∧
      (∀ a ∈ X, a ≠ b → P (R₁ n) a b) ∧ (∀ a ∈ X, a ≠ b → P (R₂ n) b a) ∧
        (∀ a ∈ X, a ≠ b → P (f R₁) a b) ∧ (∀ a ∈ X, a ≠ b → P (f R₂) b a)

lemma second_step (hf : is_arrovian f X N) (hX : 3 ≤ card X) (hN : 2 ≤ card N) :
  ∀ b ∈ X, ∃ n' ∈ N, is_pivotal f N X n' b := 
begin
  sorry,
end

def is_dictator_except (f : (ι → σ → σ → Prop) → (σ → σ → Prop)) (N : finset ι) (X : finset σ) (n : ι) (b : σ) : Prop := 
∀ a ∈ X, ∀ c ∈ X, a ≠ b → c ≠ b → ∀ Rᵢ : ι → σ → σ → Prop, P (Rᵢ n) c a → P (f Rᵢ) c a

lemma third_step (hf : is_arrovian f X N) (hX : 3 ≤ card X) (hN : 2 ≤ card N) :
  ∀ b ∈ X, ∀ n' ∈ N, is_pivotal f N X n' b → is_dictator_except f N X n' b :=
begin
  sorry,
end


lemma third_distinct_mem (hX : 3 ≤ card X) (a_in : a ∈ X) (b_in : b ∈ X) (h : a ≠ b) : 
  ∃ c ∈ X, c ≠ a ∧ c ≠ b :=
begin
  have hpos : 0 < ((X.erase b).erase a).card,
  { simpa only [card_erase_of_mem, mem_erase_of_ne_of_mem h a_in, b_in, nat.pred_succ] 
      using nat.pred_le_pred (nat.pred_le_pred hX) }, 
  cases card_pos.mp hpos with c hc,
  simp_rw mem_erase at hc,
  exact ⟨c, hc.2.2, hc.1, hc.2.1⟩,
end


lemma fourth_step (hf : is_arrovian f X N) (hX : 3 ≤ card X) (hN : 2 ≤ card N)
  (h : ∀ b ∈ X, ∃ (n' ∈ N), is_pivotal f N X n' b) : 
  is_dictatorship f X N := 
begin
  have X_pos : 0 < card X := by linarith,
  obtain ⟨b, b_in⟩ := (card_pos.1 X_pos).bex,
  obtain ⟨i, i_in, i_piv⟩ := h b b_in,
  have : ∀ a ∈ X, a ≠ b → ∀ Rᵢ : ι → σ → σ → Prop, 
          (P (Rᵢ i) a b → P (f Rᵢ) a b) ∧ (P (Rᵢ i) b a → P (f Rᵢ) b a),
  { intros a a_in ha Rᵢ,
    obtain ⟨c, c_in, not_a, not_b⟩ := third_distinct_mem hX a_in b_in ha,
    obtain ⟨j, j_in, j_piv⟩ := h c c_in,
    have j_dict := third_step hf hX hN c c_in j j_in j_piv, 
    have hij : i = j,
    { by_contra hij,
      rcases i_piv with ⟨R, R', hi₁, hi₂, hi₃, hi₄, hi₅, hi₆, hi₇⟩,
      refine nP_of_reverseP (hi₇ a a_in ha) 
        (j_dict b b_in a a_in (ne_comm.1 not_b) (ne_comm.1 not_a) R' 
          ((hi₁ j j_in (ne_comm.1 hij) a b a_in b_in).2.1.1 _)),
      by_contra bla,
      have foo := (hi₂ j j_in).2.resolve_left,
      simp only [and_imp, exists_prop, ne, exists_imp_distrib, not_forall] at foo,
      exact nP_of_reverseP (hi₆ a a_in ha) (j_dict a a_in b b_in (ne_comm.1 not_a) 
        (ne_comm.1 not_b) R (foo a a_in ha bla a a_in ha)) }, 
    rw hij,
    split; refine j_dict _ _ _ _ (ne_comm.1 _) (ne_comm.1 _) Rᵢ; assumption },
  refine ⟨i, i_in, λ x y x_in y_in Rᵢ hyp, _⟩,
  rcases @eq_or_ne _ b x with (rfl | hx); rcases @eq_or_ne _ b y with (rfl | hy), -- @s will drop when we merge master
  { exact (false_of_P_self hyp).elim },
  { exact (this y y_in hy.symm Rᵢ).2 hyp },
  { exact (this x x_in hx.symm Rᵢ).1 hyp },
  { exact third_step hf hX hN b b_in i i_in i_piv y y_in x x_in hy.symm hx.symm Rᵢ hyp },
end


lemma arrows_theorem (hf : is_arrovian f X N) (hX : 3 ≤ card X) (hN : 2 ≤ card N):
  is_dictatorship f X N := 
fourth_step hf hX hN $ second_step hf hX hN