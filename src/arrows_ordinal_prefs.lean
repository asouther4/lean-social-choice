import data.set.finite
import tactic
import basic

open relation vector finset

--we think of social states as type σ and inidividuals as type ι
variables {σ ι : Type} [decidable_eq σ] [decidable_eq ι]

variables {x y x' y' a b : σ} -- social states
          {R R' : σ → σ → Prop} --relations between social states (Andrew did I get this right?)
          {X : finset σ}

----------------------------------------------
--Some Basic Definitions and Lemmas
----------------------------------------------

/- Alternate defintion of `same_order`. Can be interchanged with the original, as 
the lemma below shows. -/
def same_order' (R R' : σ → σ → Prop) (s₁ s₂ s₃ s₄ : σ) : Prop :=
(P R s₂ s₁ ↔ P R' s₄ s₃) ∧ (P R s₁ s₂ ↔ P R' s₃ s₄)

lemma nP_iff_of_P_iff (h₁ : R a b ↔ R' a b) (h₂ : R b a ↔ R' b a) : 
(P R a b ↔ P R' a b) ∧ (P R b a ↔ P R' b a) :=
begin
  simp only [P],
  rw [h₁, h₂],
  simp only [iff_self, and_self],
end


/-- A social state `b` is *bottom* of a finite set of social states `X` with respect to 
  a ranking `p` if `b` is ranked strictly lower than every other `a ∈ X`. -/
def is_bot (b : σ) (R : σ → σ → Prop) (X : finset σ) : Prop :=
∀ a ∈ X, a ≠ b → P R a b

/-- A social state `b` is *top* of a finite set of social states `X` with respect to
  a ranking `p` if `b` is ranked strictly higher than every other `a ∈ X`. -/
def is_top (b : σ) (R : σ → σ → Prop) (X : finset σ) : Prop := 
∀ a ∈ X, a ≠ b → P R b a

/-- A social state `b` is *extremal* with respect to a finite set of social states `X` 
  and a ranking `p` if `b` is either bottom or top of `X`. -/
def is_extremal (b : σ) (p : σ → σ → Prop) (X : finset σ) : Prop := 
is_bot b p X ∨ is_top b p X


lemma is_extremal.is_top (hextr : is_extremal b R X) (not_bot : ¬is_bot b R X) :
  is_top b R X := 
hextr.resolve_left not_bot 


lemma is_extremal.is_bot (hextr : is_extremal b R X) (not_top : ¬is_top b R X) :
  is_bot b R X := 
hextr.resolve_right not_top 


/- Next, we define the notion of a preference ordering. -/
structure pref_order (α : Type*) := 
(rel : α → α → Prop)
(reflexive : reflexive rel)
(total : total rel)
(transitive : transitive rel)

instance (α : Type*) : has_coe_to_fun (pref_order α) := ⟨_, λ R, R.rel⟩

lemma pref_order_eq_coe {α : Type*} (R :pref_order α) : R.rel = R := by refl

variables {f : (ι → pref_order σ) → pref_order σ} -- our "election process" (see above)
          {Rᵢ : ι → pref_order σ} --so I think of this as a function which accepts an individual and outputs a relation R but I'm not sure how to describe it using the proper vocabulary - Ben

def weak_pareto (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop := 
∀ (x y ∈ X) (Rᵢ : ι → pref_order σ), (∀i : ι,  P (Rᵢ i) x y) → P (f Rᵢ) x y

def ind_of_irr_alts (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop :=
∀ (Rᵢ Rᵢ' : ι → pref_order σ) (x y ∈ X), (∀i : ι, same_order' (Rᵢ i) (Rᵢ' i) x y x y) → 
  same_order' (f Rᵢ) (f Rᵢ') x y x y

def is_dictatorship (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop :=
∃ i : ι, ∀ (x y ∈ X) (Rᵢ : ι → pref_order σ), P (Rᵢ i) x y → P (f Rᵢ) x y

def is_pivotal (f : (ι → pref_order σ) → pref_order σ) 
  (X : finset σ) (i : ι) (b : σ) : Prop := 
∃ (P P' : ι → pref_order σ),
  (∀ j : ι, j ≠ i → ∀ x y ∈ X, P j = P' j) ∧ 
    (∀ i : ι, is_extremal b (P i) X) ∧ (∀ i : ι, is_extremal b (P' i) X) ∧
      (is_bot b (P i) X) ∧ (is_top b (P' i) X) ∧ 
        (is_bot b (f P) X) ∧ (is_top b (f P') X)

def has_pivot (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) (b : σ): Prop := 
∃ i, is_pivotal f X i b


/-- An individual is a dictator over all social states in a given set *except* `b` 
  if they are a dictator over every pair of distinct alternatives not equal to `b`.  -/
def is_dictator_except (f : (ι → pref_order σ) → pref_order σ) 
  (X : finset σ) (i : ι) (b : σ) : Prop := 
∀ a c ∈ X, a ≠ b → c ≠ b → ∀ R : ι → pref_order σ, P (R i) c a → P (f R) c a 


/-- Given an arbitary preference order `R` and a social state `b`,
  `maketop R b` updates `R` so that `b` is now ranked strictly higher 
  than any other social state. 
  The definition also contains a proof that this new relation is a `pref_order σ`. --/
def maketop [decidable_eq σ] 
  (R : pref_order σ) (b : σ) : pref_order σ := 
begin
let R' := λ x y,
  if x = b then true else 
    (if y = b then false else R x y),
use R',
{ intro x,
    simp only [R', if_false_left_eq_and, if_true_left_eq_or],
    by_cases hx : x = b,
    { left, exact hx, },
    { right, exact ⟨hx, R.reflexive x⟩, }, },
  { intros x y,
    simp only [R', if_false_left_eq_and, if_true_left_eq_or],
    by_cases hx : x = b,
    { left, left, exact hx, },
    { by_cases hy : y = b,
      { right, left, exact hy, },
      { cases R.total x y with h,
        { left, right, exact ⟨hy, h⟩, },
        { right, right, exact ⟨hx, h⟩, }, }, }, },
  { intros x y z hxy hyz,
    simp only [R', if_false_left_eq_and, if_true_left_eq_or] at *,
    cases hxy,
    { left, exact hxy },
    { cases hyz,
      { exfalso, exact hxy.1 hyz, },
      { right, exact ⟨hyz.1, (R.transitive hxy.2 hyz.2)⟩, } }, },
end  

/-- Given an arbitary preference order `R` and a social state `b`,
  `makebot R b` updates `R` so that every other social state is now ranked 
  strictly higher than `b`. 
  The definition also contains a proof that this new relation is a `pref_order σ`. --/
def makebot [decidable_eq σ] 
  (R : pref_order σ) (b : σ) : pref_order σ := 
begin
  let R' := λ x y,
    if y = b then true 
      else if x = b then false else R x y,
  use R',
  { intro x,
    simp only [R', if_false_left_eq_and, if_true_left_eq_or],
    by_cases hx : x = b,
    { left, exact hx },
    { right, exact ⟨hx, R.reflexive x⟩, }, },
  { intros x y,
    simp only [R', if_false_left_eq_and, if_true_left_eq_or],
    by_cases hx : x = b,
    { right, left, exact hx, },
    { by_cases hy : y = b,
      { left, left, exact hy, },
      { cases R.total x y with h,
        { left, right, exact ⟨hx, h⟩, },
        { right, right, exact ⟨hy, h⟩, }, }, }, },
  { intros x y z hxy hyz,
    simp only [R', if_false_left_eq_and, if_true_left_eq_or] at *,
    cases hyz,
    { left, exact hyz, },
    { cases hxy,
      { exfalso, exact hyz.1 hxy, },
      { right, exact ⟨hxy.1, (R.transitive hxy.2 hyz.2)⟩, }, }, },
end
  
  
open classical
local attribute [instance] prop_decidable

/-- Given an arbitary preference order `R`, two social states `a` & `b`, and 
  a proof `a_neq_b : a ≠ b`, `makebot R a b a_neq_b` updates `R` so that: 
  (1) `b` is strictly higher than `a` and any other social state `y` where `R a y`
  (2) any other social state that is strictly higher than `a` is strictly higher than `b`.
  Intuitively, we have moved `b` *just above* `a` in the ordering. 
  The definition also contains a proof that this new relation is a `pref_order σ`. --/
def makejustabove [decidable_eq σ] 
  (R : pref_order σ) (a b : σ) (a_neq_b : a ≠ b): pref_order σ := 
begin
  let R' := λ x y,
    if x = b then
      (if y = b 
        then true 
    else (if R a y 
        then true
    else 
      false ) ) 
  else
    (if y = b then
      (if R a x then false
    else true)
    else R x y),
  use R',
  { intro x,  
    simp only [R', if_false_left_eq_and, and_true, 
      if_true_left_eq_or, if_false_right_eq_and],
    by_cases hx : x = b,
    { rw [if_pos hx], left, exact hx, },
    { rw [if_neg hx, if_neg hx], exact R.reflexive x, }, },
  { intros x y,
    simp only [R', if_false_left_eq_and, and_true, 
      if_true_left_eq_or, if_false_right_eq_and],
    by_cases hx : x = b,
    { by_cases hy : y = b,
      rw [if_pos hx],
      { left, left, exact hy, },
      { by_cases ha : R a y,
        { left, rw if_pos hx,
          right, exact ha, },
        { right, 
          rw [if_neg hy, if_pos hx],
          exact ha, }, }, },
    { by_cases hy : y = b,
      { by_cases ha : R a x,
        { right, rw if_pos hy,
          right, exact ha, },
        { left, 
          rw [if_neg hx, if_pos hy],
          exact ha, }, },
      { cases R.total x y,
        { left, 
          rw [if_neg hx, if_neg hy],
          exact h, },
        { right,
          rw [if_neg hx, if_neg hy],
          exact h, }, }, }, },
  { intros x y z hxy hyz,
    simp only [R', if_false_left_eq_and, and_true, 
      if_true_left_eq_or, if_false_right_eq_and] at *,
    by_cases hx : x = b,
    { by_cases hz : z = b,
      { rw if_pos hx,
        left, exact hz, },
      { by_cases hy : y = b,
        { rw if_pos hy at hyz,
          rw if_pos hx,
          right, exact hyz.resolve_left hz, },
        { rw if_pos hx at hxy,
          rw if_neg hy at hyz,
          rw if_neg hz at hyz,
          rw if_pos hx,
          right,
          exact R.transitive (hxy.resolve_left hy) hyz, }, }, },
    { by_cases hz : z = b,
      { by_cases hy : y = b,
        { rw [if_neg hx, if_pos hy] at hxy,
          rw [if_neg hx, if_pos hz],
          exact hxy, },
        { rw [if_neg hx, if_pos hz],
          rw [if_neg hx, if_neg hy] at hxy,
          rw [if_neg hy, if_pos hz] at hyz,
          by_contradiction hax,
          exact hyz (R.transitive hax hxy), }, },
      { rw [if_neg hx, if_neg hz],
        by_cases hy : y = b,
        { rw [if_neg hx, if_pos hy] at hxy,
          rw if_pos hy at hyz,
          exact R.transitive ((R.total a x).resolve_left hxy) (hyz.resolve_left hz), },
        { rw [if_neg hx, if_neg hy] at hxy,
          rw [if_neg hy, if_neg hz] at hyz,
          exact R.transitive hxy hyz, }, }, },},
end 

section make

variable [decidable_eq σ]

lemma maketop_noteq (R : pref_order σ) (a b c : σ) (ha : a ≠ b) (hc : c ≠ b) :
  ((maketop R b) a c ↔ R a c) ∧ ((maketop R b) c a ↔ R c a) := 
begin
  split,
  { simp [maketop],
    split,
    { intro h,
      cases h,
      simp at *,
      exfalso,
      exact ha h,
      exact h.2, },
    { intro h,
      right,
      exact ⟨hc, h⟩, }, },
  { split,
    { intro h,
      simp [maketop] at h,
      cases h,
      simp at *,
      exfalso,
      exact hc h,
      exact h.2, },
    { intro h,
      simp [maketop],
      right,
      exact ⟨ha, h⟩, }, },
end

lemma maketop_noteq' (R : pref_order σ) (a b c : σ) (ha : a ≠ b) (hc : c ≠ b) :
  (P (maketop R b) a c ↔ P R a c) ∧ (P (maketop R b) c a ↔ P R c a) :=
begin
  have := maketop_noteq R a b c ha hc,
  exact nP_iff_of_P_iff this.1 this.2,
end

lemma makebot_noteq (R : pref_order σ) (a b c : σ) (ha : a ≠ b) (hc : c ≠ b) :
  ((makebot R b) a c ↔ R a c) ∧ ((makebot R b) c a ↔ R c a) := 
begin
  split,
  { simp [makebot],
    split,
    { intro h,
      cases h,
      simp at *,
      exfalso,
      exact hc h,
      exact h.2, },
    { intro h,
      right,
      exact ⟨ha, h⟩, }, },
  { split,
    { intro h,
      simp [makebot] at h,
      cases h,
      simp at *,
      exfalso,
      exact ha h,
      exact h.2, },
    { intro h,
      simp [makebot],
      right,
      exact ⟨hc, h⟩, }, },
end

lemma makebot_noteq' (R : pref_order σ) (a b c : σ) (ha : a ≠ b) (hc : c ≠ b) :
  (P (makebot R b) a c ↔ P R a c) ∧ (P (makebot R b) c a ↔ P R c a) :=
begin
  have := makebot_noteq R a b c ha hc,
  exact nP_iff_of_P_iff this.1 this.2,
end

lemma makejustabove_noteq (R : pref_order σ) (a b c d: σ) (ha : a ≠ b) (hc : c ≠ b) (hd : d ≠ b):
((makejustabove R a b ha) c d ↔ R c d) ∧ ((makejustabove R a b ha) d c ↔ R d c) :=
by simp only [makejustabove, ← pref_order_eq_coe, if_neg hc, if_neg hd, iff_self, and_self]


lemma makejustabove_noteq' (R : pref_order σ) (a b c d: σ) (ha : a ≠ b) (hc : c ≠ b) (hd : d ≠ b):
(P (makejustabove R a b ha) c d ↔ P R c d) ∧ (P (makejustabove R a b ha) d c ↔ P R d c) :=
by simp only [makejustabove, ← pref_order_eq_coe, if_neg hc, if_neg hd, P, iff_self, and_self]

lemma is_top_of_maketop (b : σ) (R : pref_order σ) (X : finset σ) :
  is_top b (maketop R b) X :=
by simp only [maketop, is_top, P, ←pref_order_eq_coe, true_and, 
  if_false_left_eq_and, imp_self, implies_true_iff, true_or,
    eq_self_iff_true, not_true, or_false, if_true_left_eq_or, false_and]

lemma is_bot_of_makebot (b : σ) (R : pref_order σ) (X : finset σ) :
  is_bot b (makebot R b) X :=
by simp only [is_bot, makebot, P, ←pref_order_eq_coe, true_and, if_false_left_eq_and, 
  imp_self, implies_true_iff, true_or, eq_self_iff_true, not_true, 
    or_false, if_true_left_eq_or, false_and]

/- # TODO: new name -/
lemma lt_makejustabove (a b : σ) (R : pref_order σ) (a_neq_b: a ≠ b):
P (makejustabove R a b a_neq_b) b a :=
begin
  
  simp only [P, makejustabove, ←pref_order_eq_coe, if_false_left_eq_and, 
    and_true, if_true, true_or, eq_self_iff_true,
      if_true_left_eq_or, if_false_right_eq_and],
  push_neg,
  refine ⟨ _, ⟨a_neq_b, R.reflexive a⟩ ⟩,
  right, exact R.reflexive a, 
end

/- # TODO NEW NAME -/
lemma makejustabove_bla {a b c : σ} (R : pref_order σ) 
  (a_neq_b : a ≠ b) (c_neq_b : c ≠ b) (hP : P R c a) :
P (makejustabove R a b a_neq_b) c b :=
begin
  simp only [P, makejustabove, ←pref_order_eq_coe, if_false_left_eq_and, 
    and_true, if_true, true_or, eq_self_iff_true,
      if_true_left_eq_or, if_false_right_eq_and],
  push_neg,
  refine ⟨ _, ⟨c_neq_b, hP.2⟩ ⟩,
    right, exact hP.2,
end

end make

/--- The Proof Begins ---/

lemma first_step { R : ι → pref_order σ }
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (b_in : b ∈ X) (hextr : ∀ i, is_extremal b (R i) X) :
  is_extremal b (f R) X := sorry

/- NOTE: the proof of `first_step` below is now deprecated, and it'll take a good bit of work to fix. 
  But I am keeping it here now for future reference. -- Andrew 
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

-/


lemma second_step_aux [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 2 < X.card) (b_in : b ∈ X) {D' : finset ι} :
  ∀ {R : ι → pref_order σ}, D' = {i ∈ univ | is_bot b (R i) X} → 
    (∀ i, is_extremal b (R i) X) → is_bot b (f R) X → has_pivot f X b := 
begin
  sorry,
end

lemma second_step (hind : ind_of_irr_alts f X) 
  (hX : 3 ≤ X.card) (b) (b_in : b ∈ X) :
has_pivot f X b := 
begin
  sorry,
end


lemma third_step (hind : ind_of_irr_alts f X) 
  (hX : 3 ≤ X.card) (b_in : b ∈ X) {i : ι} (i_piv : is_pivotal f X i b) :
  is_dictator_except f X i b :=
begin
  intros a c a_in c_in a_neq_b c_neq_b Q hyp,
  obtain ⟨R, R', i_piv⟩ := i_piv,
  have X_ne := nonempty_of_ne_empty (ne_empty_of_mem b_in),
  classical,
  let Q' : ι → pref_order σ:= λ j, 
    if j = i 
      then makejustabove (Q j) a b a_neq_b
    else 
      if is_bot b (R j) X
        then makebot (Q j) b
      else maketop (Q j) b,
  have Q'_iff : ∀ j, ∀ d ≠ b, ∀ e ≠ b, 
    (P (Q j) d e ↔ P (Q' j) d e) ∧ (P (Q j) e d ↔ P (Q' j) e d),
  { intros j d d_neq_b e e_neq_b,
    by_cases hj : j = i,
    { simp only [Q', if_pos hj, 
        makejustabove_noteq' (Q j) a b d e a_neq_b d_neq_b e_neq_b, 
          and_self, iff_self], },
    { simp [Q', if_neg hj],
      by_cases hbot : is_bot b (R j) X,
      { simp only [if_pos hbot, makebot_noteq' (Q j) d b e d_neq_b e_neq_b, 
          iff_self, and_self], },
      { simp only [if_neg hbot, maketop_noteq' (Q j) d b e d_neq_b e_neq_b, 
          iff_self, and_self], }, }, },
  have hQ'bc : ∀ j, (P (R j) c b ↔ P (Q' j) c b) ∧ (P (R j) b c ↔ P (Q' j) b c),
  { refine (λ j, ⟨⟨λ hP, _, λ hQ', _⟩, ⟨λ hP, _, λ hQ', _⟩⟩ ); by_cases hj : j = i,
    { simp [Q', if_pos hj],
      rw ← hj at hyp,
      exact makejustabove_bla (Q j) a_neq_b c_neq_b hyp, },  
    { simp [Q', if_neg hj],
      have b_bot : is_bot b (R j) X,
      { unfold is_bot,
        by_contradiction b_bot, push_neg at b_bot,
        rcases b_bot with ⟨d, d_in, d_neq_b, hd⟩,
        cases i_piv.2.1 j,
        { exact hd (h d d_in d_neq_b), },
        { exact hP.2 (h c c_in c_neq_b).1, }, },
      rw if_pos b_bot,
      exact (is_bot_of_makebot b (Q j) X) c c_in c_neq_b, },
    { convert i_piv.2.2.2.1 c c_in c_neq_b, }, 
    { by_contradiction hP,
      have not_bot : ¬ is_bot b (R j) X := by simp only 
        [is_bot, exists_prop, ne.def, not_forall];
          exact ⟨c, c_in, c_neq_b, hP⟩,
      apply nP_of_reverseP ((is_top_of_maketop b (Q j) X) c c_in c_neq_b),
      convert hQ',
      simp [Q', if_neg, not_bot, hj], }, 
    { exfalso,
      rw hj at hP,
      exact hP.2 (i_piv.2.2.2.1 c c_in c_neq_b).1, },
    { simp [Q', if_neg hj],
      have not_bot : ¬ is_bot b (R j) X,
      { by_contradiction b_bot,
        specialize b_bot c c_in c_neq_b,
        exact hP.2 b_bot.1, },
      rw if_neg not_bot,
      exact is_top_of_maketop b (Q j) X c c_in c_neq_b, },
    { exfalso,
      simp only at hQ',
      simp [Q', if_pos hj] at hQ',
      rw hj at hQ',
      exact hQ'.2 (makejustabove_bla (Q i) a_neq_b c_neq_b hyp).1, },
    { by_contradiction hR,
      have b_bot : is_bot b (R j) X,
      { refine is_extremal.is_bot (i_piv.2.1 j) _,
        simp only [is_top, exists_prop, ne.def, not_forall],
        exact ⟨c, c_in, c_neq_b, hR⟩, },
      simp only at hQ',
      simp only [Q', if_neg hj, if_pos b_bot] at hQ',
      exact hQ'.2 (is_bot_of_makebot b (Q j) X c c_in c_neq_b).1, }, }, 
  have hQ'ab : ∀ j, (P (R' j) b a ↔ P (Q' j) b a) ∧ (P (R' j) a b ↔ P (Q' j) a b),
  { refine (λ j, ⟨⟨λ hP', _, λ hQ', _⟩, ⟨λ hP', _, λ hQ', _⟩ ⟩); by_cases hj : j = i,
    { simp [Q'],
      rw if_pos hj,
      rw ← hj at hyp,
      have := lt_makejustabove a b (Q j),
      exact (this a_neq_b), },
    { simp [Q'],
      have not_bot : ¬ is_bot b (R j) X,
      { rw (i_piv.1 j hj a b a_in b_in),
        simp only [is_bot, exists_prop, ne.def, not_forall],
        exact ⟨a, a_in, a_neq_b,  nP_of_reverseP hP'⟩, },
      rw [if_neg hj, if_neg not_bot],
      exact (is_top_of_maketop b (Q j) X) a a_in a_neq_b, },
    { convert i_piv.2.2.2.2.1 a a_in a_neq_b, },
    { simp only at hQ', 
      simp only [Q', dite_eq_ite, if_neg hj] at hQ',
      have not_bot : ¬ (is_bot b (R j) X),
      { by_contradiction b_bot, 
        rw if_pos b_bot at hQ',
        apply (nP_of_reverseP hQ'),
        exact (is_bot_of_makebot b (Q j) X) a a_in a_neq_b, },
      rw if_neg not_bot at hQ',
      rw ← (i_piv.1 j hj a b a_in b_in),
      have b_top : is_top b (R j) X := 
        is_extremal.is_top (i_piv.2.1 j) not_bot,
      exact b_top a a_in a_neq_b, },
      { exfalso,
        rw hj at hP',
        exact hP'.2 (i_piv.2.2.2.2.1 a a_in a_neq_b).1, },
      { simp [Q'],
        have b_bot : is_bot b (R j) X,
        { rw (i_piv.1 j hj a b a_in b_in),
          refine is_extremal.is_bot (i_piv.2.2.1 j) _,
          simp only [is_top, exists_prop, ne.def, not_forall],
          exact ⟨a, a_in, a_neq_b, nP_of_reverseP hP'⟩, }, 
        rw [if_neg hj, if_pos b_bot],
        exact is_bot_of_makebot b (Q j) X a a_in a_neq_b, },
      { exfalso,
        simp only at hQ',
        simp only [Q', dite_eq_ite, if_pos hj] at hQ',
        exact hQ'.2 (lt_makejustabove a b (Q j) a_neq_b).1, },
      { simp only at hQ', 
        simp only [Q', dite_eq_ite, if_neg hj] at hQ',
        have b_bot : (is_bot b (R j) X),
        { by_contradiction b_bot, 
          rw if_neg b_bot at hQ',
          exact hQ'.2 (is_top_of_maketop b (Q j) X a a_in a_neq_b).1,},
        rw ← (i_piv.1 j hj a b a_in b_in),
        exact b_bot a a_in a_neq_b, },},
  have hQQ' : ∀ j, (P (Q j) c a ↔ P (Q' j) c a) ∧ (P (Q j) a c ↔ P (Q' j) a c),
  { intro j,
    exact Q'_iff j c c_neq_b a a_neq_b, }, 
  simp only [ind_of_irr_alts, same_order] at hind,
  rw (hind Q Q' a c a_in c_in hQQ').1, 
  have h₁ : P (f Q') b a,
  { apply (hind R' Q' a b a_in b_in hQ'ab).1.1,
    exact i_piv.2.2.2.2.2.2 a a_in a_neq_b, },
  have h₂ : P (f Q') c b,
  { apply (hind R Q' b c b_in c_in hQ'bc).1.1,
    exact i_piv.2.2.2.2.2.1 c c_in c_neq_b },
  exact P_trans (f Q').transitive h₂ h₁,
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

/- NOTE: this proof is deprecated for now, but it should be easy to fix.-- Andrew -/
lemma fourth_step (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) 
  (hX : 3 ≤ X.card) (h : ∀ b ∈ X, has_pivot f X b) : 
is_dictatorship f X := 
begin
  sorry,
end
/--
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
--/

/-- Arrow's Impossibility Theorem: Any social welfare function involving at least three social
  states that satisfies WP and IoIA is necessarily a dictatorship. -/
theorem arrow [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) :
  is_dictatorship f X := fourth_step hwp hind hX $ second_step hind hX
