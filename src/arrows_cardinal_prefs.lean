import data.real.basic
import data.set.basic

open finset

-- We think of social states as type `σ` and inidividuals as type `ι`
variables {σ ι : Type*}

/-! 
## Notes

* "All individuals rank" refers to the rankings of each and every individual. 
* "Society ranks" refers to output of a social welfare function 
  (e.g. the final result of an election process).
* <Andrew: Can you please write something describing what a social welfare function is? Thanks!>

## Important Definitions
-/

/-- A social welfare function satisfies the Weak Pareto criterion if, for any two
  social states `x` and `y`, every individual ranking `y` higher than `x` implies
  that society ranks `y` higher than `x`. -/
def weak_pareto (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) : Prop := 
∀ (x y ∈ X) (P : ι → σ → ℝ), (∀ i : ι, P i x < P i y) → (f P) x < (f P) y

/-- Suppose that every individual's ranking of `X` and `Y` remains unchanged between two rankings `P` 
  and `P'`. We say that a social welfare function is *independent of irrelevant alternatives* if 
  society's ranking of `X` and `Y` also remains unchanged between `P` and `P'`. -/
def ind_of_irr_alts (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) : Prop := 
∀ (x y ∈ X) (P P' : ι → σ → ℝ), 
  (∀ i : ι, P i x < P i y ↔ P' i x < P' i y) → (f P x < f P y ↔ f P' x < f P' y)

/-- A social welfare function is a *dicatorship* if a single individual `i` 
  possesses the power to determine society's ordering of any two social states. -/
def is_dictatorship (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) : Prop :=
∃ i : ι, ∀ (x y ∈ X) (P : ι → σ → ℝ), P i x < P i y → f P x < f P y

/-- A social state `b` is *at the bottom of* a finite set of social states `X` with 
  respect to a ranking `p` if `b` is ranked strictly lower than every other `a ∈ X`. -/
def is_bot_of (b : σ) (p : σ → ℝ) (X : finset σ) : Prop :=
∀ a ∈ X, a ≠ b → p b < p a

/-- A social state `b` is *at the top of* a finite set of social states `X` with 
  respect to a ranking `p` if `b` is ranked strictly higher than every other `a ∈ X`. -/
def is_top_of (b : σ) (p : σ → ℝ) (X : finset σ) : Prop := 
∀ a ∈ X, a ≠ b → p a < p b

/-- A social state `b` is *extremal* with respect to a finite set of social states `X` 
  and a ranking `p` if `b` is either at the bottom or the top of `X`. -/
def is_extremal (b : σ) (p : σ → ℝ) (X : finset σ) : Prop := 
is_bot_of b p X ∨ is_top_of b p X

/-- Social sates `x`, `y`, `x'`, and `y'` are in the *same order* with respect to two rankings 
  `p` and `p'` if `x` and `y` have the same ordering in `p` as `x'` and `y'` have in `p'`. -/
def same_order (p p' : σ → ℝ) (x y x' y' : σ) : Prop :=
(p x < p y ↔ p' x' < p' y') ∧ (p y < p x ↔ p' y' < p' x')

/-- An individual `i` is *pivotal* with respect to a social state `b` if 
  there exist rankings `P` and `P'` such that: 
  ⋆ all individuals except for `i` rank all social states in the same order in both rankings
  ⋆ all individuals place `b` in an extremal position in both rankings
  ⋆ `i` ranks `b` at the bottom of their rankings in `P`, but the top of their rankings in `P'`
  ⋆ society ranks `b` at the bottom of its rankings in `P`, but the top of its rankings in `P'` -/
def is_pivotal (f : (ι → σ → ℝ) → (σ → ℝ)) (X : finset σ) (i : ι) (b : σ) : Prop := 
∃ (P P' : ι → σ → ℝ),
  (∀ j : ι, j ≠ i → ∀ x y ∈ X, same_order (P j) (P' j) x y x y) ∧ 
    (∀ i : ι, is_extremal b (P i) X) ∧ (∀ i : ι, is_extremal b (P' i) X) ∧
      (is_bot_of b (P i) X) ∧ (is_top_of b (P' i) X) ∧ 
        (is_bot_of b (f P) X) ∧ (is_top_of b (f P') X)

/-- An individual is a dictator with respect to all social states in a given set *except* for `b` 
  if they are a dictator over every pair of distinct alternatives not equal to `b`.  -/
def is_dictator_except (f : (ι → σ → ℝ) → (σ → ℝ)) (X : finset σ) (i : ι) (b : σ) : Prop := 
∀ a ∈ X, ∀ c ∈ X, a ≠ b → c ≠ b → ∀ P : ι → σ → ℝ, P i a < P i c → f P a < f P c

open function

/-- Given an arbitary ranking `p`, social state `b`, and finite set of social states `X`,
  `maketop b p X` updates `p` so that `b` is now ranked at the top of `X`. -/
noncomputable def maketop [decidable_eq σ] 
  (p : σ → ℝ) (b : σ) (X : finset σ) (h : X.nonempty) : σ → ℝ :=
update p b $ ((X.image p).max' (h.image p)) + 1

/-- Given an arbitary ranking `p`, social state `b`, and finite set of social states `X`,
  `makebot b p X` updates `p` so that `b` is now ranked at the bottom of `X`. -/
noncomputable def makebot [decidable_eq σ]
  (p : σ → ℝ) (b : σ) (X : finset σ) (h : X.nonempty) : σ → ℝ :=
update p b $ ((X.image p).min' (h.image p)) - 1

/-- Given an arbitary ranking `p` and social states `a`, `b`, and `c`, 
  `makebetween p a b c` updates `p` so that `b` is now ranked between `a` and `c`. -/
noncomputable def makebetween [decidable_eq σ] 
  (p : σ → ℝ) (a b c : σ) : σ → ℝ :=
update p b $ (p a + p c) / 2


-- ## Preliminary Lemmas

variables {a b c d : σ} {p : σ → ℝ} {P : ι → σ → ℝ} {f : (ι → σ → ℝ) → σ → ℝ} {X : finset σ}

lemma not_bot_of_top (h_top : is_top_of b p X) (h : ∃ a ∈ X, a ≠ b) : ¬ is_bot_of b p X :=
begin
  simp only [is_bot_of, not_forall, not_lt, exists_prop],
  rcases h with ⟨a, a_in, hab⟩,
  exact ⟨a, a_in, hab, (h_top a a_in hab).le⟩,
end

lemma not_top_of_bot (h_bot : is_bot_of b p X) (h : ∃ a ∈ X, a ≠ b) : ¬ is_top_of b p X :=
begin
  simp only [is_top_of, not_forall, not_lt, exists_prop],
  rcases h with ⟨a, a_in, hab⟩,
  exact ⟨a, a_in, hab, (h_bot a a_in hab).le⟩,
end

lemma top_of_not_bot_of_extr (hextr : is_extremal b p X) (not_bot : ¬ is_bot_of b p X) :
  is_top_of b p X := 
hextr.resolve_left not_bot 

lemma bot_of_not_top_of_extr (hextr : is_extremal b p X) (not_top : ¬ is_top_of b p X) :
  is_bot_of b p X := 
hextr.resolve_right not_top 

lemma extremal_of_bot_of (h_bot : is_bot_of b p X) : is_extremal b p X := 
or.inl h_bot

lemma extremal_of_top_of (h_bot : is_top_of b p X) : is_extremal b p X := 
or.inr h_bot

lemma social_top_of_all_top (b_in : b ∈ X) (hf : weak_pareto f X) 
  (hP : ∀ i : ι, is_top_of b (P i) X) : 
  is_top_of b (f P) X := 
λ a a_in hab, hf a b a_in b_in P $ λ i, hP i a a_in hab

lemma social_bot_of_all_bot (b_in : b ∈ X) (hf : weak_pareto f X) 
  (hP : ∀ i : ι, is_bot_of b (P i) X) : 
  is_bot_of b (f P) X := 
λ a a_in hab, hf b a b_in a_in P $ λ i, hP i a a_in hab

section make

variable [decidable_eq σ]

lemma maketop_noteq (p) (hab : a ≠ b) (hX : X.nonempty) :
  maketop p b X hX a = p a := 
update_noteq hab _ p

lemma makebot_noteq (p) (hab : a ≠ b) (hX : X.nonempty) :
  makebot p b X hX a = p a := 
update_noteq hab _ p

lemma makebetween_noteq (p) (hdb : d ≠ b) :
  makebetween p a b c d = p d :=
update_noteq hdb ((p a + p c) / 2) p

lemma makebetween_eq (a b c : σ) (p) :
  makebetween p a b c b = (p a + p c) / 2 :=
update_same _ _ _

--should rename to `maketop_lt_maketop`
lemma lt_of_maketop (p) (hab : a ≠ b) (hX : X.nonempty) (a_in : a ∈ X) : 
  maketop p b X hX a < maketop p b X hX b :=
by simpa [maketop, hab] using 
  ((X.image p).le_max' _ (mem_image_of_mem p a_in)).trans_lt (lt_add_one _)

--should rename to `makebot_lt_makebot`
lemma lt_of_makebot (p) (hcb : c ≠ b) (hX : X.nonempty) (c_in : c ∈ X) : 
  makebot p b X hX b < makebot p b X hX c :=
by simpa [makebot, hcb] using sub_lt_iff_lt_add'.mpr 
  (((X.image p).min'_le (p c) (mem_image_of_mem p c_in)).trans_lt (lt_one_add _))

--should rename to `makebetween_lt_makebetween_top`
lemma lt_top_of_makebetween (hcb : c ≠ b) (hp : p a < p c) : 
  makebetween p a b c b < makebetween p a b c c :=
begin
  simp only [makebetween, update_same, update_noteq hcb],
  linarith,
end

--should rename to `makebetween_lt_makebetween_bot`
lemma bot_lt_of_makebetween (hab : a ≠ b) (hp : p a < p c) : 
  makebetween p a b c a < makebetween p a b c b :=
begin
  simp only [makebetween, update_same, update_noteq hab],
  linarith,
end

lemma top_of_maketop (b p) (hX : X.nonempty) :
  is_top_of b (maketop p b X hX) X := 
λ a a_in hab, lt_of_maketop p hab hX a_in

end make

lemma second_distinct_mem (hX : 3 ≤ X.card) (a_in : a ∈ X) : 
  ∃ b ∈ X, b ≠ a :=
begin
  classical,
  have hpos : 0 < (X.erase a).card,
  { rw card_erase_of_mem a_in,
    exact zero_le_one.trans_lt (nat.pred_le_pred hX) },
  cases card_pos.mp hpos with b hb,
  cases mem_erase.mp hb with hne H,
  exact ⟨b, H, hne⟩,
end

lemma third_distinct_mem (hX : 3 ≤ X.card) (a_in : a ∈ X) (b_in : b ∈ X) (h : a ≠ b) : 
  ∃ c ∈ X, c ≠ a ∧ c ≠ b :=
begin
  classical,
  have hpos : 0 < ((X.erase b).erase a).card,
  { simpa only [card_erase_of_mem, mem_erase_of_ne_of_mem h a_in, b_in]
      using nat.pred_le_pred (nat.pred_le_pred hX) }, 
  cases card_pos.mp hpos with c hc,
  simp_rw mem_erase at hc,
  exact ⟨c, hc.2.2, hc.1, hc.2.1⟩,
end

-- ## The Proof

lemma first_step (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (b_in : b ∈ X) (hextr : ∀ i, is_extremal b (P i) X) :
  is_extremal b (f P) X := 
begin
  by_contradiction hnot,
  dsimp only [is_extremal, is_bot_of, is_top_of] at hnot,
  push_neg at hnot,
  have h : ∃ t u : σ, t ∈ X ∧ u ∈ X ∧ t ≠ b ∧ u ≠ b ∧ t ≠ u ∧ f P b ≤ f P t ∧ f P u ≤ f P b, -- I changed the variables becuase I found them confusing -Ben
  { obtain ⟨⟨c, c_in, hcb, hc⟩, ⟨a, a_in, hab, ha⟩⟩ := hnot,
    by_cases hac : a = c,
    { obtain ⟨d, d_in, hda, hdb⟩ := third_distinct_mem hX a_in b_in hab,
      by_cases hd : f P b < f P d,
      { exact ⟨d, c, d_in, c_in, hdb, hcb, ne_of_ne_of_eq hda hac, hd.le, hc⟩, },
      { exact ⟨a, d, a_in, d_in, hab, hdb, hda.symm, ha, not_lt.mp hd⟩, }, },
    { exact ⟨a, c, a_in, c_in, hab, hcb, hac, ha, hc⟩, }, },
  classical,
  obtain ⟨a, c, a_in, c_in, hab, hcb, hac, ha, hc⟩ := h,
  let P₂ := λ j, if is_top_of b (P j) X then makebetween (P j) a c b else update (P j) c (P j a + 1),
  have hP₂ac : ∀ i, P₂ i a < P₂ i c,
  { intros i,
    by_cases h : is_top_of b (P i) X,
    { simp [P₂, if_pos h, bot_lt_of_makebetween hac (h a a_in hab)] },
    { simp [P₂, if_neg h, hac] }, },
  have hPab : ∀ i, P i a < P i b ↔ P₂ i a < P₂ i b,
  { simp only [P₂],
    refine λ i, ⟨λ hP, _, λ hP₂, _⟩, 
    { by_cases h : is_top_of b (P i) X; simpa [h, makebetween_noteq, hac, hcb.symm] },
    { by_contra hP,
      have h : ¬ is_top_of b (P i) X := λ b_top, hP (b_top a a_in hab),
      simp only at hP₂, simp [if_neg h, hac, hcb.symm] at hP₂,
      exact hP hP₂ }, },
  have hPbc : ∀ i, P i b < P i c ↔ P₂ i b < P₂ i c, 
  { simp only [P₂],
    refine λ i, ⟨λ hP, _, λ hP₂, _⟩,
    { have h : ¬ is_top_of b (P i) X := λ b_top, asymm hP (b_top c c_in hcb),
      convert lt_add_of_lt_of_pos (bot_of_not_top_of_extr (hextr i) h a a_in hab) _; 
        simp [h, hcb.symm] },
    { by_contradiction hP,
      have h : is_top_of b (P i) X := top_of_not_bot_of_extr (hextr i) (λ h, hP (h c c_in hcb)),
      simp only at hP₂, simp only [if_pos h, makebetween_noteq _ hcb.symm, makebetween_eq] at hP₂,
      linarith [h a a_in hab], }, },
  have h_iir₁ := (not_congr (hind a b a_in b_in P P₂ hPab)).mp (not_lt.mpr ha),
  have h_iir₂ := (not_congr (hind b c b_in c_in P P₂ hPbc)).mp (not_lt.mpr hc),
  have h_pareto := hwp a c a_in c_in P₂ hP₂ac,
  linarith,
end    

-- let `D := {i ∈ univ | is_bot_of b (P i) X}`
-- let `P' := λ j, if j = i then maketop (P j) b X X_ne else P j`
lemma second_step_aux [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (b_in : b ∈ X) :
  ∀ {D : finset ι} {P : ι → σ → ℝ}, D = {i ∈ univ | is_bot_of b (P i) X} → 
    (∀ i, is_extremal b (P i) X) → is_bot_of b (f P) X → ∃ n', is_pivotal f X n' b := 
begin
  classical,
  refine λ D', finset.induction_on D'
    (λ P h_null h_extr bf_bot, absurd 
      (social_top_of_all_top b_in hwp (λ j, top_of_not_bot_of_extr (h_extr j) _)) 
      (not_top_of_bot bf_bot (second_distinct_mem hX b_in))) 
    (λ i D i_not_in ih P h_insert h_extr bf_bot, _),
  { simpa using eq_empty_iff_forall_not_mem.mp h_null.symm j },
  { have X_ne := nonempty_of_ne_empty (ne_empty_of_mem b_in),
    have h_extr' : ∀ j, is_extremal b (ite (j = i) (maketop (P j) b X X_ne) (P j)) X,
    { intro j,
      by_cases hji : j = i,
      { refine or.inr (λ a a_in hab, _),
        simp only [if_pos hji, lt_of_maketop _ hab X_ne a_in] },
      { simp only [if_neg hji, h_extr j] } },
    by_cases hP' : is_top_of b (f (λ j, ite (j = i) (maketop (P j) b X X_ne) (P j))) X,
    { refine ⟨i, P, _, λ j hj x y _ _, _, h_extr, h_extr', _, _, bf_bot, hP'⟩,
      { simp [same_order, if_neg hj] },
      { have : i ∈ {j ∈ univ | is_bot_of b (P j) X}, { rw ← h_insert, exact mem_insert_self i D },
        simpa },
      { simp [top_of_maketop, X_ne] } },
    { refine ih _ h_extr' (bot_of_not_top_of_extr (first_step hwp hind hX b_in h_extr') hP'),
      ext j, 
      simp only [true_and, sep_def, mem_filter, mem_univ],
      split; intro hj,
      { suffices : j ∈ insert i D, 
        { have hji : j ≠ i, 
          { rintro rfl, 
            exact i_not_in hj },
          rw h_insert at this, 
          simpa [hji] },
        exact mem_insert_of_mem hj },
      { have hji : j ≠ i,
        { rintro rfl,
          obtain ⟨a, a_in, hab⟩ := second_distinct_mem hX b_in,
          apply asymm (top_of_maketop b (P j) X_ne a a_in hab),
          simpa using hj a a_in hab },
        rw [← erase_insert i_not_in, h_insert],
        simpa [hji] using hj } } }, 
end 

lemma second_step [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (b) (b_in : b ∈ X) :
  ∃ n', is_pivotal f X n' b := 
begin
  classical,
  have h_bot : is_bot_of b (λ x, ite (x = b) 0 1) X := λ _ _ h, by simp [h],
  exact second_step_aux hwp hind hX b_in rfl (λ i, extremal_of_bot_of h_bot) 
    (social_bot_of_all_bot b_in hwp (λ i, h_bot)),
end

lemma third_step (hind : ind_of_irr_alts f X) 
  (hX : 3 ≤ X.card) (b_in : b ∈ X) {i : ι} (i_piv : is_pivotal f X i b) :
  is_dictator_except f X i b :=
begin
  intros a a_in c c_in a_neq_b c_neq_b Q hyp,
  rcases i_piv with ⟨P, P', i_piv⟩,
  have X_ne : X.nonempty := card_pos.1 (by linarith),
  classical,
  let Q' := λ j, 
    if hx : j = i 
      then makebetween (Q j) a b c
    else 
      if is_bot_of b (P j) X 
        then makebot (Q j) b X X_ne
      else maketop (Q j) b X X_ne,
  have Q'_eq : ∀ j, ∀ d ≠ b, Q j d = Q' j d,
  { intros j d d_neq,
    by_cases hj : j = i,
    { rw ← makebetween_noteq (Q j) d_neq,
      simp [Q'],
      rw if_pos hj, },
    { simp [Q'],
      rw if_neg hj,
      by_cases hbot : is_bot_of b (P j) X,
      { rw [← makebot_noteq (Q j) d_neq X_ne, if_pos hbot], },
      { rw [← maketop_noteq (Q j) d_neq X_ne, if_neg hbot], }, }, },
  have hQ'bc : ∀ j, P j b < P j c ↔ Q' j b < Q' j c,
  { refine (λ j, ⟨λ hP, _, λ hQ', _⟩); by_cases hj : j = i,
    { simp [Q'],
      rw if_pos hj,
      rw ← hj at hyp,
      exact lt_top_of_makebetween c_neq_b hyp, },
    { simp [Q'],
      rw if_neg hj,
      have b_bot : is_bot_of b (P j) X,
      { unfold is_bot_of,
        by_contradiction b_bot, push_neg at b_bot,
        rcases b_bot with ⟨d, d_in, d_neq_b, hd⟩,
        cases i_piv.2.1 j,
        { exact (h d d_in d_neq_b).not_le hd },
        { exact (irrefl _) ((h c c_in c_neq_b).trans hP) }, },
      rw if_pos b_bot,
      exact lt_of_makebot (Q j) c_neq_b X_ne c_in, },
    { convert i_piv.2.2.2.1 c c_in c_neq_b },
      { by_contradiction hP, push_neg at hP,
        have not_bot : ¬ is_bot_of b (P j) X := λ h, (h c c_in c_neq_b).not_le hP,
        apply asymm (lt_of_maketop (Q j) c_neq_b X_ne c_in),
        convert hQ'; simp [Q', if_neg, not_bot, hj] }, },
  have hQ'ab : ∀ j, P' j a < P' j b ↔ Q' j a < Q' j b,
  { refine (λ j, ⟨λ hP', _, λ hQ', _⟩); by_cases hj : j = i,
    { simp [Q'],
      rw if_pos hj,
      rw ← hj at hyp,
      exact bot_lt_of_makebetween a_neq_b hyp, },
    { simp [Q'],
      rw if_neg hj,
      have not_bot : ¬ is_bot_of b (P j) X :=
        λ h, asymm ((i_piv.1 j hj a b a_in b_in).1.mpr hP') (h a a_in a_neq_b),
      rw if_neg not_bot,
      linarith [lt_of_maketop (Q j) a_neq_b X_ne a_in], },
    { convert i_piv.2.2.2.2.1 a a_in a_neq_b, },
    { simp only at hQ', simp only [Q', dite_eq_ite, if_neg hj] at hQ',
      have not_bot : ¬ (is_bot_of b (P j) X),
      { by_contradiction b_bot, 
        rw if_pos b_bot at hQ',
        linarith [lt_of_makebot (Q j) a_neq_b X_ne a_in], },
      rw if_neg not_bot at hQ',
      rw ← (i_piv.1 j hj a b a_in b_in).1,
      have b_top : is_top_of b (P j) X := top_of_not_bot_of_extr (i_piv.2.1 j) not_bot,
      exact b_top a a_in a_neq_b, }, },
  have hQQ' : ∀ i, Q i a < Q i c ↔ Q' i a < Q' i c := λ i, by rw [Q'_eq, Q'_eq]; assumption,
  rw hind a c a_in c_in Q Q' hQQ', 
  have h₁ : f Q' a < f Q' b,
  { rw ← hind a b a_in b_in P' Q' hQ'ab,
    exact i_piv.2.2.2.2.2.2 a a_in a_neq_b },
  have h₂ : f Q' b < f Q' c,
  { rw ← hind b c b_in c_in P Q' hQ'bc,
    exact i_piv.2.2.2.2.2.1 c c_in c_neq_b },
  exact h₁.trans h₂,
end

lemma fourth_step (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (h : ∀ b ∈ X, ∃ n', is_pivotal f X n' b) : 
  is_dictatorship f X := 
begin
  have X_pos : 0 < X.card := by linarith,
  obtain ⟨b, b_in⟩ := (card_pos.1 X_pos).bex,
  obtain ⟨i, i_piv⟩ := h b b_in,
  have : ∀ a ∈ X, a ≠ b → ∀ Pᵢ : ι → σ → ℝ, 
          (Pᵢ i a < Pᵢ i b → f Pᵢ a < f Pᵢ b) ∧ (Pᵢ i b < Pᵢ i a → f Pᵢ b < f Pᵢ a),
  { intros a a_in ha Pᵢ,
    obtain ⟨c, c_in, not_a, not_b⟩ := third_distinct_mem hX a_in b_in ha,
    obtain ⟨j, j_piv⟩ := h c c_in,
    have j_dict := third_step hind hX c_in j_piv, 
    have hij : i = j,
    { by_contra hij,
      rcases i_piv with ⟨R, R', hi₁, hi₂, hi₃, hi₄, hi₅, hi₆, hi₇⟩,
      refine asymm (hi₇ a a_in ha) 
        (j_dict b b_in a a_in (ne_comm.1 not_b) (ne_comm.1 not_a) R' 
          ((hi₁ j (ne_comm.1 hij) a b a_in b_in).2.1 _)),
      by_contra hnot,
      have H := (hi₂ j).resolve_left,
      simp only [is_top_of, is_bot_of, and_imp, exists_imp_distrib, not_forall] at H,
      exact asymm (hi₆ a a_in ha) (j_dict a a_in b b_in (ne_comm.1 not_a) (ne_comm.1 not_b) R
        (H a a_in ha hnot a a_in ha)) },
    rw hij,
    split; refine j_dict _ _ _ _ (ne_comm.1 _) (ne_comm.1 _) Pᵢ; assumption, },
  refine ⟨i, λ x y x_in y_in Pᵢ hyp, _⟩,
  rcases @eq_or_ne _ b x with rfl | hx; rcases @eq_or_ne _ b y with rfl | hy, -- @s will drop when we merge master
  { exact ((irrefl _) hyp).rec _ },
  { exact (this y y_in hy.symm Pᵢ).2 hyp },
  { exact (this x x_in hx.symm Pᵢ).1 hyp },
  { exact third_step hind hX b_in i_piv x x_in y y_in hx.symm hy.symm Pᵢ hyp },
end

lemma arrows_theorem [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) :
  is_dictatorship f X := 
fourth_step hind hX $ second_step hwp hind hX