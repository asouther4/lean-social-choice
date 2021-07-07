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

/-- A social welfare function satisfies the Weak Pareto criterion if, for any two social states 
  `x` and `y`, every individual ranking `y` higher than `x` implies that society ranks `y` higher 
  than `x`. -/
def weak_pareto (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) : Prop := 
∀ (x y ∈ X) (P : ι → σ → ℝ), (∀ i, P i x < P i y) → (f P) x < (f P) y

/-- Suppose that for any two social states `x` and `y`, every individual's ranking of `x` and `y`
  remains unchanged between two rankings `P₁` and `P₂`. We say that a social welfare function is 
  *independent of irrelevant alternatives* if society's ranking of `x` and `y` also remains 
  unchanged between `P₁` and `P₂`. -/
def ind_of_irr_alts (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) : Prop := 
∀ (x y ∈ X) (P₁ P₂ : ι → σ → ℝ), 
  (∀ i, P₁ i x < P₁ i y ↔ P₂ i x < P₂ i y) → (f P₁ x < f P₁ y ↔ f P₂ x < f P₂ y)

/-- An individual is a *dictator* with respect to a given social welfare function if their 
  ranking determines society's ranking of any two social states. -/
def is_dictator (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) (i : ι) : Prop :=
∀ (x y ∈ X) (P : ι → σ → ℝ), P i x < P i y → f P x < f P y

/-- A social welfare function is called a *dictatorship* if there exists a dictator with respect to
 that function. -/
def is_dictatorship (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) : Prop :=
∃ i, is_dictator f X i

/-- An individual is a dictator over all social states in a given set *except* `b` 
  if they are a dictator over every pair of distinct alternatives not equal to `b`.  -/
def is_dictator_except (f : (ι → σ → ℝ) → (σ → ℝ)) (X : finset σ) (i : ι) (b : σ) : Prop := 
∀ a c ∈ X, a ≠ b → c ≠ b → ∀ P : ι → σ → ℝ, P i a < P i c → f P a < f P c

/-- A social welfare function is called a dictatorship over all social states in a given set 
  *except* `b` if there exists a dictator over every pair of distinct alternatives not equal 
  to `b`.  -/
def is_dictatorship_except (f : (ι → σ → ℝ) → (σ → ℝ)) (X : finset σ) (b : σ) : Prop := 
∃ i, is_dictator_except f X i b

/-- A social state `b` is *bottom* of a finite set of social states `X` with respect to 
  a ranking `p` if `b` is ranked strictly lower than every other `a ∈ X`. -/
def is_bot (b : σ) (p : σ → ℝ) (X : finset σ) : Prop :=
∀ a ∈ X, a ≠ b → p b < p a

/-- A social state `b` is *top* of a finite set of social states `X` with respect to
  a ranking `p` if `b` is ranked strictly higher than every other `a ∈ X`. -/
def is_top (b : σ) (p : σ → ℝ) (X : finset σ) : Prop := 
∀ a ∈ X, a ≠ b → p a < p b

/-- A social state `b` is *extremal* with respect to a finite set of social states `X` 
  and a ranking `p` if `b` is either bottom or top of `X`. -/
def is_extremal (b : σ) (p : σ → ℝ) (X : finset σ) : Prop := 
is_bot b p X ∨ is_top b p X

/-- Social sates `s₁`, `s₂`, `s₃`, and `s₄` have the *same order* with respect to two rankings 
  `p₁` and `p₂` if `s₁` and `s₂` have the same ranking in `p₁` as `s₃` and `s₄` have in `p₂`. -/
def same_order (p₁ p₂ : σ → ℝ) (s₁ s₂ s₃ s₄ : σ) : Prop :=
(p₁ s₁ < p₁ s₂ ↔ p₂ s₃ < p₂ s₄) ∧ (p₁ s₂ < p₁ s₁ ↔ p₂ s₄ < p₂ s₃)

/-- An individual `i` is *pivotal* with respect to a social welfare function and a social state `b` 
  if there exist rankings `P` and `P'` such that: 
  (1) all individuals except for `i` rank all social states in the same order in both rankings
  (2) all individuals place `b` in an extremal position in both rankings
  (3) `i` ranks `b` bottom of their rankings in `P`, but top of their rankings in `P'`
  (4) society ranks `b` bottom of its rankings in `P`, but top of its rankings in `P'` -/
def is_pivotal (f : (ι → σ → ℝ) → (σ → ℝ)) (X : finset σ) (i : ι) (b : σ) : Prop := 
∃ (P P' : ι → σ → ℝ),
  (∀ j : ι, j ≠ i → ∀ x y ∈ X, same_order (P j) (P' j) x y x y) ∧ 
    (∀ i : ι, is_extremal b (P i) X) ∧ (∀ i : ι, is_extremal b (P' i) X) ∧
      (is_bot b (P i) X) ∧ (is_top b (P' i) X) ∧ 
        (is_bot b (f P) X) ∧ (is_top b (f P') X)

/-- A social welfare function has a *pivot* with respect to a social state `b` if there exists an
  individual who is pivotal with respect to that function and `b`. -/
def has_pivot (f : (ι → σ → ℝ) → (σ → ℝ)) (X : finset σ) (b : σ) : Prop := 
∃ i, is_pivotal f X i b

open function

/-- Given an arbitary ranking `p`, social state `b`, and finite set of social states `X`,
  `maketop b p X` updates `p` so that `b` is now ranked at the top of `X`. -/
noncomputable def maketop [decidable_eq σ] 
  (p : σ → ℝ) (b : σ) (X : finset σ) (hX : X.nonempty) : σ → ℝ :=
update p b $ ((X.image p).max' (hX.image p)) + 1

/-- Given an arbitary ranking `p`, social state `b`, and finite set of social states `X`,
  `makebot b p X` updates `p` so that `b` is now ranked at the bottom of `X`. -/
noncomputable def makebot [decidable_eq σ]
  (p : σ → ℝ) (b : σ) (X : finset σ) (hX : X.nonempty) : σ → ℝ :=
update p b $ ((X.image p).min' (hX.image p)) - 1

/-- Given an arbitary ranking `p` and social states `a`, `b`, and `c`, 
  `makebetween p a b c` updates `p` so that `b` is now ranked between `a` and `c`. -/
noncomputable def makebetween [decidable_eq σ] 
  (p : σ → ℝ) (a b c : σ) : σ → ℝ :=
update p b $ (p a + p c) / 2


-- ## Preliminary Lemmas

variables {a b c d : σ} {p : σ → ℝ} {P : ι → σ → ℝ} {f : (ι → σ → ℝ) → σ → ℝ} {X : finset σ}

lemma exists_second_distinct_mem (hX : 2 ≤ X.card) (a_in : a ∈ X) : 
  ∃ b ∈ X, b ≠ a :=
begin
  classical,
  have hpos : 0 < (X.erase a).card,
  { rw card_erase_of_mem a_in,
    exact zero_lt_one.trans_le (nat.pred_le_pred hX) },
  cases card_pos.mp hpos with b hb,
  cases mem_erase.mp hb with hne H,
  exact ⟨b, H, hne⟩,
end

lemma exists_third_distinct_mem (hX : 2 < X.card) (a_in : a ∈ X) (b_in : b ∈ X) (h : a ≠ b) : 
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

lemma is_top.not_bot (htop : is_top b p X) (h : ∃ a ∈ X, a ≠ b) : ¬is_bot b p X :=
begin
  simp only [is_bot, not_forall, not_lt, exists_prop],
  rcases h with ⟨a, a_in, hab⟩,
  exact ⟨a, a_in, hab, (htop a a_in hab).le⟩,
end

lemma is_top.not_bot' (htop : is_top b p X) (hX : 2 ≤ X.card) (hb : b ∈ X) : ¬is_bot b p X :=
htop.not_bot $ exists_second_distinct_mem hX hb

lemma is_bot.not_top (hbot : is_bot b p X) (h : ∃ a ∈ X, a ≠ b) : ¬is_top b p X :=
begin
  simp only [is_top, not_forall, not_lt, exists_prop],
  rcases h with ⟨a, a_in, hab⟩,
  exact ⟨a, a_in, hab, (hbot a a_in hab).le⟩,
end

lemma is_bot.not_top' (hbot : is_bot b p X) (hX : 2 ≤ X.card) (hb : b ∈ X) : ¬is_top b p X :=
hbot.not_top $ exists_second_distinct_mem hX hb

lemma is_extremal.is_top (hextr : is_extremal b p X) (not_bot : ¬is_bot b p X) :
  is_top b p X := 
hextr.resolve_left not_bot 

lemma is_extremal.is_bot (hextr : is_extremal b p X) (not_top : ¬is_top b p X) :
  is_bot b p X := 
hextr.resolve_right not_top 

lemma is_bot.is_extremal (hbot : is_bot b p X) : is_extremal b p X := 
or.inl hbot

lemma is_top.is_extremal (hbot : is_top b p X) : is_extremal b p X := 
or.inr hbot

/-- If every individual ranks a social state `b` at the top of its rankings, then society must also
  rank `b` at the top of its rankings. -/
theorem is_top_of_forall_is_top (b_in : b ∈ X) (hwp : weak_pareto f X)
  (htop : ∀ i, is_top b (P i) X) :
  is_top b (f P) X :=
λ a a_in hab, hwp a b a_in b_in P $ λ i, htop i a a_in hab

/-- If every individual ranks a social state `b` at the bottom of its rankings, then society must 
  also rank `b` at the bottom of its rankings. -/
theorem is_bot_of_forall_is_bot (b_in : b ∈ X) (hwp : weak_pareto f X) 
  (hbot : ∀ i, is_bot b (P i) X) :
  is_bot b (f P) X :=
λ a a_in hab, hwp b a b_in a_in P $ λ i, hbot i a a_in hab

lemma exists_of_not_extremal (hX : 3 ≤ X.card) (hb : b ∈ X) (h : ¬ is_extremal b (f P) X):
  ∃ a c ∈ X, a ≠ b ∧ c ≠ b ∧ a ≠ c ∧ f P b ≤ f P a ∧ f P c ≤ f P b := 
begin
  unfold is_extremal is_bot is_top at h, push_neg at h,
  obtain ⟨⟨c, hc, hcb, hPc⟩, ⟨a, ha, hab, hPa⟩⟩ := h,
  obtain hac | rfl := @ne_or_eq _ a c, { exact ⟨a, c, ha, hc, hab, hcb, hac, hPa, hPc⟩ },
  obtain ⟨d, hd, hda, hdb⟩ := exists_third_distinct_mem hX ha hb hab,
  cases lt_or_le (f P b) (f P d),
  { exact ⟨d, a, hd, hc, hdb, hcb, hda, h.le, hPc⟩ },
  { exact ⟨a, d, ha, hd, hab, hdb, hda.symm, hPa, h⟩ },
end

lemma nonempty_of_mem {s : finset σ} {a : σ} (ha : a ∈ s) : s.nonempty := 
nonempty_of_ne_empty $ ne_empty_of_mem ha

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

lemma maketop_lt_maketop (p) (hab : a ≠ b) (ha : a ∈ X) : 
  maketop p b X (nonempty_of_mem ha) a < maketop p b X (nonempty_of_mem ha) b :=
by simpa [maketop, hab] using 
  ((X.image p).le_max' _ (mem_image_of_mem p ha)).trans_lt (lt_add_one _)

lemma makebot_lt_makebot (p) (hcb : c ≠ b) (hc : c ∈ X) : 
  makebot p b X (nonempty_of_mem hc) b < makebot p b X (nonempty_of_mem hc) c :=
by simpa [makebot, hcb] using sub_lt_iff_lt_add'.mpr
  (((X.image p).min'_le (p c) (mem_image_of_mem p hc)).trans_lt (lt_one_add _))

lemma makebetween_lt_makebetween_top (hcb : c ≠ b) (hp : p a < p c) : 
  makebetween p a b c b < makebetween p a b c c :=
begin
  simp only [makebetween, update_same, update_noteq hcb],
  linarith,
end

lemma makebetween_lt_makebetween_bot (hab : a ≠ b) (hp : p a < p c) : 
  makebetween p a b c a < makebetween p a b c b :=
begin
  simp only [makebetween, update_same, update_noteq hab],
  linarith,
end

lemma top_of_maketop (b p) (hX : X.nonempty) :
  is_top b (maketop p b X hX) X := 
λ a ha hab, maketop_lt_maketop p hab ha

end make

-- ## The Proof

/-- Let `f` be a SWF satisfying WP and IoIA, `P` be a preference ordering, `X` be a finite set
  containing at least 3 social states, and `b` be one of those social states.
  If every individial ranks `b` extremally, then society also ranks `b` extremally w.r.t. `f`. -/
lemma first_step (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (hb : b ∈ X) (hextr : ∀ i, is_extremal b (P i) X) :
  is_extremal b (f P) X := 
begin
  classical,
  by_contra hnot,
  obtain ⟨a, c, ha, hc, hab, hcb, hac, hPa, hPc⟩ := exists_of_not_extremal hX hb hnot,
  refine ((not_lt.mp ((not_congr (hind b c hb hc P _ (λ i, ⟨λ hP, _, λ hP', _⟩))).mp 
    hPc.not_lt)).trans (not_lt.mp ((not_congr (hind a b ha hb P _ (λ i, ⟨λ hP, _, λ hP', _⟩))).mp 
      hPa.not_lt))).not_lt (hwp a c ha hc _ (λ i, _)),
  { exact λ j, if is_top b (P j) X then makebetween (P j) a c b else update (P j) c (P j a + 1) },
  { have h : ¬ is_top b (P i) X := λ h, asymm hP (h c hc hcb),
    convert lt_add_of_lt_of_pos ((hextr i).is_bot h a ha hab) _; simp [h, hcb.symm] },
  { by_contra hP,
    have h : is_top b (P i) X := (hextr i).is_top (λ h, hP (h c hc hcb)),
    simp only at hP', simp only [if_pos h, makebetween_noteq _ hcb.symm, makebetween_eq] at hP',
    linarith [h a ha hab] },
  { by_cases h : is_top b (P i) X; simpa [h, makebetween_noteq, hac, hcb.symm] },
  { by_contra hP,
    have h : ¬ is_top b (P i) X := λ h, hP (h a ha hab),
    simp only at hP', simp [if_neg h, hac, hcb.symm] at hP',
    exact hP hP' },
  { by_cases h : is_top b (P i) X,
    { simp [if_pos h, makebetween_lt_makebetween_bot hac (h a ha hab)] },
    { simp [if_neg h, hac] } },
end  

/-- An auxiliary lemma for the second step, in which we perform induction on the finite set
  `D' := {i ∈ univ | is_bot b (P i) X}`. Its statement is formulated so strangely (involving `D'` 
  and `P`) to allow for this induction. 
  Essentially, what we are doing here is showing that, for a social welfare function `f` under the
  appropriate conditions, we can always a construct circumstances so that `f` has a pivot with
  respect to a given social state. -/
lemma second_step_aux [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 2 < X.card) (b_in : b ∈ X) {D' : finset ι} :
  ∀ {P : ι → σ → ℝ}, D' = {i ∈ univ | is_bot b (P i) X} → 
    (∀ i, is_extremal b (P i) X) → is_bot b (f P) X → has_pivot f X b := 
begin
  classical,
  refine finset.induction_on D'
    (λ P h hextr hbot, absurd (is_top_of_forall_is_top b_in hwp (λ j, (hextr j).is_top _))
                              (hbot.not_top (exists_second_distinct_mem hX.le b_in))) 
    (λ i D hi IH P h_insert hextr hbot, _),
  { simpa using eq_empty_iff_forall_not_mem.mp h.symm j },
  { have hX' := nonempty_of_mem b_in,
    have hextr' : ∀ j, is_extremal b (ite (j = i) (maketop (P j) b X hX') (P j)) X,
    { intro j,
      by_cases hji : j = i,
      { refine or.inr (λ a a_in hab, _),
        simp only [if_pos hji, maketop_lt_maketop _ hab a_in] },
      { simp only [if_neg hji, hextr j] } },
    by_cases hP' : is_top b (f (λ j, ite (j = i) (maketop (P j) b X hX') (P j))) X,
    { refine ⟨i, P, _, λ j hj x y _ _, _, hextr, hextr', _, _, hbot, hP'⟩,
      { simp [same_order, if_neg hj] },
      { have : i ∈ {j ∈ univ | is_bot b (P j) X}, { rw ← h_insert, exact mem_insert_self i D },
        simpa },
      { simp [top_of_maketop, hX'] } },
    { refine IH _ hextr' ((first_step hwp hind hX b_in hextr').is_bot hP'),
      ext j,
      simp only [true_and, sep_def, mem_filter, mem_univ],
      split; intro hj,
      { suffices : j ∈ insert i D,
        { have hji : j ≠ i, { rintro rfl, exact hi hj },
          rw h_insert at this,
          simpa [hji] },
        exact mem_insert_of_mem hj },
      { have hji : j ≠ i,
        { rintro rfl,
          obtain ⟨a, a_in, hab⟩ := exists_second_distinct_mem hX.le b_in,
          apply asymm (top_of_maketop b (P j) hX' a a_in hab),
          simpa using hj a a_in hab },
        rw [← erase_insert hi, h_insert],
        simpa [hji] using hj } } }, 
end 

/-- Let `f` be a SWF satisfying WP and IoIA, and `X` be a finite set containing at least 3 social states.
  Then `f` has a pivot w.r.t. every social state in `X`. -/
lemma second_step [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (b) (b_in : b ∈ X) :
  has_pivot f X b := 
begin
  classical,
  have hbot : is_bot b (λ x, ite (x = b) 0 1) X := λ _ _ h, by simp [h],
  exact second_step_aux hwp hind hX b_in rfl (λ i, hbot.is_extremal) 
    (is_bot_of_forall_is_bot b_in hwp (λ i, hbot)),
end

/-- Let `f` be a SWF satisfying IoIA, `X` be a finite set of social states, and `b` be one of those 
  social states.
  If an individual `i` is pivotal w.r.t. `f` and `b`, then `i` is a dictator over all social states
  in `X` except `b`. -/
lemma third_step (hind : ind_of_irr_alts f X) 
  (hb : b ∈ X) {i : ι} (hpiv : is_pivotal f X i b) :
  is_dictator_except f X i b :=
begin
  intros a c ha hc hab hcb Q hyp,
  obtain ⟨P, P', hpiv⟩ := hpiv,
  have hX := nonempty_of_ne_empty (ne_empty_of_mem hb),
  classical,
  let Q' := λ j, 
    if j = i 
      then makebetween (Q j) a b c
    else 
      if is_bot b (P j) X 
        then makebot (Q j) b X hX
      else maketop (Q j) b X hX,
  refine (hind a c ha hc Q Q' (λ j, _)).mpr
    (((hind a b ha hb P' Q' (λ j, _)).mp (hpiv.2.2.2.2.2.2 a ha hab)).trans
      ((hind b c hb hc P Q' (λ j, _)).mp (hpiv.2.2.2.2.2.1 c hc hcb))),
  { suffices : ∀ d ≠ b, Q j d = Q' j d, { rw [this, this]; assumption },
    intros d hdb,
    by_cases hj : j = i; simp only [Q', if_pos, hj, dite_eq_ite], 
    { exact (makebetween_noteq (Q i) hdb).symm },
    { by_cases hbot : is_bot b (P j) X; simp only [if_neg hj],
      { rw [← makebot_noteq (Q j) hdb hX, if_pos hbot] },
      { rw [← maketop_noteq (Q j) hdb hX, if_neg hbot] } } },
  { refine ⟨λ hP', _, λ hQ', _⟩; by_cases hj : j = i,
    { simpa [Q', if_pos, hj] using makebetween_lt_makebetween_bot hab hyp },
    { have hbot : ¬ is_bot b (P j) X := λ h, asymm ((hpiv.1 j hj a b ha hb).1.2 hP') (h a ha hab),
      simpa [Q', if_neg, hj, hbot] using maketop_lt_maketop (Q j) hab ha },
    { convert hpiv.2.2.2.2.1 a ha hab },
    { refine (hpiv.1 j hj a b ha hb).1.1 ((hpiv.2.1 j).is_top 
        (λ hbot, asymm (makebot_lt_makebot (Q j) hab ha) _) a ha hab), 
      convert hQ'; simp [Q', if_neg hj, if_pos hbot] } },
  { refine ⟨λ hP, _, λ hQ', _⟩; by_cases hj : j = i,
    { simpa [Q', if_pos, hj] using makebetween_lt_makebetween_top hcb hyp },
    { have hbot : is_bot b (P j) X,
      { unfold is_bot,
        by_contra hbot, push_neg at hbot,
        obtain ⟨d, hd, hdb, h⟩ := hbot,
        cases hpiv.2.1 j with hbot htop,
        { exact (hbot d hd hdb).not_le h },
        { exact (irrefl _) ((htop c hc hcb).trans hP) } },
      simpa [Q', if_neg hj, if_pos hbot] using makebot_lt_makebot (Q j) hcb hc },
    { convert hpiv.2.2.2.1 c hc hcb },
    { by_contra hP,
      have hbot : ¬ is_bot b (P j) X := λ h, hP (h c hc hcb),
      apply asymm (maketop_lt_maketop (Q j) hcb hc),
      convert hQ'; simp [Q', if_neg, hbot, hj] } },
end

/-- Let `f` be a SWF satisfying IoIA, and `X` be a finite set containing at least 3 social states. 
  If `f` has a pivot for every social state in `X`, then `f` is a dictatorship. -/
lemma fourth_step (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (hpiv : ∀ b ∈ X, has_pivot f X b) : 
  is_dictatorship f X := 
begin
  obtain ⟨b, hb⟩ := (card_pos.1 (zero_lt_two.trans hX)).bex,
  obtain ⟨i, ipiv⟩ := hpiv b hb,
  have h : ∀ a ∈ X, a ≠ b → ∀ Pᵢ : ι → σ → ℝ, 
          (Pᵢ i a < Pᵢ i b → f Pᵢ a < f Pᵢ b) ∧ (Pᵢ i b < Pᵢ i a → f Pᵢ b < f Pᵢ a), -- we should have a better way of stating this that doesn't require the and (i.e. stated WLOG)
  { intros a ha hab Pᵢ,
    obtain ⟨c, hc, hca, hcb⟩ := exists_third_distinct_mem hX ha hb hab,
    obtain ⟨hac, hbc⟩ := ⟨hca.symm, hcb.symm⟩,
    obtain ⟨j, jpiv⟩ := hpiv c hc,
    obtain hdict := third_step hind hc jpiv,
    obtain rfl : j = i,
    { by_contra hji,
      obtain ⟨R, R', hso, hextr, -, -, -, hbot, htop⟩ := ipiv,
      refine asymm (htop a ha hab) (hdict b a hb ha hbc hac R' ((hso j hji a b ha hb).2.1 _)),
      by_contra hnot,
      have h := (hextr j).resolve_left,
      simp only [is_top, is_bot, and_imp, exists_imp_distrib, not_forall] at h,
      exact asymm (hbot a ha hab) (hdict a b ha hb hac hbc R (h a ha hab hnot a ha hab)) },
    split; apply hdict; assumption },
  refine ⟨i, λ x y hx hy Pᵢ hPᵢ, _⟩,
  rcases @eq_or_ne _ b x with rfl | hbx; rcases @eq_or_ne _ b y with rfl | hby, -- @s will drop when we merge master
  { exact ((irrefl _) hPᵢ).rec _ },
  { exact (h y hy hby.symm Pᵢ).2 hPᵢ },
  { exact (h x hx hbx.symm Pᵢ).1 hPᵢ },
  { exact third_step hind hb ipiv x y hx hy hbx.symm hby.symm Pᵢ hPᵢ },
end

/-- Arrow's Impossibility Theorem: Any social welfare function involving at least three social
  states that satisfies WP and IoIA is necessarily a dictatorship. -/
theorem arrow [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) :
  is_dictatorship f X := 
fourth_step hind hX $ second_step hwp hind hX
