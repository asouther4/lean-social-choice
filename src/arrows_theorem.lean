import basic

/- 

In this file, we formalize a proof of Arrow's Impossibility Theorem. 
We closely follow the first proof in this 2005 paper by John Geankopolos: 
* https://link.springer.com/article/10.1007/s00199-004-0556-7


Arrow's Impossibility Theorem has been formalized in other languages before. 

Freek Wiedijk wrote a formalization in Mizar: 
* https://link.springer.com/article/10.1007/s12046-009-0005-1

Tobias Nipkow wrote a formalization in Isabelle/HOL: 
* https://link.springer.com/article/10.1007/s10817-009-9147-4


At times, our formalization is a close translation of Nipkow's proof in HOL. 
In particular, our definition of functions `maketop`, `makebot`, and `makeabove` are 
inspired by his strategy for manipulating preferences. However, Nipkow defines preference orders 
in a completely different way from our `basic` file. 
-/


open relation vector finset

-- We think of social states as type `σ` and inidividuals as type `ι`
variables {σ ι : Type} {x y x' y' a b : σ} {r r' : σ → σ → Prop} {X : finset σ}

/-! ### Some basic definitions and lemmas -/

/-- A social state `b` is *bottom* of a finite set of social states `X` with respect to 
  a ranking `p` if `b` is ranked strictly lower than every other `a ∈ X`. -/
def is_bot (b : σ) (r : σ → σ → Prop) (X : finset σ) : Prop :=
∀ a ∈ X, a ≠ b → P r a b

/-- A social state `b` is *top* of a finite set of social states `X` with respect to
  a ranking `p` if `b` is ranked strictly higher than every other `a ∈ X`. -/
def is_top (b : σ) (r : σ → σ → Prop) (X : finset σ) : Prop := 
∀ a ∈ X, a ≠ b → P r b a

/-- A social state `b` is *extremal* with respect to a finite set of social states `X` 
  and a ranking `p` if `b` is either bottom or top of `X`. -/
def is_extremal (b : σ) (r : σ → σ → Prop) (X : finset σ) : Prop := 
is_bot b r X ∨ is_top b r X

lemma not_bot : ¬is_bot b r X ↔ ∃ a (h1 : a ∈ X) (h2 : a ≠ b), ¬P r a b :=
by simp only [is_bot, not_forall]

lemma not_top : ¬is_top b r X ↔ ∃ a (h1 : a ∈ X) (h2 : a ≠ b), ¬P r b a :=
by simp only [is_top, not_forall]

lemma is_top.not_bot (htop : is_top b r X) (h : ∃ a ∈ X, a ≠ b) : ¬is_bot b r X :=
let ⟨a, a_in, hab⟩ := h in not_bot.mpr ⟨a, a_in, hab, nP_of_reverseP (htop a a_in hab)⟩

lemma is_top.not_bot' (htop : is_top b r X) (hX : 2 ≤ X.card) (hb : b ∈ X) : ¬is_bot b r X :=
htop.not_bot $ exists_second_distinct_mem hX hb

lemma is_bot.not_top (hbot : is_bot b r X) (h : ∃ a ∈ X, a ≠ b) : ¬is_top b r X :=
let ⟨a, a_in, hab⟩ := h in not_top.mpr ⟨a, a_in, hab, nP_of_reverseP (hbot a a_in hab)⟩

lemma is_bot.not_top' (hbot : is_bot b r X) (hX : 2 ≤ X.card) (hb : b ∈ X) : ¬is_top b r X :=
hbot.not_top $ exists_second_distinct_mem hX hb

lemma is_extremal.is_top (hextr : is_extremal b r X) (not_bot : ¬is_bot b r X) :
  is_top b r X := 
hextr.resolve_left not_bot 

lemma is_extremal.is_bot (hextr : is_extremal b r X) (not_top : ¬is_top b r X) :
  is_bot b r X := 
hextr.resolve_right not_top 

lemma is_bot.is_extremal (hbot : is_bot b r X) : is_extremal b r X := 
or.inl hbot

lemma is_top.is_extremal (hbot : is_top b r X) : is_extremal b r X := 
or.inr hbot

/-! ### "Make" functions -/

local attribute [instance] classical.prop_decidable

/-- Given an arbitary preference order `r` and a social state `b`,
  `maketop r b` updates `r` so that `b` is now ranked strictly higher 
  than any other social state. 
  The definition also contains a proof that this new relation is a `pref_order σ`. --/
def maketop (r : pref_order σ) (b : σ) : pref_order σ := 
begin
  use λ x y, if x = b then true else if y = b then false else r x y,
  { intro x,
    split_ifs,
    { trivial },
    { exact r.refl x } },
  { intros x y, simp only,
    split_ifs with hx _ hy,
    work_on_goal 3 { exact r.total x y },
    all_goals { simp only [or_true, true_or] } },
  { intros x y z, simp only,
    split_ifs with hx _ _ hy _ hz; intros hxy hyz,
    work_on_goal 6 { exact r.trans hxy hyz },
    all_goals { trivial } },
end  

/-- Given an arbitary preference order `r` and a social state `b`,
  `makebot r b` updates `r` so that every other social state is now ranked 
  strictly higher than `b`. 
  The definition also contains a proof that this new relation is a `pref_order σ`. --/
def makebot (r : pref_order σ) (b : σ) : pref_order σ := 
begin
  use λ x y, if y = b then true else if x = b then false else r x y,
  { intro x,
    split_ifs,
    { trivial },
    { exact r.refl x } },
  { intros x y, simp only,
    split_ifs with hx _ hy,
    work_on_goal 3 { exact r.total x y },
    all_goals { simp only [or_true, true_or] } },
  { intros x y z, simp only,
    split_ifs with hx _ _ hy _ hz; intros hxy hyz,
    work_on_goal 6 { exact r.trans hxy hyz },
    all_goals { trivial } },
end

/-- Given an arbitary preference order `r` and two social states `a` and `b`, 
  `makebot r a b` updates `r` so that: 
  (1) `b` is strictly higher than `a` and any other social state `y` where `r a y`
  (2) any other social state that is strictly higher than `a` is strictly higher than `b`.
  Intuitively, we have moved `b` just above `a` in the ordering. 
  The definition also contains a proof that this new relation is a `pref_order σ`. --/
def makeabove (r : pref_order σ) (a b : σ) : pref_order σ := 
begin
  use λ x y, if x = b then if y = b then true else if r a y then true else false 
             else if y = b then if r a x then false else true else r x y,
  { intro x,
    split_ifs,
    { trivial },
    { exact r.refl x } },
  { intros x y, simp only,
    split_ifs,
    work_on_goal 5 { exact r.total x y }, 
    all_goals { simp only [or_true, true_or] } },
  { intros x y z, simp only,
    split_ifs with hx hy _ _ hay hz haz _ _ hy hax _ _ hz haz hz hay; intros hxy hyz,
    any_goals { trivial },
    { exact haz (r.trans hay hyz) },
    { exact r.trans (pref_order.reverse hax) haz },
    { exact hay (r.trans h hxy) },
    { exact r.trans hxy hyz } },
end 

lemma maketop_noteq (r : pref_order σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
  (maketop r b a c ↔ r a c) ∧ (maketop r b c a ↔ r c a) := 
begin
  simp only [maketop, if_false_left_eq_and, if_true_left_eq_or],
  refine ⟨⟨_, λ h, or.inr ⟨hc, h⟩⟩, ⟨_, λ h, or.inr ⟨ha, h⟩⟩⟩; rintro (rfl | ⟨-, h⟩),
  exacts [absurd rfl ha, h, absurd rfl hc, h],
end

lemma maketop_noteq' (r : pref_order σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
  (P (maketop r b) a c ↔ P r a c) ∧ (P (maketop r b) c a ↔ P r c a) :=
let h := maketop_noteq r ha hc in P_iff_of_iff h.1 h.2

lemma makebot_noteq (r : pref_order σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
  (makebot r b a c ↔ r a c) ∧ (makebot r b c a ↔ r c a) := 
begin
  simp only [makebot, if_false_left_eq_and, if_true_left_eq_or],
  refine ⟨⟨_, λ h, or.inr ⟨ha, h⟩⟩, ⟨_, λ h, or.inr ⟨hc, h⟩⟩⟩; rintro (rfl | ⟨-, h⟩),
  exacts [absurd rfl hc, h, absurd rfl ha, h],
end

lemma makebot_noteq' (r : pref_order σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
  (P (makebot r b) a c ↔ P r a c) ∧ (P (makebot r b) c a ↔ P r c a) :=
let h := makebot_noteq r ha hc in P_iff_of_iff h.1 h.2

lemma makeabove_noteq (r : pref_order σ) (a : σ) {b c d : σ} (hc : c ≠ b) (hd : d ≠ b) :
  (makeabove r a b c d ↔ r c d) ∧ (makeabove r a b d c ↔ r d c) :=
by simp [makeabove, ← pref_order.eq_coe, hc, hd]

lemma makeabove_noteq' (r : pref_order σ) (a : σ) {b c d : σ} (hc : c ≠ b) (hd : d ≠ b) :
  (P (makeabove r a b) c d ↔ P r c d) ∧ (P (makeabove r a b) d c ↔ P r d c) :=
by simp [makeabove, P, ← pref_order.eq_coe, hc, hd]

lemma is_top_maketop (b : σ) (r : pref_order σ) (X : finset σ) :
  is_top b (maketop r b) X :=
by simp [maketop, is_top, P, ← pref_order.eq_coe]

lemma is_bot_makebot (b : σ) (r : pref_order σ) (X : finset σ) :
  is_bot b (makebot r b) X :=
by simp [is_bot, makebot, P, ← pref_order.eq_coe]

lemma makeabove_above {a b : σ} (r : pref_order σ) (ha : a ≠ b):
  P (makeabove r a b) b a :=
by simpa [P, makeabove, ← pref_order.eq_coe, not_or_distrib, ha] using r.refl a

lemma makeabove_above' {a b c : σ} {r : pref_order σ} (hc : c ≠ b) (hr : r a c) :
  P (makeabove r a b) b c :=
by simpa [P, makeabove, ← pref_order.eq_coe, hc]

lemma makeabove_below {a b c : σ} {r : pref_order σ} (hc : c ≠ b) (hr : ¬r a c) :
  P (makeabove r a b) c b :=
by simpa [P, makeabove, ← pref_order.eq_coe, not_or_distrib, hc]

/-! ### Properties -/

/-- A social welfare function satisfies the Weak Pareto criterion if, for any two social states 
  `x` and `y`, every individual ranking `x` higher than `y` implies that society ranks `x` higher 
  than `y`. -/
def weak_pareto (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop := 
∀ (x y ∈ X) (R : ι → pref_order σ), (∀ i : ι, P (R i) x y) → P (f R) x y

/-- Suppose that for any two social states `x` and `y`, every individual's ordering of `x` and `y`
  remains unchanged between two orderings `P₁` and `P₂`. We say that a social welfare function is 
  *independent of irrelevant alternatives* if society's ordering of `x` and `y` also remains 
  unchanged between `P₁` and `P₂`. -/
def ind_of_irr_alts (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop :=
∀ (R R' : ι → pref_order σ) (x y ∈ X), 
  (∀ i : ι, same_order' (R i) (R' i) x y x y) → same_order' (f R) (f R') x y x y

/-- A social welfare function is a *dictatorship* if there exists an individual who possesses the power
   to determine society's order of any social states. -/
def is_dictatorship (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop :=
∃ i : ι, ∀ (x y ∈ X) (R : ι → pref_order σ), P (R i) x y → P (f R) x y

/-- An individual `i` is *pivotal* with respect to a social welfare function and a social state `b`
  if there exist preference orderings `R` and `R'` such that: 
  (1) all individuals except for `i` rank all social states exactly the same in both orderings
  (2) all individuals place `b` in an extremal position in both rankings
  (3) `i` ranks `b` bottom of their rankings in `R`, but top of their rankings in `R'`
  (4) society ranks `b` bottom of its rankings in `R`, but top of its rankings in `R'` -/
def is_pivotal (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) (i : ι) (b : σ) : Prop :=
∃ (R R' : ι → pref_order σ),
  (∀ j : ι, j ≠ i → ∀ x y ∈ X, R j = R' j) ∧ 
    (∀ i : ι, is_extremal b (R i) X) ∧ (∀ i : ι, is_extremal b (R' i) X) ∧
      (is_bot b (R i) X) ∧ (is_top b (R' i) X) ∧ 
        (is_bot b (f R) X) ∧ (is_top b (f R') X)

/-- A social welfare function has a *pivot* with respect to a social state `b` if there exists an
  individual who is pivotal with respect to that function and `b`. -/
def has_pivot (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) (b : σ): Prop := 
∃ i, is_pivotal f X i b

/-- An individual is a dictator over all social states in a given set *except* `b` 
  if they are a dictator over every pair of distinct alternatives not equal to `b`.  -/
def is_dictator_except (f : (ι → pref_order σ) → pref_order σ) 
  (X : finset σ) (i : ι) (b : σ) : Prop := 
∀ a c ∈ X, a ≠ b → c ≠ b → ∀ R : ι → pref_order σ, P (R i) c a → P (f R) c a 

variables {R : ι → pref_order σ} {f : (ι → pref_order σ) → pref_order σ} 

/-! ### Auxiliary lemmas -/

/-- If every individual ranks a social state `b` at the top of its rankings, then society must also
  rank `b` at the top of its rankings. -/
theorem is_top_of_forall_is_top (b_in : b ∈ X) (hwp : weak_pareto f X)
  (htop : ∀ i, is_top b (R i) X) :
  is_top b (f R) X := 
λ a a_in hab, hwp b a b_in a_in R $ λ i, htop i a a_in hab

/-- If every individual ranks a social state `b` at the bottom of its rankings, then society must 
  also rank `b` at the bottom of its rankings. -/
theorem is_bot_of_forall_is_bot (b_in : b ∈ X) (hwp : weak_pareto f X) 
  (hbot : ∀ i, is_bot b (R i) X) :
  is_bot b (f R) X :=
λ a a_in hab, hwp a b a_in b_in R $ λ i, hbot i a a_in hab

lemma exists_of_not_extremal (hX : 3 ≤ X.card) (hb : b ∈ X) (h : ¬ is_extremal b (f R) X):
  ∃ a c ∈ X, a ≠ b ∧ c ≠ b ∧ a ≠ c ∧ f R a b ∧ f R b c := 
begin
  unfold is_extremal is_bot is_top at h, push_neg at h,
  obtain ⟨⟨c, hc, hcb, hPc⟩, ⟨a, ha, hab, hPa⟩⟩ := h,
  obtain ⟨hf, hfa, hfc⟩ := ⟨(f R).total, R_of_nP_total hf hPa, R_of_nP_total hf hPc⟩,
  obtain hac | rfl := @ne_or_eq _ a c, { exact ⟨a, c, ha, hc, hab, hcb, hac, hfa, hfc⟩ },
  obtain ⟨d, hd, hda, hdb⟩ := exists_third_distinct_mem hX ha hb hab,
  cases hf d b,
  { exact ⟨d, a, hd, hc, hdb, hcb, hda, h, hfc⟩ },
  { exact ⟨a, d, ha, hd, hab, hdb, hda.symm, hfa, h⟩ },
end

/-! ### The Proof Begins -/

/- Geankopolos (2005) calls this step the *Extremal Lemma*. If every individual
places alternative `b` in an extremal position (at the very top or bottom of her rankings),
then society must also place alternative `b` in an extremal position. -/
lemma first_step (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (hb : b ∈ X) (hextr : ∀ i, is_extremal b (R i) X) :
  is_extremal b (f R) X :=
begin
  by_contra hnot,
  obtain ⟨a, c, ha, hc, hab, hcb, hac, hfa, hfb⟩ := exists_of_not_extremal hX hb hnot,
  have H1 := λ {j} h, makeabove_below hcb.symm ((hextr j).is_top h a ha hab).2,
  have H2 := λ {j} h, makeabove_above' hcb.symm ((hextr j).is_bot h a ha hab).1,
  refine (hwp c a hc ha (λ j, makeabove (R j) a c) (λ j, makeabove_above (R j) hac)).2 
    ((f _).trans (((same_order_iff_same_order' (f R).total (f _).total).2 -- wouldn't it be better just to do everything using `same_order'`? -Ben
      (hind R _ a b ha hb (λ j, _))).1.1.1 hfa)
        (((same_order_iff_same_order' (f R).total (f _).total).2
          (hind R _ b c hb hc (λ j, ⟨⟨λ h, _ , λ h, _⟩, ⟨λ h, _ , λ h, _⟩⟩))).1.1.1 hfb)),
  { simp only [same_order', makeabove_noteq' (R j) a hcb.symm hac, iff_self, and_self] },
  { apply H1,
    simp only [is_bot, not_forall],
    exact ⟨c, hc, hcb, nP_of_reverseP h⟩ },
  { by_contra hR,
    refine h.2 (H2 _).1,
    simp only [is_top, not_forall],
    exact ⟨c, hc, hcb, hR⟩ },
  { apply H2,
    simp only [is_top, not_forall],
    exact ⟨c, hc, hcb, nP_of_reverseP h⟩ },
  { by_contra hR,
    refine h.2 (H1 _).1,
    simp only [is_bot, not_forall],
    exact ⟨c, hc, hcb, hR⟩ },
end

/-- We define relation `r₂`, a `pref_order` we will use in `second_step`. -/
def r₂ (b : σ) : pref_order σ :=
begin
  use λ x y, if y = b then true else if x = b then false else true,
  { intro x, split_ifs; trivial },
  { intros x y, simp only, split_ifs; simp only [true_or, or_true] },
  { intros x y z, simp only, split_ifs; simp only [forall_true_left, forall_false_left] },
end

/- This is an auxiliary lemma used in the `second_step`. -/
lemma second_step_aux [fintype ι] (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 2 < X.card) (b_in : b ∈ X) {D' : finset ι} :
  ∀ {R : ι → pref_order σ}, D' = {i ∈ univ | is_bot b (R i) X} → 
    (∀ i, is_extremal b (R i) X) → is_bot b (f R) X → has_pivot f X b := 
begin
  refine finset.induction_on D'
    (λ R h hextr hbot, absurd (is_top_of_forall_is_top b_in hwp (λ j, (hextr j).is_top _))
                              (hbot.not_top (exists_second_distinct_mem hX.le b_in))) 
    (λ i D hi IH R h_insert hextr hbot, _),
  { simpa using eq_empty_iff_forall_not_mem.mp h.symm j },
  { let R' := λ j, (ite (j = i) (maketop (R j) b) (R j)),
    have hextr' : ∀ j, is_extremal b (R' j) X,
    { intro j, simp only [R'], 
      split_ifs,
      { exact (is_top_maketop b (R j) X).is_extremal },
      { exact hextr j } },
    by_cases hR' : is_top b (f R') X,
    { refine ⟨i, R, R', λ j hj x y _ _, _, hextr, hextr', _, _, hbot, hR'⟩,
      { simp only [R', if_neg hj] },
      { have : i ∈ {j ∈ univ | is_bot b (R j) X}, { rw ← h_insert, exact mem_insert_self i D },
        simpa },
      { simp only [R', is_top_maketop, if_pos] } },
    { refine IH _ hextr' ((first_step hwp hind hX b_in hextr').is_bot hR'),
      ext j,
      simp only [true_and, sep_def, mem_filter, mem_univ, R'],
      split; intro hj,
      { suffices : j ∈ insert i D,
        { have hji : j ≠ i, { rintro rfl, exact hi hj },
          rw h_insert at this,
          simpa [hji] },
        exact mem_insert_of_mem hj },
      { have hji : j ≠ i,
        { rintro rfl,
          obtain ⟨a, a_in, hab⟩ := exists_second_distinct_mem hX.le b_in,
          simp only [if_pos] at hj,
          exact (is_top_maketop b (R j) X a a_in hab).2 (hj a a_in hab).1 },
        rw [← erase_insert hi, h_insert],
        simpa [hji] using hj } } },
end

/- In his second step, Geankopolos shows that for any social state `b`, 
there exists an individual who is pivotal over that social state.  -/
lemma second_step [fintype ι] (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (b) (b_in : b ∈ X) :
  has_pivot f X b := 
have hbot : is_bot b (r₂ b) X, by simp [is_bot, r₂, P, ←pref_order.eq_coe],
second_step_aux hwp hind hX b_in rfl (λ i, hbot.is_extremal) $
  is_bot_of_forall_is_bot b_in hwp $ λ i, hbot

/- Step 3 states that if an individual `is_pivotal` over some alternative `b`, they 
are also a dictator over every pair of alternatives not equal to `b`. -/
lemma third_step (hind : ind_of_irr_alts f X) 
  (b_in : b ∈ X) {i : ι} (i_piv : is_pivotal f X i b) :
  is_dictator_except f X i b :=
begin
  rintros a c a_in c_in hab hcb Q ⟨-, h⟩,
  obtain ⟨R, R', i_piv⟩ := i_piv,
  let Q' := λ j, if j = i then makeabove (Q j) a b 
                 else if is_bot b (R j) X then makebot (Q j) b else maketop (Q j) b,
  have Q'bot : ∀ j ≠ i, is_bot b (R j) X → Q' j = makebot (Q j) b :=
    λ j hj hbot, by simp only [Q', if_neg hj, if_pos hbot],
  have Q'top : ∀ j ≠ i, ¬is_bot b (R j) X → Q' j = maketop (Q j) b :=
    λ j hj hbot, by simp only [Q', if_neg hj, if_neg hbot],
  have Q'above : Q' i = makeabove (Q i) a b := by simp [Q'],
  have hQ' : ∀ j, same_order' (Q j) (Q' j) c a c a,
  { intro j,
    suffices : ∀ d ≠ b, ∀ e ≠ b, same_order' (Q j) (Q' j) e d e d, from this a hab c hcb,
    intros d hdb e heb, 
    simp only [Q', same_order'],
    split_ifs; simp [makeabove_noteq', makebot_noteq', maketop_noteq', hdb, heb] },
  rw (hind Q Q' c a c_in a_in hQ').1,
  refine P_trans (f Q').trans ((hind R Q' c b c_in b_in _).1.1 (i_piv.2.2.2.2.2.1 c c_in hcb)) 
    ((hind R' Q' b a b_in a_in _).1.1 (i_piv.2.2.2.2.2.2 a a_in hab)); 
      intro j; split; split; intro H; rcases @eq_or_ne _ j i with rfl | hj,
  { convert makeabove_below hcb h },  
  { convert (is_bot_makebot b (Q j) X) c c_in hcb,
    apply Q'bot j hj,
    unfold is_bot,
    by_contra hbot, push_neg at hbot,
    rcases hbot with ⟨d, d_in, hdb, H'⟩,
    cases i_piv.2.1 j with hbot htop,
    { exact H' (hbot d d_in hdb) },
    { exact H.2 (htop c c_in hcb).1 } },
  { exact i_piv.2.2.2.1 c c_in hcb }, 
  { by_contra H',
    apply nP_of_reverseP ((is_top_maketop b (Q j) X) c c_in hcb),
    rwa ← Q'top j hj,
    simp only [is_bot, not_forall], 
    exact ⟨c, c_in, hcb, H'⟩ },
  { exact absurd (i_piv.2.2.2.1 c c_in hcb).1 H.2 },
  { convert is_top_maketop b (Q j) X c c_in hcb,
    exact Q'top j hj (λ hbot, H.2 (hbot c c_in hcb).1) },
  { apply absurd (makeabove_below hcb h).1,
    convert ← H.2 },
  { by_contra H',
    apply absurd (is_bot_makebot b (Q j) X c c_in hcb).1,
    convert ← H.2,
    refine Q'bot j hj ((i_piv.2.1 j).is_bot _),
    simp only [is_top, not_forall],
    exact ⟨c, c_in, hcb, H'⟩ }, 
  { convert makeabove_above (Q j) hab },
  { convert is_top_maketop b (Q j) X a a_in hab,
    apply Q'top j hj,
    rw i_piv.1 j hj a b a_in b_in,
    simp only [is_bot, not_forall],
    exact ⟨a, a_in, hab, nP_of_reverseP H⟩ },
  { exact i_piv.2.2.2.2.1 a a_in hab },
  { rw ← i_piv.1 j hj a b a_in b_in,
    refine ((i_piv.2.1 j).is_top (λ hbot, nP_of_reverseP H _)) a a_in hab,
    convert is_bot_makebot b (Q j) X a a_in hab,
    exact Q'bot j hj hbot },
  { exact absurd (i_piv.2.2.2.2.1 a a_in hab).1 H.2 },
  { convert is_bot_makebot b (Q j) X a a_in hab,
    apply Q'bot j hj,
    rw i_piv.1 j hj a b a_in b_in,
    apply (i_piv.2.2.1 j).is_bot,
    simp only [is_top, not_forall],
    exact ⟨a, a_in, hab, nP_of_reverseP H⟩ },
  { apply absurd (makeabove_above (Q j) hab).1,
    convert ← H.2 },
  { rw ← i_piv.1 j hj a b a_in b_in,
    suffices : is_bot b (R j) X, from this a a_in hab,
    by_contra hbot,
    apply absurd (is_top_maketop b (Q j) X a a_in hab).1,
    convert ← H.2,
    exact Q'top j hj hbot },
end


/- Step 4 states that if an individual is a dictator over every pair of social states 
except for `b`, they are also a dictator over all pairs (including `b`). -/
lemma fourth_step (hind : ind_of_irr_alts f X) 
  (hX : 3 ≤ X.card) (hpiv : ∀ b ∈ X, has_pivot f X b) : 
  is_dictatorship f X := 
begin
  obtain ⟨b, hb⟩ := (card_pos.1 (zero_lt_two.trans hX)).bex,
  obtain ⟨i, i_piv⟩ := hpiv b hb,
  have h : ∀ a ∈ X, a ≠ b → ∀ Rᵢ : ι → pref_order σ, 
          (P (Rᵢ i) a b → P (f Rᵢ) a b) ∧ (P (Rᵢ i) b a → P (f Rᵢ) b a), -- is there perhaps a better way to state this? -Ben
  { intros a a_in hab Rᵢ,
    obtain ⟨c, hc, hca, hcb⟩ := exists_third_distinct_mem hX a_in hb hab,
    obtain ⟨hac, hbc⟩ := ⟨hca.symm, hcb.symm⟩,
    obtain ⟨j, j_piv⟩ := hpiv c hc,
    obtain hdict := third_step hind hc j_piv, 
    obtain rfl : j = i,
    { by_contra hji,
      obtain ⟨R, R', hso, hextr, -, -, -, hbot, htop⟩ := i_piv,
      refine (htop a a_in hab).2 (hdict b a hb a_in hbc hac R' _).1,
      rw ← hso j hji a b a_in hb,
      by_contra hnot,
      refine (hdict a b a_in hb hac hbc R ((hextr j).is_top _ a a_in hab)).2 (hbot a a_in hab).1,
      simp only [is_bot, not_forall], 
      exact ⟨a, a_in, hab, hnot⟩ }, 
    split; apply hdict; assumption },
  refine ⟨i, λ x y hx hy Rᵢ hRᵢ, _⟩,
  rcases @eq_or_ne _ b x with rfl | hbx; rcases @eq_or_ne _ b y with rfl | hby,
  { exact (false_of_P_self hRᵢ).elim },
  { exact (h y hy hby.symm Rᵢ).2 hRᵢ },
  { exact (h x hx hbx.symm Rᵢ).1 hRᵢ },
  { exact third_step hind hb i_piv y x hy hx hby.symm hbx.symm Rᵢ hRᵢ },
end 

/-- Arrow's Impossibility Theorem: Any social welfare function involving at least three social
  states that satisfies WP and IoIA is necessarily a dictatorship. --/
theorem arrow [fintype ι] (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) :
  is_dictatorship f X := 
fourth_step hind hX $ second_step hwp hind hX
