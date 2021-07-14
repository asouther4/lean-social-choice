import basic

open relation vector finset

/-! ### Definition of a preference ordering -/

structure pref_order (α : Type*) := 
(rel : α → α → Prop)
(refl : reflexive rel)
(total : total rel)
(trans : transitive rel)

instance (α : Type*) : has_coe_to_fun (pref_order α) := ⟨_, λ r, r.rel⟩

lemma pref_order.eq_coe {α : Type*} (r : pref_order α) : r.rel = r := rfl

lemma pref_order.reverse {α : Type*} {r : pref_order α} {a b : α} (h : ¬r a b) : r b a :=
(r.total a b).resolve_left h

-- We think of social states as type `σ` and inidividuals as type `ι`
variables {σ ι : Type} {x y x' y' a b : σ} {r r' : σ → σ → Prop} {X : finset σ}

/-! ### Some basic definitions and lemmas 
    NOTE: Eventually we should probably move most of these to the basic file -/

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

lemma nonempty_of_mem {s : finset σ} {a : σ} (ha : a ∈ s) : s.nonempty := 
nonempty_of_ne_empty $ ne_empty_of_mem ha

/- Alternate defintion of `same_order`. Can be interchanged with the original, as 
the lemma below shows. -/
def same_order' (r r' : σ → σ → Prop) (s₁ s₂ s₃ s₄ : σ) : Prop :=
(P r s₂ s₁ ↔ P r' s₄ s₃) ∧ (P r s₁ s₂ ↔ P r' s₃ s₄)

lemma P_iff_of_iff (h₁ : r a b ↔ r' a b) (h₂ : r b a ↔ r' b a) : 
  (P r a b ↔ P r' a b) ∧ (P r b a ↔ P r' b a) :=
by simp_rw [P, h₁, h₂, iff_self, and_self]

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

lemma is_top.not_bot (htop : is_top b r X) (h : ∃ a ∈ X, a ≠ b) : ¬is_bot b r X :=
begin
  simp only [is_bot, not_forall, not_lt, exists_prop],
  rcases h with ⟨a, a_in, hab⟩,
  exact ⟨a, a_in, hab, nP_of_reverseP (htop a a_in hab)⟩,
end

lemma is_top.not_bot' (htop : is_top b r X) (hX : 2 ≤ X.card) (hb : b ∈ X) : ¬is_bot b r X :=
htop.not_bot $ exists_second_distinct_mem hX hb

lemma is_bot.not_top (hbot : is_bot b r X) (h : ∃ a ∈ X, a ≠ b) : ¬is_top b r X :=
begin
  simp only [is_top, not_forall, not_lt, exists_prop],
  rcases h with ⟨a, a_in, hab⟩,
  exact ⟨a, a_in, hab, nP_of_reverseP (hbot a a_in hab)⟩,
end

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
  ((makeabove r a b) c d ↔ r c d) ∧ ((makeabove r a b) d c ↔ r d c) :=
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

lemma makeabove_below {a b c : σ} {r : pref_order σ} (hc : c ≠ b) (hr : ¬r a c) :
  P (makeabove r a b) c b :=
by simpa [P, makeabove, ← pref_order.eq_coe, not_or_distrib, hc]

/-! ### Properties -/

def weak_pareto (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop := 
∀ (x y ∈ X) (R : ι → pref_order σ), (∀ i : ι, P (R i) x y) → P (f R) x y

def ind_of_irr_alts (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop :=
∀ (R R' : ι → pref_order σ) (x y ∈ X), 
  (∀ i : ι, same_order' (R i) (R' i) x y x y) → same_order' (f R) (f R') x y x y

def is_dictatorship (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) : Prop :=
∃ i : ι, ∀ (x y ∈ X) (R : ι → pref_order σ), P (R i) x y → P (f R) x y

def is_pivotal (f : (ι → pref_order σ) → pref_order σ) (X : finset σ) (i : ι) (b : σ) : Prop :=
∃ (R R' : ι → pref_order σ),
  (∀ j : ι, j ≠ i → ∀ x y ∈ X, R j = R' j) ∧ 
    (∀ i : ι, is_extremal b (R i) X) ∧ (∀ i : ι, is_extremal b (R' i) X) ∧
      (is_bot b (R i) X) ∧ (is_top b (R' i) X) ∧ 
        (is_bot b (f R) X) ∧ (is_top b (f R') X)

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
theorem is_bot_of_forall_is_bot (f : (ι → pref_order σ) → pref_order σ)
  (b : σ) (X: finset σ)
  (b_in : b ∈ X) (hwp : weak_pareto f X) 
  (hbot : ∀ i, is_bot b (R i) X) :
  is_bot b (f R) X :=
λ a a_in hab, hwp a b a_in b_in R $ λ i, hbot i a a_in hab

lemma exists_of_not_extremal (hX : 3 ≤ X.card) (hb : b ∈ X) (h : ¬ is_extremal b (f R) X):
  ∃ a c ∈ X, a ≠ b ∧ c ≠ b ∧ a ≠ c ∧ f R a b ∧ f R b c := 
begin
  sorry,
end

/-! ### The Proof Begins -/

lemma first_step {R : ι → pref_order σ}
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 3 ≤ X.card) (b_in : b ∈ X) (hextr : ∀ i, is_extremal b (R i) X) :
  is_extremal b (f R) X :=
begin
  classical,
  by_contra hnot,
  obtain ⟨a, c, a_in, c_in, hab, hcb, hac, hfa, hfb⟩ := exists_of_not_extremal hX b_in hnot,
  let R' := λ j, makeabove (R j) a c,
  have hfR'ab : f R' a b,
  { sorry, },
  sorry, 
end

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

/-- We define relation `r₂`, a `pref_order` we will use in `second_step`. -/
def r₂ (b : σ) : pref_order σ :=
begin
  use λ x y, if y = b then true else if x = b then false else true,
  { intro x, split_ifs; trivial },
  { intros x y, simp only, split_ifs; simp only [true_or, or_true] },
  { intros x y z, simp only, split_ifs; simp only [forall_true_left, forall_false_left] },
end

lemma second_step_aux [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
  (hX : 2 < X.card) (b_in : b ∈ X) {D' : finset ι} :
  ∀ {R : ι → pref_order σ}, D' = {i ∈ univ | is_bot b (R i) X} → 
    (∀ i, is_extremal b (R i) X) → is_bot b (f R) X → has_pivot f X b := 
begin
  refine finset.induction_on D'
    (λ R h hextr hbot, absurd (is_top_of_forall_is_top b_in hwp (λ j, (hextr j).is_top _))
                              (hbot.not_top (exists_second_distinct_mem hX.le b_in))) 
    (λ i D hi IH R h_insert hextr hbot, _),
  { simpa using eq_empty_iff_forall_not_mem.mp h.symm j },
  { have hX' := nonempty_of_mem b_in,
    let R' := λ j, (ite (j = i) (maketop (R j) b) (R j)),
    have hextr' : ∀ j, is_extremal b (R' j) X,
    { intro j, simp only [R'], 
      split_ifs,
      { exact is_top.is_extremal (λ a ha hab, is_top_maketop b (R j) X a ha hab) },
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

lemma second_step [fintype ι]
  (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) 
  (hX : 3 ≤ X.card) (b) (b_in : b ∈ X) :
  has_pivot f X b := 
have hbot : is_bot b (r₂ b) X, by simp [is_bot, r₂, P, ←pref_order.eq_coe],
second_step_aux hwp hind hX b_in rfl (λ i, hbot.is_extremal) $
  is_bot_of_forall_is_bot f b X b_in hwp $ λ i, hbot

lemma third_step (hind : ind_of_irr_alts f X) 
  (b_in : b ∈ X) {i : ι} (i_piv : is_pivotal f X i b) :
  is_dictator_except f X i b :=
begin
  intros a c a_in c_in a_neq_b c_neq_b Q hyp,
  obtain ⟨R, R', i_piv⟩ := i_piv,
  have X_ne := nonempty_of_ne_empty (ne_empty_of_mem b_in),
  let Q' : ι → pref_order σ:= λ j, 
    if j = i 
      then makeabove (Q j) a b
    else 
      if is_bot b (R j) X
        then makebot (Q j) b
      else maketop (Q j) b,
  have Q'_iff : ∀ j, ∀ d ≠ b, ∀ e ≠ b, 
    (P (Q j) d e ↔ P (Q' j) d e) ∧ (P (Q j) e d ↔ P (Q' j) e d),
  { intros j d d_neq_b e e_neq_b,
    by_cases hj : j = i,
    { simp only [Q', if_pos hj, 
        makeabove_noteq' (Q j) a d_neq_b e_neq_b, 
          and_self, iff_self], },
    { simp [Q', if_neg hj],
      by_cases hbot : is_bot b (R j) X,
      { simp [if_pos hbot, makebot_noteq' (Q j) d_neq_b e_neq_b, 
          iff_self, and_self], },
      { simp only [if_neg hbot, maketop_noteq' (Q j) d_neq_b e_neq_b, 
          iff_self, and_self], }, }, },
  have hQ'bc : ∀ j, (P (R j) c b ↔ P (Q' j) c b) ∧ (P (R j) b c ↔ P (Q' j) b c),
  { refine (λ j, ⟨⟨λ hP, _, λ hQ', _⟩, ⟨λ hP, _, λ hQ', _⟩⟩ ); by_cases hj : j = i,
    { simp [Q', if_pos hj],
      rw ← hj at hyp,
      exact makeabove_below c_neq_b hyp.2, },  
    { simp [Q', if_neg hj],
      have b_bot : is_bot b (R j) X,
      { unfold is_bot,
        by_contradiction b_bot, push_neg at b_bot,
        rcases b_bot with ⟨d, d_in, d_neq_b, hd⟩,
        cases i_piv.2.1 j,
        { exact hd (h d d_in d_neq_b), },
        { exact hP.2 (h c c_in c_neq_b).1, }, },
      rw if_pos b_bot,
      exact (is_bot_makebot b (Q j) X) c c_in c_neq_b, },
    { convert i_piv.2.2.2.1 c c_in c_neq_b, }, 
    { by_contradiction hP,
      have not_bot : ¬ is_bot b (R j) X := by simp only 
        [is_bot, exists_prop, ne.def, not_forall];
          exact ⟨c, c_in, c_neq_b, hP⟩,
      apply nP_of_reverseP ((is_top_maketop b (Q j) X) c c_in c_neq_b),
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
      exact is_top_maketop b (Q j) X c c_in c_neq_b, },
    { exfalso,
      simp only at hQ',
      simp [Q', if_pos hj] at hQ',
      rw hj at hQ',
      exact hQ'.2 (makeabove_below c_neq_b hyp.2).1, },
    { by_contradiction hR,
      have b_bot : is_bot b (R j) X,
      { refine is_extremal.is_bot (i_piv.2.1 j) _,
        simp only [is_top, exists_prop, ne.def, not_forall],
        exact ⟨c, c_in, c_neq_b, hR⟩, },
      simp only at hQ',
      simp only [Q', if_neg hj, if_pos b_bot] at hQ',
      exact hQ'.2 (is_bot_makebot b (Q j) X c c_in c_neq_b).1, }, }, 
  have hQ'ab : ∀ j, (P (R' j) b a ↔ P (Q' j) b a) ∧ (P (R' j) a b ↔ P (Q' j) a b),
  { refine (λ j, ⟨⟨λ hP', _, λ hQ', _⟩, ⟨λ hP', _, λ hQ', _⟩ ⟩); by_cases hj : j = i,
    { simp [Q'],
      rw if_pos hj,
      rw ← hj at hyp,
      have := makeabove_above (Q j),
      exact (this a_neq_b), },
    { simp [Q'],
      have not_bot : ¬ is_bot b (R j) X,
      { rw (i_piv.1 j hj a b a_in b_in),
        simp only [is_bot, exists_prop, ne.def, not_forall],
        exact ⟨a, a_in, a_neq_b,  nP_of_reverseP hP'⟩, },
      rw [if_neg hj, if_neg not_bot],
      exact (is_top_maketop b (Q j) X) a a_in a_neq_b, },
    { convert i_piv.2.2.2.2.1 a a_in a_neq_b, },
    { simp only at hQ', 
      simp only [Q', dite_eq_ite, if_neg hj] at hQ',
      have not_bot : ¬ (is_bot b (R j) X),
      { by_contradiction b_bot, 
        rw if_pos b_bot at hQ',
        apply (nP_of_reverseP hQ'),
        exact (is_bot_makebot b (Q j) X) a a_in a_neq_b, },
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
        exact is_bot_makebot b (Q j) X a a_in a_neq_b, },
      { exfalso,
        simp only at hQ',
        simp only [Q', dite_eq_ite, if_pos hj] at hQ',
        exact hQ'.2 (makeabove_above (Q j) a_neq_b).1, },
      { simp only at hQ', 
        simp only [Q', dite_eq_ite, if_neg hj] at hQ',
        have b_bot : (is_bot b (R j) X),
        { by_contradiction b_bot, 
          rw if_neg b_bot at hQ',
          exact hQ'.2 (is_top_maketop b (Q j) X a a_in a_neq_b).1,},
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
  exact P_trans (f Q').trans h₂ h₁,
end

lemma fourth_step (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) (h : ∀ b ∈ X, has_pivot f X b) : 
  is_dictatorship f X := 
begin
  have X_pos : 0 < card X := by linarith,
  obtain ⟨b, b_in⟩ := (card_pos.1 X_pos).bex,
  obtain ⟨i, i_piv⟩ := h b b_in,
  have h : ∀ a ∈ X, a ≠ b → ∀ Rᵢ : ι → pref_order σ, 
          (P (Rᵢ i) a b → P (f Rᵢ) a b) ∧ (P (Rᵢ i) b a → P (f Rᵢ) b a),
  { intros a a_in hab Rᵢ,
    obtain ⟨c, c_in, hca, hcb⟩ := exists_third_distinct_mem hX a_in b_in hab,
    obtain ⟨hac, hbc⟩ := ⟨hca.symm, hcb.symm⟩,
    obtain ⟨j, j_piv⟩ := h c c_in,
    have hdict := third_step hind c_in j_piv, 
    obtain rfl : j = i,
    { by_contra hji,
      obtain ⟨R, R', hso, hextr, -, -, -, hbot, htop⟩ := i_piv,
      have h₁ := hdict b a b_in a_in hbc hac R',
      have h₂ := (hextr j).is_top,
      rw ← (hso j hji a b a_in b_in) at h₁,
      refine (htop a a_in hab).2 (h₁ _).1,
      by_contra hnot,
      simp only [is_top, is_bot, and_imp, exists_imp_distrib, not_forall] at h₂,
      exact (hdict a b a_in b_in hac hbc R (h₂ a a_in hab hnot a a_in hab)).2 
        (hbot a a_in hab).1, }, 
    split; apply hdict; assumption, },
  refine ⟨i, λ x y hx hy Rᵢ hRᵢ, _⟩,
  rcases @eq_or_ne _ b x with rfl | hbx; rcases @eq_or_ne _ b y with rfl | hby,
  { exact (false_of_P_self hRᵢ).elim, },
  { exact (h y hy hby.symm Rᵢ).2 hRᵢ, },
  { exact (h x hx hbx.symm Rᵢ).1 hRᵢ, },
  { exact third_step hind b_in i_piv y x hy hx hby.symm hbx.symm Rᵢ hRᵢ, },
end 

/-- Arrow's Impossibility Theorem: Any social welfare function involving at least three social
  states that satisfies WP and IoIA is necessarily a dictatorship. --/
theorem arrow [fintype ι] (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) :
  is_dictatorship f X := 
fourth_step hind hX $ second_step hwp hind hX
