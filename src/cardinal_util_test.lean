import data.real.basic
import data.finset.lattice 

open finset

--we think of social states as type σ and inidividuals as type ι
variables {σ ι : Type} [decidable_eq σ] [decidable_eq ι]

-- Important Definitions -- 

def weak_pareto (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) (N : finset ι) : Prop := 
∀ (x ∈ X) (y ∈ X) (P : ι → σ → ℝ), (∀ i ∈ N, P i x < P i y) → (f P) x < (f P) y

def ind_of_irr_alts (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) (N : finset ι) : Prop := 
∀ (x ∈ X) (y ∈ X) (P P' : ι → σ → ℝ), 
  (∀ i ∈ N, P i x < P i y ↔ P' i x < P' i y) →
    (f P x < f P y ↔ f P' x < f P' y)

def is_dictatorship (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) (N : finset ι) : Prop :=
∃ i ∈ N, ∀ (x y ∈ X) (P : ι → σ → ℝ), P i x < P i y → f P x < f P y

def is_bot_of (b : σ) (p : σ → ℝ) (X : finset σ) : Prop :=
∀ a ∈ X, a ≠ b → p b < p a

def is_top_of (b : σ) (p : σ → ℝ) (X : finset σ): Prop := 
∀ a ∈ X, a ≠ b → p a < p b

def is_extremal (b : σ) (p : σ → ℝ) (X : finset σ) : Prop := 
is_bot_of b p X ∨ is_top_of b p X

def same_order (p p' : σ → ℝ) (x y x' y' : σ) : Prop :=
((p x < p y ↔ p' x' < p' y') ∧ (p y < p x ↔ p' y' < p' x'))

def is_pivotal (f : (ι → σ → ℝ) → (σ → ℝ)) (N : finset ι) (X : finset σ) 
  (i : ι) (b : σ) : Prop := 
∃ (P P' : ι → σ → ℝ),
  (∀ j ∈ N, j ≠ i → ∀ x y ∈ X, same_order (P j) (P' j) x y x y) ∧ 
    (∀ i ∈ N, is_extremal b (P i) X) ∧ (∀ i ∈ N, is_extremal b (P' i) X) ∧
      (is_bot_of b (P i) X) ∧ (is_top_of b (P' i) X) ∧ (is_bot_of b (f P) X) ∧ (is_top_of b (f P') X)

def is_dictator_except (f : (ι → σ → ℝ) → (σ → ℝ))
  (N : finset ι) (X : finset σ) (i : ι) (b : σ) : Prop := 
∀ a ∈ X, ∀ c ∈ X, a ≠ b → c ≠ b → 
    ∀ P : ι → σ → ℝ, P i a < P i c → f P a < f P c

open classical

noncomputable def maketop (p : σ → ℝ) (b : σ) (X : finset σ) (h : X.nonempty): σ → ℝ :=
function.update p b (((X.image p).max' (finset.nonempty.image h p))+1)

noncomputable def makebot (p : σ → ℝ) (b : σ) (X : finset σ) (h : X.nonempty): σ → ℝ :=
function.update p b (((X.image p).min' (finset.nonempty.image h p))-1)

noncomputable def makebetween (p : σ → ℝ) (a b c : σ) : σ → ℝ :=
function.update p b ((p a + p c)/2)


---- Preliminary Lemmas ----

lemma maketop_noteq (a b : σ) (ha : a ≠ b) (p : σ → ℝ) (X : finset σ) (hX : X.nonempty) :
  (maketop p b X hX) a = p a := 
function.update_noteq ha _ p

lemma makebot_noteq (a b : σ) (ha : a ≠ b) (p : σ → ℝ) (X : finset σ) (hX : X.nonempty) :
(makebot p b X hX) a = p a := function.update_noteq ha _ p

lemma makebetween_noteq (a b c d: σ) (hd : d ≠ b) (p : σ → ℝ) (X : finset σ) (hX : X.nonempty) :
  (makebetween p a b c) d = p d :=
function.update_noteq hd ((p a + p c) / 2) p

lemma makebetween_eq (a b c : σ) (p : σ → ℝ) (X : finset σ) (hX : X.nonempty) :
  (makebetween p a b c) b = (p a + p c) / 2 :=
function.update_same _ _ _

lemma lt_of_maketop (a b : σ) (p : σ → ℝ) (a_neq : a ≠ b) (X : finset σ) (hX : X.nonempty) 
  (a_in : a ∈ X) : 
  (maketop p b X hX) a < (maketop p b X hX) b :=
begin
  unfold maketop,
  rw function.update_noteq a_neq _ p,
  simp only [function.update_same],
  have := finset.le_max' (finset.image p X) (p a) (finset.mem_image_of_mem p a_in),
  exact this.trans_lt (lt_add_one _),
end

lemma lt_of_makebot (b c : σ) (p : σ → ℝ) (c_neq : c ≠ b) (X : finset σ) (hX : X.nonempty)
  (c_in : c ∈ X) : 
  (makebot p b X hX) b < (makebot p b X hX) c :=
begin
  unfold makebot,
  rw function.update_noteq c_neq _ p,
  simp only [function.update_same],
  have := finset.min'_le (finset.image p X) (p c) (finset.mem_image_of_mem p c_in),
  exact sub_lt_iff_lt_add'.mpr (this.trans_lt (lt_one_add _)),
end

lemma lt_top_of_makebetween (a b c : σ) (p : σ → ℝ) (c_neq : c ≠ b) (X : finset σ) (hX : X.nonempty) 
  (hc : p a < p c) : 
  (makebetween p a b c) b < (makebetween p a b c) c :=
begin
  unfold makebetween,
  simp only [function.update_same],
  rw function.update_noteq c_neq ((p a + p c) / 2) p,
  linarith,
end

lemma bot_lt_of_makebetween (a b c : σ) (p : σ → ℝ) (a_neq : a ≠ b ) (X : finset σ) (hX : X.nonempty)
  (ha : p a < p c) : 
  (makebetween p a b c) a < (makebetween p a b c) b :=
begin
  unfold makebetween,
  simp only [function.update_same],
  rw function.update_noteq a_neq ((p a + p c) / 2) p,
  linarith,
end

lemma top_of_not_bot_of_extr {b : σ} {p : σ → ℝ} {X : finset σ} 
  (extr : is_extremal b p X) (not_bot : ¬ is_bot_of b p X) :
  is_top_of b p X := 
extr.resolve_left not_bot 

lemma bot_of_not_top_of_extr {b : σ} {p : σ → ℝ} {X : finset σ} 
  (extr : is_extremal b p X) (not_top : ¬ is_top_of b p X) :
  is_bot_of b p X := 
extr.resolve_right not_top 

lemma third_distinct_mem {X : finset σ} {a b : σ}
  (hX : 3 ≤ finset.card X) (a_in : a ∈ X) (b_in : b ∈ X) (h : a ≠ b) : 
  ∃ c ∈ X, c ≠ a ∧ c ≠ b :=
begin
  have hpos : 0 < ((X.erase b).erase a).card,
  { simpa only [card_erase_of_mem, mem_erase_of_ne_of_mem h a_in, b_in]
      using nat.pred_le_pred (nat.pred_le_pred hX) }, 
  cases card_pos.mp hpos with c hc,
  simp_rw mem_erase at hc,
  exact ⟨c, hc.2.2, hc.1, hc.2.1⟩,
end


---- The Proof --------


variables {X : finset σ} {N : finset ι}

lemma first_step {f : (ι → σ → ℝ) → (σ → ℝ)}
  (hf : weak_pareto f X N ∧ ind_of_irr_alts f X N)
  (hX : finset.card X ≥ 3)
  (b : σ) (b_in : b ∈ X) (P : ι → σ → ℝ)
  (hyp : ∀ i ∈ N, is_extremal b (P i) X) :
  is_extremal b (f P) X := 
begin
  have X_ne : X.nonempty := finset.card_pos.1 (by linarith),
  by_contradiction hnot,
  simp only [is_extremal, is_bot_of, is_top_of] at hnot,
  push_neg at hnot,
  have : ∃ a : σ, ∃ c : σ, a ∈ X ∧ c ∈ X ∧
         a ≠ b ∧ c ≠ b ∧ a ≠ c ∧ f P b ≤ f P a ∧ f P c ≤ f P b,
  { rcases hnot with ⟨⟨c, c_in, c_neq_b, hc⟩, ⟨a, a_in, a_neq_b, ha⟩⟩,
    by_cases a_neq_c : a ≠ c,
    { use a, use c,
      exact ⟨a_in, c_in, a_neq_b, c_neq_b, a_neq_c, ha, hc⟩, },
    { push_neg at a_neq_c,
      obtain ⟨d, d_in, d_neq_a, d_neq_b⟩ := third_distinct_mem hX a_in b_in a_neq_b,
      by_cases hd : f P b < f P d,
      { use d, use c,
        rw a_neq_c at d_neq_a,
        exact ⟨d_in, c_in, d_neq_b, c_neq_b, d_neq_a, (by linarith), hc⟩, },
      { push_neg at hd,
        use a, use d,
        exact ⟨a_in, d_in, a_neq_b, d_neq_b, d_neq_a.symm, ha, hd⟩, }, }, }, 
  classical,
  rcases this with ⟨a, c, a_in, c_in, a_neq_b, c_neq_b, a_neq_c, ha, hc ⟩,
  let Q : ι → σ → ℝ := λ j, (makebetween (P j) a c b),
  let R : ι → σ → ℝ := λ j, function.update (P j) c (P j a + 1),
  let P₂ : ι → σ → ℝ := λ j,
    if is_top_of b (P j) X then (Q j) else (R j),
  have hP₂ac : ∀ i ∈ N, P₂ i a < P₂ i c,
  { intros i i_in,
    by_cases b_top : is_top_of b (P i) X,
    { simp [P₂],
      rw if_pos b_top,
      simp [Q],
      specialize b_top a a_in a_neq_b,
      exact bot_lt_of_makebetween a c b (P i) a_neq_c X X_ne b_top, },
    { simp [P₂],
      rw if_neg b_top,
      simp [R],
      rw function.update_noteq a_neq_c (P i a + 1),
      linarith, }, },
  have hPab : ∀ i ∈ N, P i a < P i b ↔ P₂ i a < P₂ i b,
  { intros i i_in,
    split,
    { intro hP,
      simp [P₂],
      by_cases b_top : is_top_of b (P i) X,
      { rw if_pos b_top, 
        simp [Q],
        rw [makebetween_noteq a c b a a_neq_c (P i) X X_ne,
            makebetween_noteq a c b b c_neq_b.symm (P i) X X_ne],
        exact hP, },
      { rw if_neg b_top,
        simp [R],
        rw [function.update_noteq a_neq_c (P i a + 1) (P i),
            function.update_noteq c_neq_b.symm (P i a + 1) (P i)],
        exact hP, }, },
    { intro hP₂,
      by_contradiction hP,
      have not_top : ¬ is_top_of b (P i) X,
      { by_contradiction b_top,
        exact hP (b_top a a_in a_neq_b), },
      simp [P₂] at hP₂,
      rw if_neg not_top at hP₂,
      simp [R] at hP₂,
      rw [function.update_noteq a_neq_c (P i a + 1) (P i),
            function.update_noteq c_neq_b.symm (P i a + 1) (P i)] at hP₂,
      exact hP hP₂, }, },
  have hPbc : ∀ i ∈ N, P i b < P i c ↔ P₂ i b < P₂ i c, 
  { intros i i_in,
    split,
    { intro hP, 
      have not_top : ¬ is_top_of b (P i) X,
      { by_contradiction b_top,
        linarith [b_top c c_in c_neq_b], },
      simp [P₂],
      rw if_neg not_top,
      have b_bot : is_bot_of b (P i) X := bot_of_not_top_of_extr (hyp i i_in) not_top,
      simp [R],
      rw function.update_noteq c_neq_b.symm (P i a + 1) (P i),
      linarith [b_bot a a_in a_neq_b], },
    { intro hP₂,
      by_contradiction hP,
      have b_top : is_top_of b (P i) X,
      { refine top_of_not_bot_of_extr (hyp i i_in) _,
        intro b_bot,
        exact hP (b_bot c c_in c_neq_b), },
      simp [P₂] at hP₂,
      rw if_pos b_top at hP₂,
      simp [Q] at hP₂,
      rw [makebetween_noteq a c b b c_neq_b.symm (P i) X X_ne,
          makebetween_eq a c b (P i) X X_ne] at hP₂,
      linarith [b_top a a_in a_neq_b], }, },
  have h_iir₁ := (not_congr (hf.2 a a_in b b_in P P₂ hPab)).mp (not_lt.mpr ha),
  have h_iir₂ := (not_congr (hf.2 b b_in c c_in P P₂ hPbc)).mp (not_lt.mpr hc),
  have h_pareto := hf.1 a a_in c c_in P₂ hP₂ac,
  linarith [(not_congr (hf.2 a a_in b b_in P P₂ hPab)).mp (not_lt.mpr ha),
            (not_congr (hf.2 b b_in c c_in P P₂ hPbc)).mp (not_lt.mpr hc),
            hf.1 a a_in c c_in P₂ hP₂ac],
end      


lemma second_step {f : (ι → σ → ℝ) → (σ → ℝ)}
  (hf : weak_pareto f X N ∧ ind_of_irr_alts f X N)
  (hX : finset.card X ≥ 3)
  (hN : finset.card N ≥ 2) :
  ∀ b ∈ X, ∃ n' ∈ N, is_pivotal f N X n' b := 
begin
  sorry,
end


lemma third_step {f : (ι → σ → ℝ) → (σ → ℝ)}
  (hf : weak_pareto f X N ∧ ind_of_irr_alts f X N)
  (hX : finset.card X ≥ 3)
  (hN : finset.card N ≥ 2) :
  ∀ b ∈ X, ∀ i ∈ N, is_pivotal f N X i b →
  is_dictator_except f N X i b :=
begin
  intros b b_in i i_in i_piv,
  rcases i_piv with ⟨P, P', i_piv⟩,
  intros a a_in c c_in a_neq_b c_neq_b Q hyp,
  have X_ne : X.nonempty := finset.card_pos.1 (by linarith),
  classical,
  let R : ι → σ → ℝ := λ j, (makebetween (Q j) a b c),
  let S : ι → σ → ℝ := λ j, makebot (Q j) b X X_ne,
  let T : ι → σ → ℝ := λ j, maketop (Q j) b X X_ne,
  let Q' : ι → σ → ℝ := λ j,  
    if hx : j = i 
      then (R j)
    else 
      (if is_bot_of b (P j) X 
        then (S j) 
      else (T j)),

  have Q'_eq : ∀ j : ι, ∀ d ≠ b, Q j d = Q' j d,
  { intros j d d_neq,
    by_cases hj : j = i,
    { rw ← makebetween_noteq a b c d d_neq (Q j) X X_ne,
      simp [Q', R],
      rw if_pos hj, },
    { simp [Q'],
      rw if_neg hj,
      by_cases hbot : is_bot_of b (P j) X,
      { rw [← makebot_noteq d b d_neq (Q j) X X_ne, if_pos hbot], },
      { rw [← maketop_noteq d b d_neq (Q j) X X_ne, if_neg hbot], }, }, },
  have hQ'bc : ∀ j ∈ N, P j b < P j c ↔ Q' j b < Q' j c,
  { refine (λ j j_in, ⟨λ hP, _, λ hQ', _⟩); by_cases hj : j = i,
    { simp [Q'],
      rw if_pos hj,
      simp [R],
      rw ← hj at hyp,
      exact lt_top_of_makebetween a b c (Q j) c_neq_b X X_ne hyp, },
    { simp [Q'],
      rw if_neg hj,
      have b_bot : is_bot_of b (P j) X,
      { unfold is_bot_of,
        by_contradiction b_bot, push_neg at b_bot,
        rcases b_bot with ⟨d, d_in, d_neq_b, hd⟩,
        cases i_piv.2.1 j j_in,
        { exact (h d d_in d_neq_b).not_le hd },
        { exact (irrefl _) ((h c c_in c_neq_b).trans hP) }, },
      rw if_pos b_bot,
      exact lt_of_makebot b c (Q j) c_neq_b X X_ne c_in, },
    { convert i_piv.2.2.2.1 c c_in c_neq_b },
      { by_contradiction hP, push_neg at hP,
        have not_bot : ¬ is_bot_of b (P j) X,
        { by_contradiction h,
          unfold is_bot_of at h,
          exact (h c c_in c_neq_b).not_le hP },
        simp only at hQ', simp only [Q', dite_eq_ite, if_neg not_bot, if_neg hj] at hQ',
        linarith [lt_of_maketop c b (Q j) c_neq_b X X_ne c_in], }, },
  have hQ'ab : ∀ j ∈ N, P' j a < P' j b ↔ Q' j a < Q' j b,
  { intros j j_in,
    split,
    { intro hP',
      by_cases hj : j = i,
      { simp [Q'],
        rw if_pos hj,
        rw ← hj at hyp,
        exact bot_lt_of_makebetween a b c (Q j) a_neq_b X X_ne hyp, },
      { simp [Q'],
        rw if_neg hj,
        have not_bot : ¬ is_bot_of b (P j) X,
        { by_contradiction h,
          unfold is_bot_of at h,
          specialize h a a_in a_neq_b,
          rw ← (i_piv.1 j j_in hj a b a_in b_in).1 at hP',
          linarith, },
        rw if_neg not_bot,
        linarith [lt_of_maketop a b (Q j) a_neq_b X X_ne a_in], }, },
    { intro hQ',
      by_cases hj : j = i,
      { rw hj,
        exact i_piv.2.2.2.2.1 a a_in a_neq_b, },
      { simp [Q'] at hQ',
        rw if_neg hj at hQ',
        have not_bot : ¬ (is_bot_of b (P j) X),
        { by_contradiction b_bot, 
          rw if_pos b_bot at hQ',
          linarith [lt_of_makebot b a (Q j) a_neq_b X X_ne a_in], },
        rw if_neg not_bot at hQ',
        rw ← (i_piv.1 j j_in hj a b a_in b_in).1,
        have b_top : is_top_of b (P j) X,
        { refine top_of_not_bot_of_extr _ not_bot,
          exact i_piv.2.1 j j_in, },
        exact b_top a a_in a_neq_b, }, }, },
  have hQQ' : ∀ i ∈ N, Q i a < Q i c ↔ Q' i a < Q' i c,
  { intros i i_in,
    rw [Q'_eq i a a_neq_b, Q'_eq i c c_neq_b], },
  rw hf.2 a a_in c c_in Q Q' hQQ', 
  have h₁ : f Q' a < f Q' b,
  { rw ← (hf.2 a a_in b b_in P' Q' hQ'ab),
    exact i_piv.2.2.2.2.2.2 a a_in a_neq_b, },
  have h₂ : f Q' b < f Q' c,
  { rw ← (hf.2 b b_in c c_in P Q' hQ'bc),
    exact i_piv.2.2.2.2.2.1 c c_in c_neq_b, },
  exact h₁.trans h₂,
end
 
example (a b : ℝ) (h1: a < b) : ¬ b < a := asymm h1
example (p : Prop) (h1 : p) (h2 : ¬ p) : false := h2 h1
example (a : ℝ) : ¬ a < a  := irrefl a

lemma fourth_step {f : (ι → σ → ℝ) → (σ → ℝ)}
    (hf : weak_pareto f X N 
        ∧ ind_of_irr_alts f X N)
    (hX : finset.card X ≥ 3)
    (hN : finset.card N ≥ 2)
  (h : ∀ b ∈ X, ∃ (n' ∈ N), is_pivotal f N X n' b) : 
  is_dictatorship f X N := 
begin
  have X_pos : 0 < finset.card X := by linarith,
  obtain ⟨b, b_in⟩ := (finset.card_pos.1 X_pos).bex,
  obtain ⟨i, i_in, i_piv⟩ := h b b_in,
  have : ∀ a ∈ X, a ≠ b → ∀ Pᵢ : ι → σ → ℝ, 
          (Pᵢ i a < Pᵢ i b → f Pᵢ a < f Pᵢ b) ∧ 
          (Pᵢ i b < Pᵢ i a → f Pᵢ b < f Pᵢ a),
  { intros a a_in ha Pᵢ,
    obtain ⟨c, c_in, not_a, not_b⟩ := third_distinct_mem hX a_in b_in ha,
    obtain ⟨j, j_in, j_piv⟩ := h c c_in,
    have j_dict := third_step hf hX hN c c_in j j_in j_piv, 
    have hij : i = j,
    { by_contra hij,
      rcases i_piv with ⟨R, R', hi₁, hi₂, hi₃, hi₄, hi₅, hi₆, hi₇⟩,
      refine asymm (hi₇ a a_in ha) 
        (j_dict b b_in a a_in (ne_comm.1 not_b) (ne_comm.1 not_a) R' 
          ((hi₁ j j_in (ne_comm.1 hij) a b a_in b_in).2.1 _)),
      by_contra foo,
      have bar := (hi₂ j j_in).resolve_left,
      simp only [is_top_of, is_bot_of, and_imp, 
                 exists_prop, ne, exists_imp_distrib, not_forall] at bar,
      refine asymm (hi₆ a a_in ha) _,
      exact (j_dict a a_in b b_in (ne_comm.1 not_a) 
        (ne_comm.1 not_b) R (bar a a_in ha foo a a_in ha)), },
    rw hij,
    split; refine j_dict _ _ _ _ (ne_comm.1 _) (ne_comm.1 _) Pᵢ; assumption, },
  refine ⟨i, i_in, λ x y x_in y_in Pᵢ hyp, _⟩,
  rcases @eq_or_ne _ b x with (rfl | hx); rcases @eq_or_ne _ b y with (rfl | hy), -- @s will drop when we merge master
  { linarith, },
  { exact (this y y_in hy.symm Pᵢ).2 hyp },
  { exact (this x x_in hx.symm Pᵢ).1 hyp },
  { exact third_step hf hX hN b b_in i i_in i_piv x x_in y y_in hx.symm hy.symm Pᵢ hyp },
end

lemma arrows_theorem {f : (ι → σ → ℝ) → (σ → ℝ)}
  (hf : weak_pareto f X N ∧ ind_of_irr_alts f X N)
  (hX : 3 ≤ card X) 
  (hN : 2 ≤ card N):
  is_dictatorship f X N := 
fourth_step hf hX hN $ second_step hf hX hN