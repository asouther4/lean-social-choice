import data.real.basic

--we think of social states as type σ and inidividuals as type ι
variables {σ ι : Type}

def weak_pareto (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) (N : finset ι) : Prop 
    := ∀ (x y ∈ X) (P : ι → σ → ℝ), (∀ i ∈ N, P i x < P i y) → (f P) x < (f P) y

def ind_of_irr_alts (f : (ι → σ → ℝ) → σ → ℝ) (X : finset σ) (N : finset ι) : Prop := 
    ∀ (x y ∈ X) (P P' : ι → σ → ℝ), 
    ( ∀ i ∈ N, P i x < P i y ↔ P' i x < P' i y) →
    ( ∀ i ∈ N, f P x < f P y ↔ f P' x < f P y)


/- a social state is extremal with respect to a relation and a set of individuals
if every individual ranks that social state either highest or lowest -/
def is_extremal (P : σ → ℝ) (X : finset σ) (s : σ) : Prop := 
    s ∈ X ∧ ((∀ t ∈ X, t ≠ s → P s < P t) ∨ (∀ t ∈ X,  t ≠ s → P t < P s))


--what it means for social states to have the "same order" with respect to two relations
def same_order (p p': σ → ℝ) (x y x' y' : σ) : Prop :=
    ((p x < p y ↔ p' x' < p' y') ∧ (p y < p x ↔ p' y' < p' x'))

def is_pivotal  (f : (ι → σ → ℝ) → (σ → ℝ)) (N : finset ι) (X : finset σ) 
    (i : ι) (b : σ) : Prop := 
    ∃ (P P' : ι → σ → ℝ),
    ( ∀ j ∈ N, j ≠ i → ∀ x y ∈ X, same_order (P j) (P' j) x y x y) ∧ 
    ( ∀ i ∈ N,  is_extremal (P i) X b ) ∧ 
    ( ∀ i ∈ N,  is_extremal (P' i) X b ) ∧
    ( ∀ a ∈ X, a ≠ b → P i b < P i a ) ∧
    ( ∀ a ∈ X, a ≠ b → P i a < P i b  ) ∧
    ( ∀ a ∈ X, a ≠ b → f P b < f P a  ) ∧
    ( ∀ a ∈ X, a ≠ b → f P a < f P b  )

def is_dictator_except (f : (ι → σ → ℝ) → (σ → ℝ))
    (N : finset ι) (X : finset σ) (i : ι) (b : σ) : Prop := 
    ∀ a ∈ X, ∀ c ∈ X, a ≠ b → c ≠ b → 
    ∀ P : ι → σ → ℝ, P i a < P i c → f P a < f P c


variables {i : ι} {b : σ} {u : ι → σ → ℝ }
open classical

def u' : ι → σ → ℝ := λ j x,
    if hj : j = i then (if hx : x = b then 9999 else u j x)
    else u j x


variables {X : finset σ} {N : finset ι}

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
    classical,
    let Q' : ι → σ → ℝ := λ j x,  
      if hx : x = b then (if hj : j = i then (Q i a + Q i b)/2 else 999)
      else Q j x,
    sorry,  
end
