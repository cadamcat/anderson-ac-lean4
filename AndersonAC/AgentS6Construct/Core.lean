import AndersonAC.S6.Definitions

/-! Deterministic state operations for the stopped trial. -/

noncomputable section

open scoped Matrix

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def initialState (core : Finset ι) (M : Matrix ι ι ℝ) (G : Matrix ι ι ℂ)
    (hM : M.IsSymm) : TrialState core where
  active := Finset.univ
  core_active := Finset.subset_univ _
  M := fun i j => M i j
  symmetric := by
    ext i j
    change M (j : ι) (i : ι) = M (i : ι) (j : ι)
    exact congrFun (congrFun hM (i : ι)) (j : ι)
  hatG := G

theorem initialState_active (core : Finset ι) (M : Matrix ι ι ℝ)
    (G : Matrix ι ι ℂ) (hM : M.IsSymm) : (initialState core M G hM).active = Finset.univ := rfl

theorem initialState_entries (core : Finset ι) (M : Matrix ι ι ℝ)
    (G : Matrix ι ι ℂ) (hM : M.IsSymm) : (initialState core M G hM).hatG = G := rfl

def univEquiv : {i : ι // i ∈ (Finset.univ : Finset ι)} ≃ ι where
  toFun := Subtype.val
  invFun i := ⟨i, Finset.mem_univ i⟩
  left_inv i := by ext; rfl
  right_inv _ := rfl

theorem dampedMatrix_submatrix_equiv (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) :
    dampedMatrix (M.submatrix univEquiv univEquiv) t (r ∘ univEquiv) =
      (dampedMatrix M t r).submatrix univEquiv univEquiv := by
  have hmap : (M.submatrix univEquiv univEquiv).map Complex.ofReal =
      (M.map Complex.ofReal).submatrix univEquiv univEquiv := by
    ext i j
    rfl
  have hdiag : Matrix.diagonal (r ∘ univEquiv) =
      (Matrix.diagonal r).submatrix univEquiv univEquiv := by
    ext i j
    simp [Matrix.diagonal, univEquiv]
  rw [dampedMatrix, dampedMatrix, hmap, hdiag]
  ext i j
  rfl

theorem activeInverse_submatrix_equiv (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) :
    activeInverse (M.submatrix univEquiv univEquiv) t (r ∘ univEquiv) =
      (activeInverse M t r).submatrix univEquiv univEquiv := by
  unfold activeInverse
  rw [dampedMatrix_submatrix_equiv, Matrix.inv_submatrix_equiv]

theorem initialState_inverse (core : Finset ι) (M : Matrix ι ι ℝ)
    (G : Matrix ι ι ℂ) (hM : M.IsSymm) (t : ℝ) (r : ι → ℂ)
    (i j : {i // i ∈ (initialState core M G hM).active}) :
    trialInverse t r (initialState core M G hM) i j = activeInverse M t r i j := by
  change activeInverse (M.submatrix univEquiv univEquiv) t (r ∘ univEquiv) i j = _
  rw [activeInverse_submatrix_equiv]
  rfl

def heatMatrix {core : Finset ι} (s : TrialState core) (x : ι)
    (hx : x ∈ s.active) (ξ : ℝ) :
    Matrix {i // i ∈ s.active.erase x} {i // i ∈ s.active.erase x} ℝ :=
  fun i j =>
    s.M ⟨i.1, Finset.mem_of_mem_erase i.2⟩ ⟨j.1, Finset.mem_of_mem_erase j.2⟩ -
      s.M ⟨i.1, Finset.mem_of_mem_erase i.2⟩ ⟨x, hx⟩ *
        s.M ⟨x, hx⟩ ⟨j.1, Finset.mem_of_mem_erase j.2⟩ /
        (s.M ⟨x, hx⟩ ⟨x, hx⟩ + ξ)

theorem heatMatrix_isSymm {core : Finset ι} (s : TrialState core) (x : ι)
    (hx : x ∈ s.active) (ξ : ℝ) :
    (heatMatrix s x hx ξ).IsSymm := by
  ext i j
  simp only [heatMatrix, Matrix.transpose_apply]
  have h_ij : s.M ⟨i.1, Finset.mem_of_mem_erase i.2⟩
      ⟨j.1, Finset.mem_of_mem_erase j.2⟩ =
      s.M ⟨j.1, Finset.mem_of_mem_erase j.2⟩
        ⟨i.1, Finset.mem_of_mem_erase i.2⟩ := by
    have h := congrFun (congrFun s.symmetric
      ⟨i.1, Finset.mem_of_mem_erase i.2⟩) ⟨j.1, Finset.mem_of_mem_erase j.2⟩
    simpa using h.symm
  have h_ix : s.M ⟨i.1, Finset.mem_of_mem_erase i.2⟩ ⟨x, hx⟩ =
      s.M ⟨x, hx⟩ ⟨i.1, Finset.mem_of_mem_erase i.2⟩ := by
    have h := congrFun (congrFun s.symmetric
      ⟨i.1, Finset.mem_of_mem_erase i.2⟩) ⟨x, hx⟩
    simpa using h.symm
  have h_jx : s.M ⟨j.1, Finset.mem_of_mem_erase j.2⟩ ⟨x, hx⟩ =
      s.M ⟨x, hx⟩ ⟨j.1, Finset.mem_of_mem_erase j.2⟩ := by
    have h := congrFun (congrFun s.symmetric
      ⟨j.1, Finset.mem_of_mem_erase j.2⟩) ⟨x, hx⟩
    simpa using h.symm
  rw [h_ij, h_ix, h_jx]
  ring

def heatState {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s : TrialState core)
    (x : ι) (hx : x ∈ s.active) (hxc : x ∉ core) (ξ : ℝ) : TrialState core := by
  let A := s.active.erase x
  let M' := heatMatrix s x hx ξ
  refine {
    active := A
    core_active := ?_
    M := M'
    symmetric := heatMatrix_isSymm s x hx ξ
    hatG := fun i j => s.hatG i j +
      if hi : i ∈ A then if hj : j ∈ A then
        activeInverse M' t (fun y => r y) ⟨i, hi⟩ ⟨j, hj⟩ - s.hatG i j else 0 else 0 }
  intro i hi
  apply Finset.mem_erase.mpr
  constructor
  · intro hEq
    subst i
    exact hxc hi
  · exact s.core_active hi

theorem heatState_transition {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (s : TrialState core) (x : ι) (hx : x ∈ s.active) (hxc : x ∉ core)
    (ξ : ℝ) (hden : s.M ⟨x, hx⟩ ⟨x, hx⟩ + ξ ≠ 0) :
    HeatTransition t r s (heatState t r s x hx hxc ξ) x ξ := by
  refine ⟨hx, hxc, rfl, hden, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i j hi hj
    rfl
  · intro i j
    rfl

theorem heatState_hatG_matches_inverse {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (s : TrialState core) (x : ι) (hx : x ∈ s.active) (hxc : x ∉ core)
    (ξ : ℝ) (i j : {i // i ∈ (heatState t r s x hx hxc ξ).active}) :
    (heatState t r s x hx hxc ξ).hatG i j =
      trialInverse t r (heatState t r s x hx hxc ξ) i j := by
  have hi : ¬(i : ι) = x ∧ (i : ι) ∈ s.active := Finset.mem_erase.mp i.property
  have hj : ¬(j : ι) = x ∧ (j : ι) ∈ s.active := Finset.mem_erase.mp j.property
  simp [heatState, trialInverse, hi, hj]
  abel

theorem leverage_eq_zero_of_row_zero {R B : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] (C : Matrix R B ℂ) (τ : ℝ) (i : R)
    (hrow : ∀ j, C i j = 0) : leverage C τ i = 0 := by
  unfold leverage ridgeProjection
  have hrow' : ∀ j, (C * (ridgeGram C τ)⁻¹ * Cᴴ) i j = 0 := by
    intro j
    simp [Matrix.mul_apply, hrow]
  rw [hrow' i]
  rfl

theorem trialWeights_eq_zero_of_core {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (s : TrialState core) (τ : ℝ) {i : ι} (hi : i ∈ core) :
    trialWeights t r s τ i = 0 := by
  unfold trialWeights
  apply leverage_eq_zero_of_row_zero
  intro j
  simp [trialCross, hi]

theorem trialWeights_eq_zero_of_inactive {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (s : TrialState core) (τ : ℝ) {i : ι} (hi : i ∉ s.active) :
    trialWeights t r s τ i = 0 := by
  unfold trialWeights
  apply leverage_eq_zero_of_row_zero
  intro j
  simp [trialCross, hi]

end AndersonAC.AgentS6Construct
