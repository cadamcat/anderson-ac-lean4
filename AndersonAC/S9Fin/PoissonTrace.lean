import AndersonAC.S9Fin.Scalar

noncomputable section
open MeasureTheory AndersonAC.S9
open scoped Matrix ComplexConjugate

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_unitary_conjugation (U : unitary (Matrix n n ℂ)) (M : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U M).trace = M.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

lemma matrixResolvent_diagonalization (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) :
    matrixResolvent H E η = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((hH.eigenvalues i - E : ℝ) - η * Complex.I)⁻¹)) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
  let v (i : n) : ℂ := (hH.eigenvalues i - E : ℝ) - η * Complex.I
  have hn : ∀ i, v i ≠ 0 := by
    intro i h
    have hh := congrArg Complex.im h
    simp [v] at hh
    exact hη.ne' hh
  have hV : IsUnit (Matrix.diagonal v) := Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hn i)))
  have hdiag : Matrix.diagonal v = Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) -
      ((E : ℂ) + η * Complex.I) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [v, Matrix.one_apply]
      ring
    · simp [Matrix.one_apply, hij]
  have hmat : H - ((E : ℂ) + η * Complex.I) • 1 = φ (Matrix.diagonal v) := by
    rw [hdiag]
    simp only [map_sub, map_smul, map_one]
    have hspec : H = φ (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))) := hH.spectral_theorem
    exact congrArg (fun M : Matrix n n ℂ => M - ((E : ℂ) + η * Complex.I) • 1) hspec
  have hinv : (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j <;> simp [hij, hn, Matrix.one_apply]
  unfold matrixResolvent
  rw [hmat, starAlgEquiv_matrix_inv φ _ hV, hinv]

/-- The full finite spectral count is the sum of true diagonal Poisson weights. -/
lemma sum_scalarQ_eq_eigenvalues (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) :
    (∑ i, scalarQ H E η i) =
      ∑ i, η / ((hH.eigenvalues i - E) ^ 2 + η ^ 2) := by
  have ht : (∑ i, scalarQ H E η i) = (matrixResolvent H E η).trace.im := by
    simp [Matrix.trace, scalarQ]
  rw [ht, matrixResolvent_diagonalization H hH E η hη, trace_unitary_conjugation,
    Matrix.trace_diagonal, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.inv_im, Complex.normSq_apply, pow_two]

lemma finiteWindowRank_eq_card (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) :
    windowRank H hH E δ = Fintype.card {i : n // |hH.eigenvalues i - E| ≤ δ} := by
  classical
  let U := hH.eigenvectorUnitary
  have hu : IsUnit (U : Matrix n n ℂ).det := Matrix.UnitaryGroup.det_isUnit U
  have hs : IsUnit (↑(star U) : Matrix n n ℂ).det := Matrix.UnitaryGroup.det_isUnit (star U)
  unfold windowRank windowProjection
  rw [← Unitary.coe_star, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hs,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu, Matrix.rank_diagonal]
  have hp : ∀ i : n,
      (if |hH.eigenvalues i - E| ≤ δ then (1 : ℂ) else 0) ≠ 0 ↔
        |hH.eigenvalues i - E| ≤ δ := by
    intro i
    split_ifs <;> simp_all
  simp only [Fintype.card_subtype, hp]

lemma finiteWindowRank_eq_sum (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) :
    (windowRank H hH E δ : ℝ) =
      ∑ i, if |hH.eigenvalues i - E| ≤ δ then (1 : ℝ) else 0 := by
  classical
  rw [finiteWindowRank_eq_card, Fintype.card_subtype]
  exact (Finset.sum_boole _ _).symm

end AndersonAC.SolS9
