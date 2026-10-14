import AndersonAC.S9Fin.ColumnSpectral

noncomputable section
open AndersonAC.S9
open scoped Matrix ComplexConjugate

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma cutInverse_diagonalization (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hprincipal : allPrincipalInvertible H E) :
    cutInverse H hH E η ε = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
      (Matrix.diagonal (fun j => if |hH.eigenvalues j - E| ≤ ε * η then 0
        else ((hH.eigenvalues j - E : ℝ) : ℂ)⁻¹)) := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
  let v (j : n) : ℂ := (hH.eigenvalues j - E : ℝ)
  let V := Matrix.diagonal v
  let W := Matrix.diagonal (fun j : n =>
    if |hH.eigenvalues j - E| ≤ ε * η then (1 : ℂ) else 0)
  have hH0 : H - (E : ℂ) • 1 = φ V := by
    have hdiag : V = Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) - (E : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [V, v, Matrix.one_apply, hij]
    rw [hdiag]
    simp only [map_sub, map_smul, map_one]
    have hspec : H = φ (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ))) := hH.spectral_theorem
    exact congrArg (fun M : Matrix n n ℂ => M - (E : ℂ) • 1) hspec
  have hV : IsUnit V := by
    have hu := (allPrincipalInvertible_isUnit H E hprincipal).map φ.symm.toRingHom
    change IsUnit (φ.symm (H - (E : ℂ) • 1)) at hu
    rw [hH0, φ.symm_apply_apply] at hu
    exact hu
  have hn : ∀ j, v j ≠ 0 := by
    have hu := Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hV)
    exact fun j => (hu j).ne_zero
  have hinv : V⁻¹ = Matrix.diagonal (fun j => (v j)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    change Matrix.diagonal (fun j => (v j)⁻¹) * Matrix.diagonal v = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j <;> simp [hij, hn, Matrix.one_apply]
  have hQ : windowProjection H hH E (ε * η) = φ W := rfl
  have hOne : 1 - W = Matrix.diagonal (fun j : n =>
      if |hH.eigenvalues j - E| ≤ ε * η then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [W, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply_eq,
        if_pos rfl]
      split_ifs <;> simp
    · simp [W, Matrix.diagonal_apply, Matrix.one_apply, hij]
  unfold cutInverse
  rw [hH0, starAlgEquiv_matrix_inv φ V hV, hQ]
  have hInside : 1 - φ W = φ (1 - W) := by simp only [map_sub, map_one]
  rw [hInside, ← map_mul, hinv, hOne, Matrix.diagonal_mul_diagonal]
  apply congrArg φ
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> simp [v]
  · simp [Matrix.diagonal_apply, hij]

lemma outside_cut_inverse_weight (u η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hout : ε * η < |u|) :
    ‖(u : ℂ)⁻¹‖ ^ 2 ≤ cutMultiplier ε * ‖((u : ℂ) - η * Complex.I)⁻¹‖ ^ 2 := by
  have hs : (ε * η) ^ 2 < |u| ^ 2 :=
    (sq_lt_sq₀ (mul_pos hε hη).le (abs_nonneg u)).mpr hout
  rw [mul_pow, sq_abs] at hs
  have hu : 0 < u ^ 2 := lt_trans (mul_pos (sq_pos_of_pos hε) (sq_pos_of_pos hη)) hs
  have hd : 0 < u ^ 2 + η ^ 2 := by positivity
  have hreal : ‖(u : ℂ)⁻¹‖ ^ 2 = 1 / u ^ 2 := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs]
  have hcomplex : ‖((u : ℂ) - η * Complex.I)⁻¹‖ ^ 2 = 1 / (u ^ 2 + η ^ 2) := by
    rw [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  rw [hreal, hcomplex, mul_one_div]
  apply (div_le_div_iff₀ hu hd).mpr
  have hratio : η ^ 2 ≤ u ^ 2 / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith [hs.le]
  have hratio' : η ^ 2 ≤ ε⁻¹ ^ 2 * u ^ 2 := by
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hratio
  unfold cutMultiplier
  nlinarith

set_option linter.unusedVariables false in
theorem cut_column_proof (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n) (i : A) :
    η * columnNormSq (dampingFunction η (compress A (cutInverse H hH E η ε))) i ≤
      cutMultiplier ε * scalarQ H E η i := by
  classical
  let a (j : n) : ℂ := if |hH.eigenvalues j - E| ≤ ε * η then 0
    else ((hH.eigenvalues j - E : ℝ) : ℂ)⁻¹
  let b (j : n) : ℂ := ((hH.eigenvalues j - E : ℝ) - η * Complex.I)⁻¹
  have hweight : ∀ j, ‖a j‖ ^ 2 ≤ cutMultiplier ε * ‖b j‖ ^ 2 := by
    intro j
    by_cases hj : |hH.eigenvalues j - E| ≤ ε * η
    · simp only [a, if_pos hj, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (by unfold cutMultiplier; positivity) (sq_nonneg _)
    · simp only [a, if_neg hj, b]
      exact outside_cut_inverse_weight _ η ε hη hε (lt_of_not_ge hj)
  have hfull : columnNormSq (cutInverse H hH E η ε) (i : n) ≤
      cutMultiplier ε * columnNormSq (matrixResolvent H E η) (i : n) := by
    rw [cutInverse_diagonalization H hH E η ε hprincipal,
      matrixResolvent_diagonalization H hH E η hη]
    exact conjugated_diagonal_column_le hH.eigenvectorUnitary a b (cutMultiplier ε) hweight i
  calc
    η * columnNormSq (dampingFunction η (compress A (cutInverse H hH E η ε))) i ≤
        η * columnNormSq (compress A (cutInverse H hH E η ε)) i :=
      mul_le_mul_of_nonneg_left (dampingFunction_columnNormSq_le _
        ((cutInverse_isHermitian H hH E η ε hprincipal).submatrix _) η i) hη.le
    _ ≤ η * columnNormSq (cutInverse H hH E η ε) (i : n) :=
      mul_le_mul_of_nonneg_left (compress_columnNormSq_le A _ i) hη.le
    _ ≤ η * (cutMultiplier ε * columnNormSq (matrixResolvent H E η) (i : n)) :=
      mul_le_mul_of_nonneg_left hfull hη.le
    _ = cutMultiplier ε * scalarQ H E η i := by
      rw [scalarQ_eq_ward H hH E η hη i]
      ring

end AndersonAC.SolS9
