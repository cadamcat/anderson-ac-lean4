import AndersonAC.S9Fin.Basic

noncomputable section
open AndersonAC.S9
open scoped ComplexConjugate

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma damping_isUnit (B : Matrix n n ℂ) (hB : B.IsHermitian) (η : ℝ) :
    IsUnit (1 - (η * Complex.I) • B) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary
  have hd : IsUnit (Matrix.diagonal (fun i => 1 - (η * Complex.I) * (hB.eigenvalues i : ℂ))) := by
    apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro i
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  have hdiag : Matrix.diagonal (fun i => 1 - (η * Complex.I) * (hB.eigenvalues i : ℂ)) =
      1 - (η * Complex.I) • Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hdiag] at hd
  have heq : φ (1 - (η * Complex.I) • Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) =
      1 - (η * Complex.I) • B := by
    simp only [map_sub, map_one, map_smul]
    rw [← hB.spectral_theorem]
  rw [← heq]
  exact hd.map φ.toAlgEquiv.toAlgHom.toRingHom

set_option linter.unusedVariables false in
theorem dampingFunction_difference_proof (B C : Matrix n n ℂ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (η : ℝ) (hη : 0 < η) :
    dampingFunction η B - dampingFunction η C =
      (1 - (η * Complex.I) • B)⁻¹ * (B - C) * (1 - (η * Complex.I) • C)⁻¹ := by
  let X := 1 - (η * Complex.I) • B
  let Y := 1 - (η * Complex.I) • C
  have hX : IsUnit X := damping_isUnit B hB η
  have hY : IsUnit Y := damping_isUnit C hC η
  have hXd : IsUnit X.det := X.isUnit_iff_isUnit_det.mp hX
  have hYd : IsUnit Y.det := Y.isUnit_iff_isUnit_det.mp hY
  have hXB : X * B = B * X := by
    simp only [X, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul]
  change B * X⁻¹ - C * Y⁻¹ = X⁻¹ * (B - C) * Y⁻¹
  apply hX.mul_left_cancel
  apply hY.mul_right_cancel
  calc
    X * (B * X⁻¹ - C * Y⁻¹) * Y = B * Y - X * C := by
      simp only [mul_sub, sub_mul, ← Matrix.mul_assoc]
      rw [hXB, Matrix.mul_nonsing_inv_cancel_right X B hXd,
        Matrix.nonsing_inv_mul_cancel_right Y (X * C) hYd]
    _ = B - C := by
      simp only [X, Y, mul_sub, sub_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul]
      abel
    _ = X * (X⁻¹ * (B - C) * Y⁻¹) * Y := by
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv X hXd, one_mul,
        Matrix.nonsing_inv_mul_cancel_right Y (B - C) hYd]

set_option linter.unusedVariables false in
/-- The identity also holds for a singular matrix: the total matrix inverse is zero. -/
theorem damped_ward_identity_proof (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η : ℝ) (hη : 0 < η) (r : n → ℂ) (hr : ∀ i, 0 < (r i).im) :
    let G := (S - (η : ℂ) • Matrix.diagonal r)⁻¹
    matrixImaginaryPart G = (η : ℂ) •
      (star G * Matrix.diagonal (fun i => ((r i).im : ℂ)) * G) := by
  let A := S - (η : ℂ) • Matrix.diagonal r
  change matrixImaginaryPart A⁻¹ = (η : ℂ) •
    (star A⁻¹ * Matrix.diagonal (fun i => ((r i).im : ℂ)) * A⁻¹)
  by_cases hA : IsUnit A.det
  · have hAG : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have hsAG : star A⁻¹ * star A = 1 := by
      rw [← star_mul, hAG, star_one]
    have hid : A⁻¹ - star A⁻¹ = star A⁻¹ * (star A - A) * A⁻¹ := by
      rw [mul_sub, sub_mul, hsAG, one_mul, Matrix.mul_assoc, hAG, mul_one]
    have him : star A - A = (2 * Complex.I) •
        ((η : ℂ) • Matrix.diagonal (fun i => ((r i).im : ℂ))) := by
      simp only [A]
      simp only [star_sub, star_smul, hS.star_eq]
      have hreal : star (η : ℂ) = (η : ℂ) := by simp
      rw [hreal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
          Matrix.star_apply, smul_eq_mul]
        apply Complex.ext <;> simp
        all_goals ring
      · simp [hij, Matrix.star_apply, eq_comm]
    unfold matrixImaginaryPart
    rw [hid, him]
    simp [smul_smul, ← mul_assoc]
  · rw [Matrix.nonsing_inv_apply_not_isUnit A hA]
    simp [matrixImaginaryPart]

end AndersonAC.SolS9
