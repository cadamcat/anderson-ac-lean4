import AndersonAC.S78Var.NormalizedResolvent

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem normalized_inverse_pair {ι : Type} [Fintype ι] [DecidableEq ι]
    (M G G' : Matrix ι ι ℂ) (r ζ : ι → ℂ) (t : ℝ) (ht : 0 < t)
    (hInv : AndersonAC.Blueprint.twoSidedInverse (M - (t : ℂ) • Matrix.diagonal r) G)
    (hInv' : AndersonAC.Blueprint.twoSidedInverse (M - (t : ℂ) • Matrix.diagonal (r + ζ)) G') :
    let h := (Real.sqrt t : ℂ) • G
    let h' := (Real.sqrt t : ℂ) • G'
    let z := (Real.sqrt t : ℂ) • ζ
    IsUnit h.det ∧ IsUnit (h⁻¹ - Matrix.diagonal z).det ∧
      h' = (h⁻¹ - Matrix.diagonal z)⁻¹ := by
  let s : ℂ := (Real.sqrt t : ℂ)
  have hs : s ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr ht))
  have hs2 : s * s = (t : ℂ) := by
    dsimp [s]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  have hist : s⁻¹ * (t : ℂ) = s := by rw [← hs2, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hright : (s • G) * (s⁻¹ • (M - (t : ℂ) • Matrix.diagonal r)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hInv.2, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have he : (s • G)⁻¹ = s⁻¹ • (M - (t : ℂ) • Matrix.diagonal r) :=
    Matrix.inv_eq_right_inv hright
  have hdiff : (s • G)⁻¹ - Matrix.diagonal (s • ζ) =
      s⁻¹ • (M - (t : ℂ) • Matrix.diagonal (r + ζ)) := by
    have hadd : Matrix.diagonal (r + ζ) = Matrix.diagonal r + Matrix.diagonal ζ :=
      (Matrix.diagonal_add r ζ).symm
    rw [he, hadd, Matrix.diagonal_smul]
    simp only [smul_sub, smul_add, smul_smul, hist]
    abel
  have hright' : ((s • G)⁻¹ - Matrix.diagonal (s • ζ)) * (s • G') = 1 := by
    rw [hdiff, Matrix.smul_mul, Matrix.mul_smul, hInv'.1, smul_smul, inv_mul_cancel₀ hs, one_smul]
  exact ⟨Matrix.isUnit_det_of_right_inverse hright,
    Matrix.isUnit_det_of_right_inverse hright', (Matrix.inv_eq_right_inv hright').symm⟩

end AndersonAC.SolS78Var
