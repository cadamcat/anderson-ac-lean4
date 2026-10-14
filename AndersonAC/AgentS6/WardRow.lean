import AndersonAC.S6.Statements

/-! Ward row bound (06-clearing.tex `clearing-row-bound`): `Σ_j p_j |h_ij|² = Im g_ii`, hence
`Σ_j |h_ij|² ≤ K/c`. -/

noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace AndersonAC.S6

theorem ward_row_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (t c K : ℝ) (p : ι → ℝ)
    (g : Matrix ι ι ℂ) (ht : 0 < t) (hc : 0 < c) (hp : ∀ i, c ≤ p i)
    (hdiag : ∀ i, ‖g i i‖ ≤ K)
    (hWard : (t : ℂ) • (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ) = matrixImag g) :
    Planned.ward_row_bound t c K p g ht hc hp hdiag hWard := by
  intro i
  have hentry := congrFun (congrFun hWard i) i
  have hL : ((t : ℂ) • (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ)) i i =
      ((∑ j, p j * ‖scaledInverse t g i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      smul_eq_mul, scaledInverse, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (Real.sqrt_nonneg t), mul_pow, Real.sq_sqrt ht.le]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.mul_conj', Complex.star_def]
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    push_cast
    ring
  have hR : (matrixImag g) i i = (((g i i).im : ℝ) : ℂ) := by
    simp only [matrixImag, AndersonAC.Blueprint.matrixImag, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.conjTranspose_apply, smul_eq_mul, Complex.star_def]
    rw [Complex.sub_conj]
    field_simp
    push_cast
    ring
  rw [hL, hR] at hentry
  have heq : (∑ j, p j * ‖scaledInverse t g i j‖ ^ 2) = (g i i).im := by exact_mod_cast hentry
  refine ⟨heq, ?_⟩
  unfold sqRow
  have h1 : c * (∑ j, ‖scaledInverse t g i j‖ ^ 2) ≤ ∑ j, p j * ‖scaledInverse t g i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hp j) (sq_nonneg _)
  have h2 : (g i i).im ≤ K := (Complex.im_le_norm _).trans (hdiag i)
  rw [le_div_iff₀ hc]
  linarith

end AndersonAC.S6

#print axioms AndersonAC.S6.ward_row_bound
