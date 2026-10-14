import AndersonAC.S78Var.OperatorBounds

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

/-- Frobenius sums transpose-invariant. -/
theorem frobenius_transpose {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) :
    (∑ i, ∑ j, ‖X.transpose i j‖ ^ 2) = (∑ i, ∑ j, ‖X i j‖ ^ 2) := by
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Left Frobenius bound via columns + l2_opNorm_mulVec. -/
theorem frobenius_left_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (A X : Matrix ι ι ℂ) :
    (∑ i, ∑ j, ‖(A * X) i j‖ ^ 2)
      ≤ ‖A‖ ^ 2 * (∑ i, ∑ j, ‖X i j‖ ^ 2) := by
  classical
  -- For each column j, ∑_i ‖(A*X)(i,j)‖^2 = ‖A*ᵥ col_j‖_2^2 ≤ ‖A‖^2 ‖col_j‖_2^2
  have hcol : ∀ j, ∑ i, ‖(A * X) i j‖ ^ 2
      ≤ ‖A‖ ^ 2 * ∑ i, ‖X i j‖ ^ 2 := by
    intro j
    let v : ι → ℂ := fun k => X k j
    have hmul : ∀ i, (A * X) i j = (A *ᵥ v) i := by
      intro i
      simp only [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum, v]
    simp only [hmul]
    have hop : ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2
        ≤ ‖A‖ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by
      have hle : ‖WithLp.toLp 2 (A *ᵥ v)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 v‖ := by
        have hle0 : ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A)
            (WithLp.toLp 2 v)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have heq : ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A)
            (WithLp.toLp 2 v) = WithLp.toLp 2 (A *ᵥ v) := rfl
        rw [heq] at hle0
        exact hle0
      calc ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2
          ≤ (‖A‖ * ‖WithLp.toLp 2 v‖) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = ‖A‖ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by ring
    have hnorm : ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2 = ∑ i, ‖(A *ᵥ v) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    have hnorm2 : ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [hnorm, hnorm2] at hop
    simpa [v] using hop
  calc ∑ i, ∑ j, ‖(A * X) i j‖ ^ 2
      = ∑ j, ∑ i, ‖(A * X) i j‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ j, (‖A‖ ^ 2 * ∑ i, ‖X i j‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact hcol j
    _ = ‖A‖ ^ 2 * ∑ j, ∑ i, ‖X i j‖ ^ 2 := by rw [Finset.mul_sum]
    _ = ‖A‖ ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by rw [Finset.sum_comm]

def hsSq {ι : Type} [Fintype ι] (X : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖X i j‖ ^ 2

theorem hsSq_nonneg {ι : Type} [Fintype ι] (X : Matrix ι ι ℂ) : 0 ≤ hsSq X := by
  unfold hsSq
  positivity

theorem hsSq_conjTranspose {ι : Type} [Fintype ι] (X : Matrix ι ι ℂ) :
    hsSq X.conjTranspose = hsSq X := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]

theorem hsSq_right_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (X A : Matrix ι ι ℂ) : hsSq (X * A) ≤ ‖A‖ ^ 2 * hsSq X := by
  rw [← hsSq_conjTranspose (X * A), Matrix.conjTranspose_mul]
  have hh := frobenius_left_mul A.conjTranspose X.conjTranspose
  change hsSq (A.conjTranspose * X.conjTranspose) ≤ ‖A.conjTranspose‖ ^ 2 * hsSq X.conjTranspose at hh
  rwa [Matrix.l2_opNorm_conjTranspose, hsSq_conjTranspose] at hh

theorem hsSq_two_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (A X B : Matrix ι ι ℂ) (u : ℝ) (hu : 0 ≤ u) (hA : ‖A‖ ≤ u) (hB : ‖B‖ ≤ u) :
    hsSq (A * X * B) ≤ u ^ 4 * hsSq X := by
  have hL : hsSq (A * X) ≤ ‖A‖ ^ 2 * hsSq X := frobenius_left_mul A X
  calc hsSq (A * X * B) ≤ ‖B‖ ^ 2 * hsSq (A * X) := hsSq_right_mul _ _
    _ ≤ ‖B‖ ^ 2 * (‖A‖ ^ 2 * hsSq X) := mul_le_mul_of_nonneg_left hL (sq_nonneg _)
    _ ≤ u ^ 2 * (u ^ 2 * hsSq X) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (norm_nonneg _) hB 2
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hA 2) (hsSq_nonneg _)
      · exact mul_nonneg (sq_nonneg _) (hsSq_nonneg _)
      · exact sq_nonneg _
    _ = u ^ 4 * hsSq X := by ring

end AndersonAC.SolS78Var
