import Mathlib
import AndersonAC.S6.LocalizationInputs

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

theorem schurNormBound_proof : SchurNormBoundStatement := by
  intro m n A u v hu hv hrow hcol
  -- Operator norm via continuous linear map.
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  -- Name the continuous map and its action.
  set T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A with hT
  show ‖T x‖ ≤ Real.sqrt (u * v) * ‖x‖
  -- Pointwise squared bound implies the norm bound.
  have hC_sq : (Real.sqrt (u * v) * ‖x‖) ^ 2 = (u * v) * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hu hv)]
  have hC_nonneg : 0 ≤ Real.sqrt (u * v) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  -- It suffices to bound the squares.
  suffices hsq : ‖T x‖ ^ 2 ≤ (u * v) * ‖x‖ ^ 2 by
    have hsq' : ‖T x‖ ^ 2 ≤ (Real.sqrt (u * v) * ‖x‖) ^ 2 := by
      rw [hC_sq]; exact hsq
    have h := (sq_le_sq₀ (norm_nonneg _) hC_nonneg).mp hsq'
    exact h
  -- Unfold norms as sums of squares.
  have hTx_eq : ∀ i, (T x).ofLp i = ∑ j, A i j * x.ofLp j := by
    intro i
    -- T x = toEuclideanLin A x as Euclidean vectors.
    have : T x = Matrix.toEuclideanLin A x := rfl
    rw [this]
    show ((Matrix.toEuclideanLin A x).ofLp) i = _
    -- toEuclideanLin = toLpLin 2 2, applied gives mulVec.
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_apply_eq_sum]
  have hnorm_T : ‖T x‖ ^ 2 = ∑ i, ‖(T x).ofLp i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  have hnorm_x : ‖x‖ ^ 2 = ∑ j, ‖x.ofLp j‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [hnorm_T, hnorm_x]
  -- Row-wise estimate.
  have hrow_est : ∀ i, ‖(T x).ofLp i‖ ^ 2 ≤
      u * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
    intro i
    rw [hTx_eq i]
    -- Step 1: triangle inequality.
    have htri : ‖∑ j, A i j * x.ofLp j‖ ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
      calc ‖∑ j, A i j * x.ofLp j‖ ≤ ∑ j, ‖A i j * x.ofLp j‖ :=
            norm_sum_le _ _
        _ = ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
            congr 1; ext j; rw [norm_mul]
    -- Step 2: Cauchy-Schwarz in the form (∑ r)^2 ≤ (∑ f)(∑ g).
    have hCS : (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 ≤
        (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ?_ ?_ ?_
      · intro j _
        exact norm_nonneg _
      · intro j _
        exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
      · intro j _
        -- (a*ξ)^2 = a * (a*ξ^2)
        exact (by ring : (‖A i j‖ * ‖x.ofLp j‖) ^ 2 =
          ‖A i j‖ * (‖A i j‖ * ‖x.ofLp j‖ ^ 2)).le
    have hrow_i := hrow i
    have hsum_nonneg : 0 ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
    have hCS' : (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 ≤
        u * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
      calc (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2
            ≤ (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := hCS
          _ ≤ u * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hrow_i hsum_nonneg
    -- Combine: ‖y_i‖^2 ≤ (∑ r)^2 ≤ u * ∑ g.
    have hsq1 : ‖∑ j, A i j * x.ofLp j‖ ^ 2 ≤
        (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) htri
    exact le_trans hsq1 hCS'
  -- Sum over rows and swap sums.
  calc ∑ i, ‖(T x).ofLp i‖ ^ 2
        ≤ ∑ i, (u * (∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2)) :=
          Finset.sum_le_sum fun i _ => hrow_est i
      _ = u * (∑ i, ∑ j, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ = u * (∑ j, ∑ i, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) := by
          rw [Finset.sum_comm]
      _ ≤ u * (∑ j, v * ‖x.ofLp j‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hu
          apply Finset.sum_le_sum
          intro j _
          -- Factor the column sum.
          have hcol_j := hcol j
          have hfac : (∑ i, ‖A i j‖ * ‖x.ofLp j‖ ^ 2) =
              (∑ i, ‖A i j‖) * ‖x.ofLp j‖ ^ 2 := by
            rw [Finset.sum_mul]
          rw [hfac]
          exact mul_le_mul_of_nonneg_right hcol_j (sq_nonneg _)
      _ = (u * v) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
          have h1 : (∑ j, v * ‖x.ofLp j‖ ^ 2) = v * ∑ j, ‖x.ofLp j‖ ^ 2 := by
            rw [← Finset.mul_sum]
          rw [h1, ← mul_assoc]

#print axioms schurNormBound_proof

end AndersonAC.SolS6
