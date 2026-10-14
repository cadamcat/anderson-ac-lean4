import AndersonAC.S6.RidgeStatements

noncomputable section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix ComplexConjugate

namespace AndersonAC.SolS6

private lemma ridge_maxWeight_le_inv {B R : Type*} [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R] (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ)
    (hC : ‖C‖ ≤ 1) :
    AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ) ≤ τ⁻¹ := by
  classical
  let A : Matrix B B ℂ := AndersonAC.S6.ridgeGram C τ
  let T : Matrix B B ℂ := (τ : ℂ) • (1 : Matrix B B ℂ)
  have hGram : (AndersonAC.S6.gram C).PosSemidef := by
    unfold AndersonAC.S6.gram
    exact Matrix.posSemidef_conjTranspose_mul_self C
  have hT : T.PosDef := by
    rw [show T = (τ : ℂ) • (1 : Matrix B B ℂ) by rfl,
      Matrix.smul_one_eq_diagonal]
    apply Matrix.PosDef.diagonal
    intro i
    simpa using hτ
  have hA : A.PosDef := by
    dsimp [A]
    unfold AndersonAC.S6.ridgeGram
    exact Matrix.PosDef.posSemidef_add hGram hT
  have hTA : T ≤ A := by
    rw [Matrix.le_iff]
    change (A - T).PosSemidef
    simpa [A, T, AndersonAC.S6.ridgeGram] using hGram
  have hInv : A⁻¹ ≤ T⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
    exact CStarAlgebra.ringInverse_le_ringInverse hTA hT.isStrictlyPositive
  have hTinv : T⁻¹ = (τ⁻¹ : ℝ) • (1 : Matrix B B ℂ) := by
    apply Matrix.inv_eq_right_inv
    change ((τ : ℂ) • (1 : Matrix B B ℂ)) *
      ((τ⁻¹ : ℝ) • (1 : Matrix B B ℂ)) = 1
    ext i j
    simp [Matrix.mul_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, hτ.ne']
  have hCC : C * Cᴴ ≤ (1 : Matrix R R ℂ) := by
    have hCCpsd : (C * Cᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose C
    have hCCnorm : ‖C * Cᴴ‖ ≤ 1 := by
      rw [show ‖C * Cᴴ‖ = ‖C‖ * ‖C‖ by
        simpa [Matrix.l2_opNorm_conjTranspose] using
          (Matrix.l2_opNorm_conjTranspose_mul_self Cᴴ)]
      nlinarith [norm_nonneg C]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg (C * Cᴴ) hCCpsd.nonneg).mp hCCnorm
  have hConj : C * A⁻¹ * Cᴴ ≤ C * T⁻¹ * Cᴴ := by
    rw [Matrix.le_iff]
    have hFactor : C * T⁻¹ * Cᴴ - C * A⁻¹ * Cᴴ =
        C * (T⁻¹ - A⁻¹) * Cᴴ := by
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    rw [hFactor]
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (Matrix.le_iff.mp hInv).conjTranspose_mul_mul_same Cᴴ
  have hScalar : C * T⁻¹ * Cᴴ = (τ⁻¹ : ℝ) • (C * Cᴴ) := by
    rw [hTinv]
    ext i j
    simp [Matrix.mul_apply, Matrix.smul_apply, mul_assoc, mul_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hScaled : (τ⁻¹ : ℝ) • (C * Cᴴ) ≤ (τ⁻¹ : ℝ) • (1 : Matrix R R ℂ) :=
    smul_le_smul_of_nonneg_left hCC (inv_nonneg.mpr hτ.le)
  have hBound : C * A⁻¹ * Cᴴ ≤ (τ⁻¹ : ℝ) • (1 : Matrix R R ℂ) := by
    calc
      C * A⁻¹ * Cᴴ ≤ C * T⁻¹ * Cᴴ := hConj
      _ = (τ⁻¹ : ℝ) • (C * Cᴴ) := hScalar
      _ ≤ (τ⁻¹ : ℝ) • (1 : Matrix R R ℂ) := hScaled
  have hPoint : ∀ i : R, AndersonAC.S6.leverage C τ i ≤ τ⁻¹ := by
    intro i
    have hi := (Matrix.le_iff.mp hBound).diag_nonneg (i := i)
    have hcomplex : (C * A⁻¹ * Cᴴ) i i ≤ (τ⁻¹ : ℂ) := by
      simpa [Matrix.smul_one_eq_diagonal] using hi
    have hre : ((C * A⁻¹ * Cᴴ) i i).re ≤ τ⁻¹ := by
      simpa using (Complex.le_def.mp hcomplex).1
    change (AndersonAC.S6.ridgeProjection C τ i i).re ≤ τ⁻¹
    simpa [AndersonAC.S6.ridgeProjection, A] using hre
  unfold AndersonAC.S6.maxWeight
  change (↑(Finset.univ.sup (fun i => Real.toNNReal (AndersonAC.S6.leverage C τ i))) : ℝ)
    ≤ τ⁻¹
  rw [← Real.coe_toNNReal τ⁻¹ (inv_nonneg.mpr hτ.le)]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  exact Real.toNNReal_le_toNNReal (hPoint i)

theorem ridgeInitial_proof : RidgeInitialStatement := by
  intro B R instB instDecB instR instDecR C l hl hsmall hC
  refine ⟨?_, ?_⟩
  · have hτ : 0 < l ^ (-2 : ℤ) := zpow_pos hl _
    have hmax := ridge_maxWeight_le_inv C (l ^ (-2 : ℤ)) hτ hC
    have hInv : (l ^ (-2 : ℤ))⁻¹ = l ^ 2 := by
      rw [zpow_neg]
      simp
    simpa [hInv] using hmax
  · nlinarith [mul_lt_mul_of_pos_right hsmall hl]

#print axioms ridgeInitial_proof

end AndersonAC.SolS6
