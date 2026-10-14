import AndersonAC.S9Fin.Columns
import AndersonAC.S9Fin.CutRank

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma measurable_matrix_inverse : Measurable (fun M : Matrix n n ℂ => M⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul
    continuous_id.matrix_adjugate.measurable

lemma scalarQ_measurable {Ξ : Type*} [MeasurableSpace Ξ]
    (H : Ξ → Matrix n n ℂ) (hH : Measurable H) (E η : ℝ) (i : n) :
    Measurable (fun ω => scalarQ (H ω) E η i) := by
  unfold scalarQ matrixResolvent
  exact Complex.measurable_im.comp
    ((measurable_matrix_inverse.comp (hH.sub measurable_const)).eval_matrix)

lemma scalar_damped_matrix_eq (H : Matrix n n ℂ) (E η : ℝ) :
    H - ((E : ℂ) + η * Complex.I) • 1 =
      (H - (E : ℂ) • 1) - (η : ℂ) • Matrix.diagonal (fun _ : n => Complex.I) := by
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.one_apply, Matrix.diagonal_apply, hij, smul_eq_mul] <;> ring

lemma scalarQ_eq_ward (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (i : n) :
    scalarQ H E η i = η * columnNormSq (matrixResolvent H E η) i := by
  have hw := weighted_ward_diag (H - (E : ℂ) • 1)
    (hH.sub (by simp [Matrix.IsHermitian])) η hη (fun _ : n => Complex.I)
    (by simp) i
  simpa only [scalarQ, matrixResolvent, scalar_damped_matrix_eq, Complex.I_im,
    one_mul, columnNormSq] using hw

lemma scalarQ_nonneg (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (i : n) : 0 ≤ scalarQ H E η i := by
  rw [scalarQ_eq_ward H hH E η hη i]
  exact mul_nonneg hη.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma scalarQ_zero (H : Matrix n n ℂ) (hH : H.IsHermitian) (E : ℝ) (i : n) :
    scalarQ H E 0 i = 0 := by
  have hG : (matrixResolvent H E 0).IsHermitian := by
    simpa [matrixResolvent] using (hH.sub (by simp [Matrix.IsHermitian])).inv
  have hh := congrArg Complex.im (hG.apply i i)
  unfold scalarQ
  simp at hh
  linarith

lemma matrixResolvent_star (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ) :
    matrixResolvent H E (-η) = star (matrixResolvent H E η) := by
  unfold matrixResolvent
  rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse,
    ← Ring.inverse_star]
  congr 1
  simp only [star_sub, star_smul, star_one, hH.star_eq]
  congr 2
  simp

lemma matrixResolvent_norm_pos (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) : matrixOpNorm (matrixResolvent H E η) ≤ η⁻¹ := by
  have hb := dissipative_inverse_bound_proof (H - (E : ℂ) • 1)
    (hH.sub (by simp [Matrix.IsHermitian])) η 1 hη zero_lt_one
    (fun _ : n => Complex.I) (by simp)
  simpa only [matrixResolvent, scalar_damped_matrix_eq, mul_one] using hb

lemma matrixResolvent_norm_ne_zero (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : η ≠ 0) : matrixOpNorm (matrixResolvent H E η) ≤ |η|⁻¹ := by
  rcases lt_or_gt_of_ne hη with hn | hp
  · have hb := matrixResolvent_norm_pos H hH E (-η) (neg_pos.mpr hn)
    rw [matrixResolvent_star H hH E η, matrixOpNorm_eq, norm_star] at hb
    simpa only [matrixOpNorm_eq, abs_of_neg hn] using hb
  · simpa only [abs_of_pos hp] using matrixResolvent_norm_pos H hH E η hp

lemma matrix_entry_norm_le (G : Matrix n n ℂ) (i j : n) :
    ‖G j i‖ ≤ matrixOpNorm G := by
  let ei : EuclideanSpace ℂ n := EuclideanSpace.single i 1
  have heq : G.toEuclideanLin ei = WithLp.toLp 2 (fun j => G j i) := by
    change WithLp.toLp 2 (G *ᵥ Pi.single i 1) = _
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    ‖G j i‖ ≤ ‖G.toEuclideanLin ei‖ := by
      rw [heq]
      change ‖(WithLp.toLp 2 (fun k => G k i) : EuclideanSpace ℂ n) j‖ ≤
        ‖(WithLp.toLp 2 (fun k => G k i) : EuclideanSpace ℂ n)‖
      exact PiLp.norm_apply_le _ _
    _ ≤ matrixOpNorm G * ‖ei‖ := G.toEuclideanLin.toContinuousLinearMap.le_opNorm _
    _ = matrixOpNorm G := by simp [ei]

lemma truncatedReadout_abs_bound (b : CertificateBounds) (ε q : ℝ) :
    |truncatedReadout b ε q| ≤ |2 * cutMultiplier ε| * |q| + columnConstant b := by
  unfold truncatedReadout
  have hc := columnConstant_pos_proof b
  rcases le_total (2 * cutMultiplier ε * q) (columnConstant b) with h | h
  · rw [min_eq_left h, abs_mul]
    linarith
  · rw [min_eq_right h, abs_of_pos hc]
    linarith [mul_nonneg (abs_nonneg (2 * cutMultiplier ε)) (abs_nonneg q)]

lemma truncatedReadout_torus_integrable (d m : ℕ) (coupling E η ε : ℝ)
    (b : CertificateBounds) (i : Torus d m) :
    Integrable (fun ω => truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i))
      (torusLaw d m) := by
  have hm : Measurable (fun ω : TorusConfiguration d m =>
      truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) := by
    unfold truncatedReadout
    have hq := scalarQ_measurable _ (continuous_periodicHamiltonian d m coupling).measurable E η i
    exact (hq.const_mul (2 * cutMultiplier ε)).min measurable_const
  by_cases hη : η = 0
  · subst η
    have heq : (fun ω : TorusConfiguration d m =>
        truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E 0 i)) =
        fun _ => (0 : ℝ) := by
      funext ω
      rw [scalarQ_zero _ (periodicHamiltonian_isHermitian_proof d m coupling ω)]
      simp [truncatedReadout, (columnConstant_pos_proof b).le]
    rw [heq]
    exact integrable_zero _ _ _
  · refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (C := |2 * cutMultiplier ε| * |η|⁻¹ + columnConstant b) ?_⟩
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    apply (truncatedReadout_abs_bound b ε _).trans
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (Complex.abs_im_le_norm _).trans ((matrix_entry_norm_le _ i i).trans
      (matrixResolvent_norm_ne_zero _ (periodicHamiltonian_isHermitian_proof d m coupling ω)
        E η hη))

end AndersonAC.SolS9
