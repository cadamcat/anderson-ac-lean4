import AndersonAC.S9.Core
import AndersonAC.Boundary.Poisson

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace AndersonAC.SolS9

theorem borelTransform_eq_resolventTransform (μ : Measure ℝ) (z : ℂ) :
    borelTransform μ z = MeasureTheory.resolventTransform μ z := by
  unfold borelTransform AndersonAC.Blueprint.borelTransform MeasureTheory.resolventTransform
  apply integral_congr_ae
  filter_upwards with t
  simp [resolvent, Ring.inverse_eq_inv']

theorem poisson_interval_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E r : ℝ) (hr : 0 < r) :
    μ (Set.Ioo (E - r) (E + r)) ≤ ENNReal.ofReal
      (2 * r * (borelTransform μ ((E : ℂ) + r * Complex.I)).im) := by
  let S := Set.Ioo (E - r) (E + r)
  let f := AndersonAC.Boundary.poissonKernel E r
  have hi : Integrable f μ := AndersonAC.Boundary.integrable_poissonKernel μ E r hr
  have hpoint : ∀ t ∈ S, (2 * r)⁻¹ ≤ f t := by
    intro t ht
    have htabs : |t - E| ≤ r := by apply abs_le.mpr; constructor <;> linarith [ht.1, ht.2]
    have hsq : (t - E) ^ 2 ≤ r ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg _) hr.le).mpr htabs
      simpa only [sq_abs] using h
    change (2 * r)⁻¹ ≤ r / ((t - E) ^ 2 + r ^ 2)
    have hden : 0 < (t - E) ^ 2 + r ^ 2 := by positivity
    apply (le_div_iff₀ hden).mpr
    apply (inv_mul_le_iff₀ (mul_pos (by norm_num) hr)).mpr
    nlinarith
  have hlower : (μ S).toReal / (2 * r) ≤ ∫ t, f t ∂μ := by
    calc
      _ = ∫ t in S, (2 * r)⁻¹ ∂μ := by
        simp [integral_const, Measure.real, Measure.restrict_apply_univ, div_eq_mul_inv, smul_eq_mul]
      _ ≤ ∫ t in S, f t ∂μ := by
        apply integral_mono_ae (integrable_const _) hi.restrict
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hpoint t ht
      _ ≤ ∫ t, f t ∂μ := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun t => by dsimp [f, AndersonAC.Boundary.poissonKernel]; positivity) hi
  have hreal : (μ S).toReal ≤ 2 * r *
      (borelTransform μ ((E : ℂ) + r * Complex.I)).im := by
    rw [borelTransform_eq_resolventTransform,
      AndersonAC.Boundary.im_resolventTransform_eq_poissonTransform μ E r hr]
    have h := (div_le_iff₀ (mul_pos (by norm_num) hr)).mp hlower
    simpa [f, AndersonAC.Boundary.poissonTransform, mul_comm] using h
  calc
    μ S = ENNReal.ofReal (μ S).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end AndersonAC.SolS9
