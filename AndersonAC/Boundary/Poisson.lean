import Mathlib

/-!
# Poisson kernel form of the Borel transform

The Borel transform convention in the Anderson paper is
`F(z) = ∫ (t - z)⁻¹ dμ(t)`.  This file records its positive Poisson-kernel
imaginary part and a pointwise criterion for divergence at a boundary point.
-/

open MeasureTheory Complex spectrum Filter
open scoped Topology

namespace AndersonAC.Boundary

/-- The real Poisson kernel with height `y > 0`. -/
noncomputable def poissonKernel (x y t : ℝ) : ℝ :=
  y / ((t - x) ^ 2 + y ^ 2)

@[fun_prop]
theorem measurable_poissonKernel (x y : ℝ) : Measurable (poissonKernel x y) := by
  unfold poissonKernel
  fun_prop

/-- The Poisson transform of a finite measure on the real line. -/
noncomputable def poissonTransform (μ : Measure ℝ) (x y : ℝ) : ℝ :=
  ∫ t, poissonKernel x y t ∂μ

private theorem im_resolvent_eq_poissonKernel (t x y : ℝ) :
    (resolvent ((x : ℂ) + (y : ℂ) * I) t).im = poissonKernel x y t := by
  rw [resolvent, Ring.inverse_eq_inv']
  simp [poissonKernel, Complex.inv_im, Complex.normSq_apply]
  ring

/-- The imaginary part of the scalar Borel transform is exactly the Poisson transform. -/
theorem im_resolventTransform_eq_poissonTransform (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x y : ℝ) (hy : 0 < y) :
    (MeasureTheory.resolventTransform μ ((x : ℂ) + (y : ℂ) * I)).im =
      poissonTransform μ x y := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * I
  have hz : z ∉ (algebraMap ℝ ℂ) '' μ.support := by
    rintro ⟨t, ht, htz⟩
    have hzim : 0 < z.im := by simp [z, hy]
    rw [← htz] at hzim
    simp at hzim
  have hres : Integrable (fun t : ℝ => resolvent z t) μ :=
    MeasureTheory.integrable_resolvent hz
  rw [MeasureTheory.resolventTransform_apply, poissonTransform]
  change RCLike.im (∫ t, resolvent z t ∂μ) = ∫ t, poissonKernel x y t ∂μ
  rw [← integral_im hres]
  apply integral_congr_ae
  filter_upwards with t
  simpa [z] using im_resolvent_eq_poissonKernel t x y

/-- The Poisson kernel is integrable against a finite measure. -/
theorem integrable_poissonKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x y : ℝ) (hy : 0 < y) : Integrable (poissonKernel x y) μ := by
  refine Integrable.mono' (integrable_const (1 / y))
    (measurable_poissonKernel x y).aestronglyMeasurable ?_
  filter_upwards with t
  have hden : 0 < (t - x) ^ 2 + y ^ 2 := by positivity
  have hnonneg : 0 ≤ poissonKernel x y t :=
    div_nonneg (le_of_lt hy) (le_of_lt hden)
  have hbound : poissonKernel x y t ≤ 1 / y := by
    unfold poissonKernel
    calc
      y / ((t - x) ^ 2 + y ^ 2) ≤ y / y ^ 2 := by
        gcongr
        nlinarith [sq_nonneg (t - x)]
      _ = 1 / y := by field_simp [ne_of_gt hy]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hbound

/-- Increasing the measure increases its Poisson transform. -/
theorem poissonTransform_mono_measure {μ ν : Measure ℝ} [IsFiniteMeasure ν]
    (hμν : μ ≤ ν) (x y : ℝ) (hy : 0 < y) :
    poissonTransform μ x y ≤ poissonTransform ν x y := by
  unfold poissonTransform
  apply integral_mono_measure hμν
    (ae_of_all _ fun t => div_nonneg (le_of_lt hy) (by positivity))
  exact integrable_poissonKernel ν x y hy

/-- Imaginary parts of Borel transforms are monotone in the measure. -/
theorem im_resolventTransform_mono {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ ≤ ν) (x y : ℝ) (hy : 0 < y) :
    (MeasureTheory.resolventTransform μ ((x : ℂ) + (y : ℂ) * I)).im ≤
      (MeasureTheory.resolventTransform ν ((x : ℂ) + (y : ℂ) * I)).im := by
  rw [im_resolventTransform_eq_poissonTransform μ x y hy,
    im_resolventTransform_eq_poissonTransform ν x y hy]
  exact poissonTransform_mono_measure hμν x y hy

/-- On the interval of radius `y`, the Poisson kernel is at least `1 / (2*y)`. -/
private theorem one_div_two_mul_le_poissonKernel {x y t : ℝ} (hy : 0 < y)
    (ht : t ∈ Metric.closedBall x y) :
    1 / (2 * y) ≤ poissonKernel x y t := by
  have hdist : |t - x| ≤ y := by
    simpa [Real.dist_eq] using ht
  have hden : 0 < (t - x) ^ 2 + y ^ 2 := by positivity
  have hsq : (t - x) ^ 2 ≤ y ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (t - x)) (le_of_lt hy)).2 hdist
    simpa [abs_mul_abs_self] using h
  unfold poissonKernel
  rw [div_le_div_iff₀ (by positivity) hden]
  nlinarith

/-- A large symmetric density forces the Poisson transform to diverge.  The hypothesis is the
local density estimate that the singular-part application obtains from measure differentiation.
-/
theorem poissonTransform_tendsto_atTop_of_ballDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ)
    (hden : Filter.Tendsto (fun y : ℝ => μ.real (Metric.closedBall x y) / (2 * y))
      (𝓝[>] 0) atTop) :
    Filter.Tendsto (fun y : ℝ => poissonTransform μ x y) (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_mono' (l := 𝓝[>] 0) ?_ hden
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hypos : 0 < y := Set.mem_Ioi.mp hy
  have hkernel : Integrable (poissonKernel x y) μ := by
    apply Integrable.mono' (integrable_const (1 / y)) (measurable_poissonKernel x y).aestronglyMeasurable
    filter_upwards with t
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hypos
    have hdenom : 0 < (t - x) ^ 2 + y ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) hy2
    have hnonneg : 0 ≤ poissonKernel x y t :=
      div_nonneg (le_of_lt hypos) (le_of_lt hdenom)
    have hbound : poissonKernel x y t ≤ 1 / y := by
      unfold poissonKernel
      calc
        y / ((t - x) ^ 2 + y ^ 2) ≤ y / y ^ 2 := by
          gcongr
          nlinarith [sq_nonneg (t - x)]
        _ = 1 / y := by field_simp [ne_of_gt hypos]
    calc
      ‖poissonKernel x y t‖ = |poissonKernel x y t| := Real.norm_eq_abs _
      _ = poissonKernel x y t := abs_of_nonneg hnonneg
      _ ≤ 1 / y := hbound
  let g : ℝ → ℝ := (Metric.closedBall x y).indicator (fun _ => 1 / (2 * y))
  have hg : Integrable g μ := by
    dsimp [g]
    exact (integrable_const (1 / (2 * y))).indicator measurableSet_closedBall
  have hpoint : g ≤ᵐ[μ] poissonKernel x y := by
    filter_upwards with t
    by_cases ht : t ∈ Metric.closedBall x y
    · simpa [g, ht] using one_div_two_mul_le_poissonKernel hypos ht
    · have hnonneg : 0 ≤ poissonKernel x y t := by
        unfold poissonKernel
        exact div_nonneg (le_of_lt hypos) (by positivity)
      simpa [g, ht] using hnonneg
  have hle : ∫ t, g t ∂μ ≤ poissonTransform μ x y := by
    unfold poissonTransform
    exact integral_mono_ae hg hkernel hpoint
  have hconst : ∫ t, g t ∂μ = μ.real (Metric.closedBall x y) * (1 / (2 * y)) := by
    dsimp [g]
    rw [integral_indicator_const (1 / (2 * y)) measurableSet_closedBall]
    simp [smul_eq_mul]
  rw [hconst] at hle
  have hmass : 0 ≤ μ.real (Metric.closedBall x y) := ENNReal.toReal_nonneg
  have hratio : μ.real (Metric.closedBall x y) / (2 * y) ≤ poissonTransform μ x y := by
    calc
      μ.real (Metric.closedBall x y) / (2 * y) =
          μ.real (Metric.closedBall x y) * (1 / (2 * y)) := by ring
      _ ≤ poissonTransform μ x y := hle
  exact hratio

end AndersonAC.Boundary
