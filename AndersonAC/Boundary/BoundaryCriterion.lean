import AndersonAC.Boundary.Singular
import AndersonAC.Blueprint.SpectralInputs

/-!
# Finite boundary values exclude singular mass

The bounded-boundary criterion follows from the singular-part divergence result: if the transform
has a finite boundary value throughout a measurable set, the restriction to that set has no
singular part.
-/

open MeasureTheory Filter Complex
open scoped Topology

namespace AndersonAC.Boundary

private theorem borelTransform_eq_resolventTransform (μ : Measure ℝ) :
    AndersonAC.Blueprint.borelTransform μ = MeasureTheory.resolventTransform μ := by
  funext z
  rw [AndersonAC.Blueprint.borelTransform, MeasureTheory.resolventTransform_apply]
  apply integral_congr_ae
  filter_upwards with t
  simp [resolvent, Ring.inverse_eq_inv']

private theorem finiteBoundary_not_singularDivergence (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≤ μ) (x : ℝ) (w : ℂ)
    (hlim : Filter.Tendsto
      (fun y : ℝ => AndersonAC.Blueprint.borelTransform μ
        ((x : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 w))
    (hdiv : Filter.Tendsto
      (fun y : ℝ => (MeasureTheory.resolventTransform ν
        ((x : ℂ) + (y : ℂ) * Complex.I)).im)
      (𝓝[>] 0) atTop) : False := by
  have hlim' : Filter.Tendsto
      (fun y : ℝ => MeasureTheory.resolventTransform μ
        ((x : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 w) := by
    simpa only [borelTransform_eq_resolventTransform] using hlim
  have him : Filter.Tendsto
      (fun y : ℝ => (MeasureTheory.resolventTransform μ
        ((x : ℂ) + (y : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 w.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlim'
  have hlarge : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      (MeasureTheory.resolventTransform ν ((x : ℂ) + (y : ℂ) * Complex.I)).im > w.im + 1 :=
    hdiv.eventually (Ioi_mem_atTop (w.im + 1))
  have hlt : w.im < w.im + 1 := by linarith
  have hsmall : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      (MeasureTheory.resolventTransform μ ((x : ℂ) + (y : ℂ) * Complex.I)).im < w.im + 1 :=
    him.eventually (Iio_mem_nhds hlt)
  have hcontra : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      (MeasureTheory.resolventTransform ν ((x : ℂ) + (y : ℂ) * Complex.I)).im >
          w.im + 1 ∧
        (MeasureTheory.resolventTransform μ ((x : ℂ) + (y : ℂ) * Complex.I)).im <
          w.im + 1 ∧ 0 < y := by
    filter_upwards [hlarge, hsmall, self_mem_nhdsWithin] with y hlarge hsmall hy
    exact ⟨hlarge, hsmall, Set.mem_Ioi.mp hy⟩
  obtain ⟨y, ⟨hlarge, hsmall, hy⟩⟩ := hcontra.exists
  have hmono := im_resolventTransform_mono hνμ x y hy
  exact (not_lt_of_ge (le_of_lt hsmall)) (lt_of_lt_of_le hlarge hmono)

/-- A finite vertical boundary limit on every point of a measurable set forces the restricted
measure to be absolutely continuous. -/
theorem boundedBoundaryCriterion_proof :
    AndersonAC.Blueprint.BoundedBoundaryCriterion := by
  intro μ hμ S hS hfinite
  let ν : Measure ℝ := μ.restrict S
  have hνμ : ν ≤ μ := by
    dsimp [ν]
    exact Measure.restrict_le_self
  letI : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνμ
  let σ : Measure ℝ := ν.singularPart volume
  have hσν : σ ≤ ν := by
    dsimp [σ]
    exact Measure.singularPart_le ν volume
  letI : IsFiniteMeasure σ := isFiniteMeasure_of_le ν hσν
  have hσμ : σ ≤ μ := hσν.trans hνμ
  have hνmem : ∀ᵐ x : ℝ ∂ν, x ∈ S := by
    dsimp [ν]
    exact ae_restrict_mem hS
  have hσmem : ∀ᵐ x ∂σ, x ∈ S := hνmem.filter_mono (ae_mono hσν)
  have hdiv : ∀ᵐ x : ℝ ∂σ,
      Filter.Tendsto
        (fun y : ℝ => (MeasureTheory.resolventTransform σ
          ((x : ℂ) + (y : ℂ) * Complex.I)).im)
        (𝓝[>] 0) atTop := by
    simpa [σ] using singularPart_im_resolventTransform_tendsto_atTop ν
  by_cases hσzero : σ = 0
  · have hac : ν ≪ volume := (Measure.singularPart_eq_zero ν volume).mp hσzero
    simpa [ν] using hac
  · have hσS : σ S ≠ 0 := by
      intro hSzero
      have hrestrictzero : σ.restrict S = 0 := Measure.restrict_eq_zero.mpr hSzero
      have hself : σ.restrict S = σ := Measure.restrict_eq_self_of_ae_mem hσmem
      apply hσzero
      rw [← hself]
      exact hrestrictzero
    have hdivS : ∀ᵐ x : ℝ ∂σ.restrict S,
        Filter.Tendsto
          (fun y : ℝ => (MeasureTheory.resolventTransform σ
            ((x : ℂ) + (y : ℂ) * Complex.I)).im)
          (𝓝[>] 0) atTop := ae_restrict_of_ae hdiv
    obtain ⟨x, hxS, hxdiv⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hσS hdivS
    obtain ⟨w, hwlim⟩ := hfinite x hxS
    exfalso
    exact finiteBoundary_not_singularDivergence μ σ hσμ x w
      (by simpa [AndersonAC.Blueprint.HasBoundary] using hwlim) hxdiv

end AndersonAC.Boundary
