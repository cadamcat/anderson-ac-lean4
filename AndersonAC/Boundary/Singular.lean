import AndersonAC.Boundary.Poisson

/-!
# Divergence of the Poisson transform on the singular part

The Besicovitch differentiation theorem, applied with Lebesgue measure relative to the singular
part, gives zero density for Lebesgue measure at singular-almost-every point. Inverting the local
measure ratio gives infinite symmetric density for the singular measure. The Poisson-kernel lower
bound from `Poisson.lean` then gives the boundary divergence statement.
-/

open MeasureTheory Filter
open scoped Topology

namespace AndersonAC.Boundary

private theorem ae_singularPart_ballDensity_tendsto_atTop (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    ∀ᵐ (x : ℝ) ∂(μ.singularPart (volume : Measure ℝ)),
      Filter.Tendsto
        (fun r : ℝ => (μ.singularPart volume).real (Metric.closedBall x r) / (2 * r))
        (𝓝[>] 0) atTop := by
  let ν : Measure ℝ := μ.singularPart volume
  have hνle : ν ≤ μ := by
    dsimp [ν]
    exact Measure.singularPart_le μ volume
  haveI : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνle
  have hsing : ν ⟂ₘ volume := by
    dsimp [ν]
    exact Measure.mutuallySingular_singularPart μ volume
  have hzero : volume.rnDeriv ν =ᵐ[ν] 0 :=
    hsing.symm.rnDeriv_ae_eq_zero
  have hdiff : ∀ᵐ x ∂ν,
      Filter.Tendsto
        (fun r : ℝ => volume (Metric.closedBall x r) / ν (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (volume.rnDeriv ν x)) :=
    Besicovitch.ae_tendsto_rnDeriv volume ν
  filter_upwards [hzero, hdiff] with x hxzero hxratio
  have hxratio0 : Filter.Tendsto
      (fun r : ℝ => volume (Metric.closedBall x r) / ν (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 (0 : ENNReal)) := by
    simpa [hxzero, Pi.zero_apply] using hxratio
  let ratio : ℝ → ENNReal := fun r =>
    volume (Metric.closedBall x r) / ν (Metric.closedBall x r)
  have hinv : Filter.Tendsto (fun r => (ratio r)⁻¹) (𝓝[>] 0)
      (𝓝 (⊤ : ENNReal)) := by
    simpa [ratio] using (tendsto_inv_iff).2 hxratio0
  have hvol_top (r : ℝ) : volume (Metric.closedBall x r) ≠ (⊤ : ENNReal) := by
    rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top
  have hvol_pos : ∀ᶠ r in 𝓝[>] 0, volume (Metric.closedBall x r) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : 0 < r := Set.mem_Ioi.mp hr
    rw [Real.volume_closedBall]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hratio_eq : (fun r => (ratio r)⁻¹) =ᶠ[𝓝[>] 0]
      fun r => ν (Metric.closedBall x r) / volume (Metric.closedBall x r) := by
    filter_upwards [hvol_pos] with r hvol
    dsimp [ratio]
    rw [ENNReal.inv_div (Or.inr (hvol_top r)) (Or.inr hvol)]
  have hdensity : Filter.Tendsto
      (fun r => ν (Metric.closedBall x r) / volume (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 (⊤ : ENNReal)) := Filter.Tendsto.congr' hratio_eq hinv
  let density : ℝ → ENNReal := fun r =>
    if 0 < r then ν (Metric.closedBall x r) / volume (Metric.closedBall x r) else 0
  have hdensity' : Filter.Tendsto density (𝓝[>] 0) (𝓝 (⊤ : ENNReal)) := by
    apply (tendsto_congr' ?_).2 hdensity
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp [density, Set.mem_Ioi.mp hr]
  have hdensity_finite : ∀ r, density r ≠ (⊤ : ENNReal) := by
    intro r
    by_cases hr : 0 < r
    · have hvol : volume (Metric.closedBall x r) ≠ 0 := by
        rw [Real.volume_closedBall]
        exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
      simpa [density, hr] using ENNReal.div_ne_top (measure_ne_top ν _) hvol
    · simp [density, hr]
  have hdensity_real : Filter.Tendsto (fun r => (density r).toReal)
      (𝓝[>] 0) atTop := by
    apply tendsto_atTop.2
    intro C
    let B : ℝ := max C 0 + 1
    have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
    have hCB : C ≤ B := by dsimp [B]; linarith [le_max_left C 0]
    have hIoi : Set.Ioi (ENNReal.ofReal B) ∈ 𝓝 (⊤ : ENNReal) :=
      Ioi_mem_nhds ENNReal.ofReal_lt_top
    filter_upwards [hdensity'.eventually hIoi] with r hr
    have htoReal : B ≤ (density r).toReal := by
      have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (hdensity_finite r)).2 hr
      rw [ENNReal.toReal_ofReal hB_nonneg] at h
      exact h.le
    exact hCB.trans htoReal
  have hdensity_real_eq : (fun r => (density r).toReal) =ᶠ[𝓝[>] 0]
      fun r => ν.real (Metric.closedBall x r) / (2 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : 0 < r := Set.mem_Ioi.mp hr
    simp [density, hrpos, Measure.real_def, ENNReal.toReal_div]
    rw [ENNReal.toReal_ofReal (le_of_lt hrpos)]
  have hfinal := Filter.Tendsto.congr' hdensity_real_eq hdensity_real
  simpa [ν] using hfinal

/-- For almost every point with respect to the singular part of a finite measure, the imaginary
part of its Borel transform diverges to `+∞` as the spectral height decreases to zero. This is the
singular-support conclusion of Teschl, Theorem 3.23 / Corollary 3.24.
-/
theorem singularPart_im_resolventTransform_tendsto_atTop (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    ∀ᵐ (x : ℝ) ∂(μ.singularPart (volume : Measure ℝ)),
      Filter.Tendsto
        (fun y : ℝ =>
          (MeasureTheory.resolventTransform (μ.singularPart (volume : Measure ℝ))
            ((x : ℂ) + (y : ℂ) * Complex.I)).im)
        (𝓝[>] 0) atTop := by
  have hdensity := ae_singularPart_ballDensity_tendsto_atTop μ
  filter_upwards [hdensity] with x hx
  have hpoisson := poissonTransform_tendsto_atTop_of_ballDensity
    (μ.singularPart (volume : Measure ℝ)) x hx
  apply Filter.Tendsto.congr' ?_ hpoisson
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa using (im_resolventTransform_eq_poissonTransform
    (μ.singularPart (volume : Measure ℝ)) x y (Set.mem_Ioi.mp hy)).symm

end AndersonAC.Boundary
