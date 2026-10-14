import Mathlib

/-!
General polar integration for the shell and patch arguments in §3.

The `polar_lintegral` proof is adapted from OpenAI's Apache-2.0 library,
openai/math, OAI/Probability/Perceptron/Variational/NormSquareBand.lean,
lines 281–306. That module has no built olean in the shared dependency set;
this standalone helper uses the existing Mathlib theorem directly and does
not import or rebuild that OAI module. Source license: Apache-2.0.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace AndersonAC.S3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem polar_lintegral (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ u : Metric.sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
        f ((r : ℝ) • (u : E)) ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂μ.toSphere := by
  let h := homeomorphUnitSphereProd E
  let F : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun p => f ((p.2 : ℝ) • (p.1 : E))
  have hF : Measurable F := hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)
  calc
    _ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), f (x : E) ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p, F p ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      convert (μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp hF) using 1
      apply lintegral_congr
      intro x
      change f (x : E) = f ((h x).2.val • (h x).1.val)
      have he := congrArg Subtype.val (h.symm_apply_apply x)
      exact congrArg f he.symm
    _ = _ := lintegral_prod _ hF.aemeasurable

end AndersonAC.S3
