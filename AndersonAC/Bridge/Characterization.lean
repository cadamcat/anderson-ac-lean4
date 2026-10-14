import AndersonAC.Bridge.MomentDeterminacy

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal lp Topology
open AndersonAC.Blueprint AndersonChallenge

namespace AndersonAC.LunaBridge

variable {d : ℕ} {T : Operator d}

/-- Every OAI vector measure satisfies the challenge's moment characterization. -/
theorem vectorMeasure_isSpectralMeasure (S : SpectralResolution T) (v : StateSpace d) :
    IsSpectralMeasure T v (S.vectorMeasure v) := by
  refine ⟨S.finite_vectorMeasure v, fun k => ⟨?_, ?_⟩⟩
  · haveI := S.finite_vectorMeasure v
    exact integrable_pow_of_supported (norm_nonneg _) (S.vectorMeasure_supported v) k
  · exact S.vectorMeasure_moments v k

/-- Any measure satisfying the challenge's moments coincides with the OAI vector measure.
Both are finite, supported in `[-‖T‖, ‖T‖]`, and share all moments. -/
theorem spectralMeasure_eq_vectorMeasure (S : SpectralResolution T) (v : StateSpace d)
    {μ : Measure ℝ} (hμ : IsSpectralMeasure T v μ) :
    μ = S.vectorMeasure v := by
  haveI := hμ.1
  haveI := S.finite_vectorMeasure v
  apply measure_eq_of_moments_eq_of_supported (norm_nonneg _)
    (spectralMeasure_supported v hμ) (S.vectorMeasure_supported v)
  intro k
  rw [(hμ.2 k).2, S.vectorMeasure_moments v k]

/-- Characterization of spectral measures: for any spectral resolution, the challenge's
`IsSpectralMeasure` holds exactly for its vector measures. -/
theorem isSpectralMeasure_iff (S : SpectralResolution T) (v : StateSpace d)
    (μ : Measure ℝ) : IsSpectralMeasure T v μ ↔ μ = S.vectorMeasure v := by
  constructor
  · exact spectralMeasure_eq_vectorMeasure S v
  · intro h
    rw [h]
    exact vectorMeasure_isSpectralMeasure S v

/-- Vector measures of any two spectral resolutions of the same operator coincide. -/
theorem vectorMeasure_unique (S₁ S₂ : SpectralResolution T) (v : StateSpace d) :
    S₁.vectorMeasure v = S₂.vectorMeasure v :=
  spectralMeasure_eq_vectorMeasure S₂ v (vectorMeasure_isSpectralMeasure S₁ v)

end AndersonAC.LunaBridge
