import AndersonAC.S9.HelperStatements
import AndersonAC.Spectral.SpectralProof
import AndersonAC.Bridge.MomentDeterminacy

/-! The frozen averaging contract accepts an arbitrary supplied
SpectralResolution. Compact moment determinacy identifies its scalar
measure with the constructed WP01 resolution. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9

theorem ResolutionTransformInput_proof : ResolutionTransformInput := by
  intro d T hT S v z hz
  obtain ⟨R⟩ := AndersonAC.Blueprint.Packages.spectral d T hT
  letI : IsFiniteMeasure (S.vectorMeasure v) := S.finite_vectorMeasure v
  letI : IsFiniteMeasure (R.spectral.vectorMeasure v) := R.spectral.finite_vectorMeasure v
  have hmeasure : S.vectorMeasure v = R.spectral.vectorMeasure v :=
    AndersonAC.LunaBridge.measure_eq_of_moments_eq_of_supported (norm_nonneg T)
      (S.vectorMeasure_supported v) (R.spectral.vectorMeasure_supported v) (by
        intro n
        rw [S.vectorMeasure_moments, R.spectral.vectorMeasure_moments])
  rw [hmeasure]
  exact R.resolvent_eq v z hz

end AndersonAC.SolS9
