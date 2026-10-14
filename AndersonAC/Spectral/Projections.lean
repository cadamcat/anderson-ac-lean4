import AndersonAC.Spectral.PVM

open MeasureTheory
open scoped InnerProductSpace

namespace AndersonAC.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Borel spectral projection of a bounded self-adjoint operator. For nonmeasurable sets,
this definition returns zero; every Borel set uses the projection from `boundedPVM`. -/
noncomputable def spectralProjection (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (B : Set ℝ) : H →L[ℂ] H := by
  classical
  exact if hB : MeasurableSet B then (TauCeti.BorelCalculus.boundedPVM hT).proj B hB else 0

/-- The spectral projection of a closed interval. -/
noncomputable def chiIcc (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (a b : ℝ) :
    H →L[ℂ] H := spectralProjection T hT (Set.Icc a b)

end AndersonAC.Spectral
