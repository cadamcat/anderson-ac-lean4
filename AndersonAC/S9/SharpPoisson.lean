import AndersonAC.S9Fin.PoissonDomination
import AndersonAC.S9.HelperStatements

/-! Sharp Poisson domination for finite-volume spectral measures, expressed as
the generic `BoundedPoissonMeasureInput`. -/

namespace AndersonAC.SolS9

theorem boundedPoisson_from_finite : BoundedPoissonMeasureInput :=
  finitePoissonDomination_proof

end AndersonAC.SolS9
