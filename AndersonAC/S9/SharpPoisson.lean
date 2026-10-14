import AndersonAC.S9Fin.PoissonDomination
import AndersonAC.S9.HelperStatements

/-! The finite lane copied the checked sharp Poisson proof into its own
module, under the original helper namespace. Importing both copies would
conflict. Its export is the same generic measure theorem; this adapter
avoids loading the duplicate standalone module. -/

namespace AndersonAC.SolS9

theorem boundedPoisson_from_finite : BoundedPoissonMeasureInput :=
  finitePoissonDomination_proof

end AndersonAC.SolS9
