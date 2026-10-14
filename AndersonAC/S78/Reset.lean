import AndersonAC.S78.Contraction
import AndersonAC.Blueprint.Interfaces

/-! Compatibility witness for the package type. Blueprint.Interfaces
can import Contraction and use the body below without an import cycle. -/
set_option autoImplicit false

namespace AndersonAC.Blueprint.Packages

theorem reset : ResetInput := by
  intro N F r ρ hρ hball hcontract
  exact AndersonAC.SolS78.fixedPoint_closedBall F r ρ hρ.le hball hcontract


end AndersonAC.Blueprint.Packages

#print axioms AndersonAC.Blueprint.Packages.reset
