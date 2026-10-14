import AndersonAC.AgentS78.Construction.StagePhasePkg
import AndersonAC.AgentS78.Construction.StagePhaseDoneAnalytic

/-!
# The clearing-phase package with the analytic DONE statement discharged. `clearingPhasePackage_closed`: `ClearingPhasePackage d` from the clearing bound
`hB` only (`clearingDoneAnalytic_proof`, the DONE physical identity off the
exceptional set is `clearingDonePhysZ_proof`, route R2).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

theorem clearingPhasePackage_closed (d : ℕ) (hd : 3 ≤ d) (hB : ClearingBoundR d) :
    ClearingPhasePackage d :=
  clearingPhasePackage_of d hd (clearingDoneAnalytic_proof d hd) hB

end AndersonAC.AgentS78
