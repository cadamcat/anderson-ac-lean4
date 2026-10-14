import AndersonAC.AgentS78.Construction.StagePhaseDoneDecay

/-!
# The analytic DONE statement

agent-s78donea. `clearingDoneAnalytic_proof : ClearingDoneAnalyticStatement d` (d ≥ 3), from the
Combes–Thomas bound (StagePhaseDoneCT), the heat/core split at the core-phase snapshot
(StagePhaseDoneParts), the core completion (StagePhaseDoneCore) and the decay
(StagePhaseDoneDecay).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

/-- **The analytic part of the DONE step facts** (07-assembly.tex:390–433). -/
theorem clearingDoneAnalytic_proof (d : ℕ) (hd : 3 ≤ d) : ClearingDoneAnalyticStatement d :=
  DoneA.clearingDoneAnalytic_of_parts hd (DoneA.doneCore_proof d) (DoneA.doneDecay_proof d)

end AndersonAC.AgentS78
