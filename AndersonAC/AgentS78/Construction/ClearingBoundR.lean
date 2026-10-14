import AndersonAC.AgentS78.Construction.ClearingBound
import AndersonAC.AgentS78.Construction.StagePhasePkgOps
import AndersonAC.AgentS78.Construction.ClearingBridge

/-!
# `ClearingBoundR` (the input `hB` of `clearingPhasePackage_of`)

The clearing first-failure bound on `ClearPhaseR … j (rank y)` records, in the exact form of
`ClearingBoundR d` (StagePhasePkgOps.lean), from `clearingBound_clearPhaseR`
(ClearingBound.lean), assuming the sample-by-sample bridge
`ClearingBridgeAtStatement`. The constant `c` does not depend on
`Cb`, and the two record hypotheses of `ClearingBoundR` are not needed (they follow from
`ClearPhaseR` at the scan position `rank y`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **`ClearingBoundR d` from the sample-by-sample bridge.** -/
theorem clearingBoundR_of_bridge (d : ℕ) (hd : 3 ≤ d) (hbr : ∀ m, ClearingBridgeAtStatement d m) :
    ClearingBoundR d := by
  intro cB CB Ctr CA cA PA Cb hcB _ hCtr hCA hcA hPA
  obtain ⟨c, hc, N, hN⟩ := clearingBound_clearPhaseR d hd hbr CA cA PA hCA hcA hPA cB CB hcB Ctr
    (by linarith)
  exact ⟨c, hc, N, fun m n₀ u E ρ M j y x h1 h2 hu hj hjm hx _ _ =>
    hN n₀ m h1 h2 u hu E ρ Cb j hj hjm y M x hx⟩

/-- **`ClearingBoundR d`, unconditional**: the pointwise bridge is
`clearingBridgeAtD_proof` (its `ClearingBridgeAtDStatement` is `ClearingBridgeAtStatement`
verbatim). -/
theorem clearingBoundR_proof (d : ℕ) (hd : 3 ≤ d) : ClearingBoundR d :=
  clearingBoundR_of_bridge d hd (fun m => clearingBridgeAtD_proof d m)

end AndersonAC.AgentS78
