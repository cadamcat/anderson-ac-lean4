import AndersonAC.AgentS78.Construction.FinishClosed
import AndersonAC.AgentS78.Construction.ClearingBoundR

/-! WP10 finish line, current closed form (lead, agent-s78con4): `uniformCertificateInput_closedR2T`
(route R2, agent-s78phase2 + agent-s78r2chain) with the clearing first-failure bound
`clearingBoundR_proof` (agent-s78clrbound, via agent-s78cbridge's pointwise bridge) plugged in. -/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **WP10 finish line.** Open: clearing-block measurability (muse-s78clear) and A2 (luna-s78a2). -/
theorem uniformCertificateInput_closedMA (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedR2T d hd e₂ he₂ hcmeas hA2 (clearingBoundR_proof d hd)

/-- **WP10 finish line at the tile-trial level** (independent of the form of A2): open are the
clearing-block measurability (muse-s78clear) and the C4a one-trial contract
`∀ C ≥ 1, TileTrialBoundStatement d C`, which A1 (proved) and A2 give
(`tileTrialBound_of_A1_A2`, or `tileTrialBound_of_crossing ∘ tileCrossing_of_pieces2` for the
approved `TileMonitorBoundsStatement2`, luna-s78a2). -/
theorem uniformCertificateInput_closedMT (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hTTB : ∀ C : ℝ, 1 ≤ C → TileTrialBoundStatement d C) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_boxInvariantsK' d hd e₂ tileMarkingStatement_proof
    tileQueryStatement_proof tilePatternStatement_proof tileAbortStatement_proof
    tileHaltPatternStatement_proof hcmeas hTTB
    (boxInvariantK_of_contracts d hd e₂ he₂ (activeCT_proof d hd) startBridge_proof
      (sweepTransport_proof d) (terminalCT_proof d)
      (clearingPhasePackage_closed d hd (clearingBoundR_proof d hd)) tileTrueValues_proof
      clearingTrueValues_proof)

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedMA
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedMT
