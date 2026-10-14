import AndersonAC.AgentS78.Construction.BoxPhasesFinish
import AndersonAC.AgentS78.Construction.SweepTransport
import AndersonAC.AgentS78.Construction.TileStartBridge
import AndersonAC.AgentS78.Construction.ActiveCTProof

/-!
# WP10 finish line with the proved phase contracts plugged in (lead, agent-s78con4)

`boxInvariantK_closed` / `uniformCertificateInput_closed`: agent-s78box's assembly with the stage-start
bridge (`startClauses_of_live`, luna-s78sbridge), the sweep transport
(`sweepTransport_proof`, agent-s78stransp) and the final sweep (`finalSweep_closed`, inside
`boxInvariantK_of_phases`) discharged. Open: ActiveCT, TerminalCT (agent-s78ct), the clearing
phase package, the run true values, and the finish-line inputs (clearing-block measurability,
A1, A2).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem startBridge_proof : StartBridgeStatement :=
  fun C P j z h1 h2 => startClauses_of_live C P j z h1 h2

/-- **WP10 finish line, closed form.** -/
theorem uniformCertificateInput_closed (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hCT : ActiveCTStatement d) (hTCT : TerminalCTStatement d)
    (hclr : ClearingPhasePackage d) (hRTV : RunTVClosureStatement d) (hAT : RunAllTerminalStatement d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_phases d hd e₂ he₂ hcmeas hA1 hA2 hCT startBridge_proof
    (sweepTransport_proof d) hTCT hclr hRTV hAT

/-- **WP10 finish line, closed form with Combes–Thomas** (ActiveCT, TerminalCT: luna-s78actct /
agent-s78ct). Open: clearing-block measurability, A1, A2, the clearing phase package and the run
true values. -/
theorem uniformCertificateInput_closedCT (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hclr : ClearingPhasePackage d) (hRTV : RunTVClosureStatement d) (hAT : RunAllTerminalStatement d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed d hd e₂ he₂ hcmeas hA1 hA2 (activeCT_proof d hd)
    (terminalCT_proof d) hclr hRTV hAT

/-- **WP10 finish line, current closed form** (agent-s78box's reduction of the run true values
to the tile and clearing true-value disciplines plugged in, `runAllTerminal_proof`). Open:
clearing-block measurability, A1, A2, the clearing phase package, TileTrueValues
(luna-s78truev), ClearingTrueValues. -/
theorem uniformCertificateInput_closedTV (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hclr : ClearingPhasePackage d) (hTT : TileTrueValuesStatement)
    (hCTV : ClearingTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_contracts d hd e₂ he₂ hcmeas hA1 hA2 (activeCT_proof d hd)
    startBridge_proof (sweepTransport_proof d) (terminalCT_proof d) hclr hTT hCTV

end AndersonAC.AgentS78
