import AndersonAC.AgentS78.Construction.BoxPhasesFinish
import AndersonAC.AgentS78.Construction.SweepTransport
import AndersonAC.AgentS78.Construction.TileStartBridge
import AndersonAC.AgentS78.Construction.ActiveCTProof

/-!
# Uniform certificate input from phase contracts

`boxInvariantK_closed` and `uniformCertificateInput_closed` assemble the stage-start
bridge, sweep transport, final sweep, and phase hypotheses into a uniform certificate
input.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem startBridge_proof : StartBridgeStatement :=
  fun C P j z h1 h2 => startClauses_of_live C P j z h1 h2

/-- Uniform certificate input from the phase contracts. -/
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

/-- Uniform certificate input with the active and terminal Combes–Thomas bounds proved. -/
theorem uniformCertificateInput_closedCT (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hclr : ClearingPhasePackage d) (hRTV : RunTVClosureStatement d) (hAT : RunAllTerminalStatement d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed d hd e₂ he₂ hcmeas hA1 hA2 (activeCT_proof d hd)
    (terminalCT_proof d) hclr hRTV hAT

/-- Uniform certificate input with the run true values obtained from the tile and
clearing true-value disciplines. -/
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
