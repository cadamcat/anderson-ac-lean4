import AndersonAC.AgentS78.Construction.FinishClosed
import AndersonAC.AgentS78.Construction.ClearingBoundR

/-! The route R2 certificate input with the proved clearing first-failure bound
`clearingBoundR_proof`. -/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The uniform certificate input from clearing-block measurability and tile-monitor bounds. -/
theorem uniformCertificateInput_closedMA (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedR2T d hd e₂ he₂ hcmeas hA2 (clearingBoundR_proof d hd)

/-- The uniform certificate input from a tile-trial bound, independently of the
form of the tile-monitor bounds. -/
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
