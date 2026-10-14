import AndersonAC.AgentS78.Construction.BoxClosed
import AndersonAC.AgentS78.Construction.ClearingTrueValues
import AndersonAC.AgentS78.Construction.TileCoreA1
import AndersonAC.AgentS78.Construction.StagePhasePkgClosed
import AndersonAC.AgentS78.Construction.TileTrueValues

/-! WP10 finish line, current closed form (lead, agent-s78con4): `uniformCertificateInput_closedTV`
with `clearingTrueValues_proof` (agent-s78runinv) plugged in. -/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **WP10 finish line.** Open: clearing-block measurability (muse-s78clear), A1 (muse-s78a1),
A2 (luna-s78a2), the clearing phase package (agent-s78phase2: hB clearing bound, hP DONE physical
identity), the tile true values (luna-s78truev). -/
theorem uniformCertificateInput_closed5 (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hclr : ClearingPhasePackage d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedTV d hd e₂ he₂ hcmeas hA1 hA2 hclr hTT clearingTrueValues_proof

/-- **WP10 finish line** with A1 (`tileSlotLaw_proof`, muse-s78a1) plugged in. Open: clearing-block
measurability (muse-s78clear), A2 (luna-s78a2), the clearing phase package (agent-s78phase2), the
tile true values (agent-s78runinv). -/
theorem uniformCertificateInput_closed4 (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hclr : ClearingPhasePackage d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed5 d hd e₂ he₂ hcmeas tileSlotLaw_proof hA2 hclr hTT

/-- **WP10 finish line** with the clearing phase package assembled (agent-s78phase2,
`clearingPhasePackage_closed`). Open: clearing-block measurability (muse-s78clear), A2 (luna-s78a2),
the clearing first-failure bound `ClearingBoundR` (agent-s78clrbound + agent-s78cbridge), the DONE
physical identity `ClearingDonePhysHyp` (DISPATCH A+B), the tile true values (agent-s78runinv). -/
theorem uniformCertificateInput_closedB (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) (_hP : ClearingDonePhysHyp d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed4 d hd e₂ he₂ hcmeas hA2 (clearingPhasePackage_closed d hd hB) hTT

/-- **WP10 finish line, route R2** (agent-s78phase2: the DONE physical identity holds off the
null `exceptionalSet`, `clearingDonePhysZ_proof`; the run invariant is kept off it jointly with
the true installed values, agent-s78r2chain). Open: clearing-block measurability
(muse-s78clear), A2 (luna-s78a2), the clearing first-failure bound `ClearingBoundR`
(agent-s78clrbound + agent-s78cbridge), the tile true values (agent-s78runinv). -/
theorem uniformCertificateInput_closedR2 (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) (hTT : TileTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closed4 d hd e₂ he₂ hcmeas hA2 (clearingPhasePackage_closed d hd hB) hTT

/-- **WP10 finish line** with the tile true values (`tileTrueValues_proof`, agent-s78runinv /
luna-s78truev) plugged in. Open: clearing-block measurability (muse-s78clear), A2 (luna-s78a2),
`ClearingBoundR` (agent-s78clrbound + agent-s78cbridge), `ClearingDonePhysHyp` (to be replaced by
route R2: agent-s78r2chain + agent-s78phase2). -/
theorem uniformCertificateInput_closedT (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) (hP : ClearingDonePhysHyp d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedB d hd e₂ he₂ hcmeas hA2 hB hP tileTrueValues_proof

/-- **WP10 finish line, route R2 with the tile true values** (`tileTrueValues_proof`). Open:
clearing-block measurability (muse-s78clear), A2 (luna-s78a2), the clearing first-failure bound
`ClearingBoundR` (agent-s78clrbound + agent-s78cbridge). -/
theorem uniformCertificateInput_closedR2T (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hB : ClearingBoundR d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_closedR2 d hd e₂ he₂ hcmeas hA2 hB tileTrueValues_proof

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedR2T
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedR2
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedT
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closedB
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closed5
#print axioms AndersonAC.AgentS78.uniformCertificateInput_closed4
