import AndersonAC.AgentS78.Construction.BoxPhasesSweepEnd
import AndersonAC.AgentS78.Construction.BoxPhasesTrue
import AndersonAC.AgentS78.Construction.BoxPhasesTerminal
import AndersonAC.AgentS78.Construction.Finish

/-!
# Uniform certificate input from the run invariant

`uniformCertificateInput_of_phases` assembles `S78.UniformCertificateInput d e₂` for
`d ≥ 3` and `e₂ ∈ (0, 1/100)` from clearing-block measurability, tile bounds, and the
phase contracts of `boxInvariantK_of_phases'`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem uniformCertificateInput_of_phases (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hCT : ActiveCTStatement d) (hbridge : StartBridgeStatement)
    (hT : SweepTransportStatement d) (hTCT : TerminalCTStatement d)
    (hclr : ClearingPhasePackage d)
    (hRTV : RunTVClosureStatement d) (hAT : RunAllTerminalStatement d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_A1_A2_boxes d hd e₂ hcmeas hA1 hA2
    (boxInvariantK_of_phases' d hd e₂ he₂ hCT hbridge hT hTCT hclr hRTV hAT)

/-- **certificate construction per-box packages with the final installed values reduced** to the tile and clearing
true-value disciplines and the terminal completeness at the end. -/
theorem boxInvariantK_of_phases'' (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hCT : ActiveCTStatement d) (hbridge : StartBridgeStatement)
    (hT : SweepTransportStatement d) (hTCT : TerminalCTStatement d)
    (hclr : ClearingPhasePackage d)
    (hTT : TileTrueValuesStatement) (hCTV : ClearingTrueValuesStatement)
    (hAT : RunAllTerminalStatement d) :
    ∀ C : ℝ, 1 ≤ C → ∃ Cg : ℝ, 1 ≤ Cg ∧ ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariantK d m n₀ u E Cr cp cg c Cg P) :=
  boxInvariantK_of_phases' d hd e₂ he₂ hCT hbridge hT hTCT hclr
    (runTVClosure_of_parts hTT hCTV) hAT

/-- Uniform certificate input with the run invariant assembled. -/
theorem uniformCertificateInput_of_phases' (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hCT : ActiveCTStatement d) (hbridge : StartBridgeStatement)
    (hT : SweepTransportStatement d) (hTCT : TerminalCTStatement d)
    (hclr : ClearingPhasePackage d)
    (hTT : TileTrueValuesStatement) (hCTV : ClearingTrueValuesStatement)
    (hAT : RunAllTerminalStatement d) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_A1_A2_boxes d hd e₂ hcmeas hA1 hA2
    (boxInvariantK_of_phases'' d hd e₂ he₂ hCT hbridge hT hTCT hclr hTT hCTV hAT)

/-- Per-box invariant packages assembled from the phase and true-value hypotheses. -/
theorem boxInvariantK_of_contracts (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hCT : ActiveCTStatement d) (hbridge : StartBridgeStatement)
    (hT : SweepTransportStatement d) (hTCT : TerminalCTStatement d)
    (hclr : ClearingPhasePackage d)
    (hTT : TileTrueValuesStatement) (hCTV : ClearingTrueValuesStatement) :
    ∀ C : ℝ, 1 ≤ C → ∃ Cg : ℝ, 1 ≤ Cg ∧ ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariantK d m n₀ u E Cr cp cg c Cg P) :=
  boxInvariantK_of_phases'' d hd e₂ he₂ hCT hbridge hT hTCT hclr hTT hCTV
    runAllTerminal_proof

/-- Uniform certificate input from the assembled per-box invariants. -/
theorem uniformCertificateInput_of_contracts (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hCT : ActiveCTStatement d) (hbridge : StartBridgeStatement)
    (hT : SweepTransportStatement d) (hTCT : TerminalCTStatement d)
    (hclr : ClearingPhasePackage d)
    (hTT : TileTrueValuesStatement) (hCTV : ClearingTrueValuesStatement) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_A1_A2_boxes d hd e₂ hcmeas hA1 hA2
    (boxInvariantK_of_contracts d hd e₂ he₂ hCT hbridge hT hTCT hclr hTT hCTV)

end AndersonAC.AgentS78
