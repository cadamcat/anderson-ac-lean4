import AndersonAC.AgentS78.Construction.ClearingSix
import AndersonAC.AgentS78.Construction.TileDisciplines
import AndersonAC.AgentS78.Construction.TileCoreCheck
import AndersonAC.AgentS78.Construction.TileCoreA3b

/-!
# WP10 construction: the finish line with the proved inputs plugged in (lead, agent-s78con3)

`uniformCertificateInput_of_A1_A2_boxes`: S78.UniformCertificateInput d e₂ from the
clearing-block measurability (muse-s78clear), the C4a pieces A1 (`TileSlotLawStatement`,
muse-s78a1) and A2 (`TileMonitorBoundsStatement`, luna-s78a2), and the kind-split run invariant
packages `BoxInvariantK`. Plugged in: the five tile disciplines (luna-s78tdisc), A0
(`tileSlotDescription_proof`) and A3b (`tileTransfer_proof`, ported to v3.1 by agent-s78a3bv3).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- C4a's one-trial contract from A1 and A2 (A0, A3b proved). -/
theorem tileTrialBound_of_A1_A2 (d : ℕ) (C : ℝ) (hC : 1 ≤ C) (h1 : TileSlotLawStatement)
    (h2 : TileMonitorBoundsStatement d C) : TileTrialBoundStatement d C :=
  tileTrialBound_of_crossing d C (tileCrossing_of_pieces d C tileSlotDescription_proof h1 h2
    (tileFailCrossing_of_transfer d C (tileTransfer_proof d C hC)))

/-- **WP10 finish line, current form.** -/
theorem uniformCertificateInput_of_A1_A2_boxes (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hA1 : TileSlotLawStatement) (hA2 : ∀ C : ℝ, 1 ≤ C → TileMonitorBoundsStatement d C)
    (hbox : ∀ C : ℝ, 1 ≤ C → ∃ Cg : ℝ, 1 ≤ Cg ∧ ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariantK d m n₀ u E Cr cp cg c Cg P)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_boxInvariantsK' d hd e₂ tileMarkingStatement_proof
    tileQueryStatement_proof tilePatternStatement_proof tileAbortStatement_proof
    tileHaltPatternStatement_proof hcmeas
    (fun C hC => tileTrialBound_of_A1_A2 d C hC hA1 (hA2 C hC)) hbox

end AndersonAC.AgentS78
