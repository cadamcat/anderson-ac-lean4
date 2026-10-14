import AndersonAC.AgentS78.Construction.ClearingSix
import AndersonAC.AgentS78.Construction.TileDisciplines
import AndersonAC.AgentS78.Construction.TileCoreCheck
import AndersonAC.AgentS78.Construction.TileCoreA3b

/-!
# Certificate input from tile and run hypotheses

`uniformCertificateInput_of_A1_A2_boxes` assembles `S78.UniformCertificateInput d e₂`
from clearing-block measurability, the tile slot law, monitor bounds, and the kind-split
`BoxInvariantK` packages. The tile disciplines, slot recursion, and sweep transfer
are supplied by their proofs.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Tile-trial bound from the tile slot law and monitor bounds. -/
theorem tileTrialBound_of_A1_A2 (d : ℕ) (C : ℝ) (hC : 1 ≤ C) (h1 : TileSlotLawStatement)
    (h2 : TileMonitorBoundsStatement d C) : TileTrialBoundStatement d C :=
  tileTrialBound_of_crossing d C (tileCrossing_of_pieces d C tileSlotDescription_proof h1 h2
    (tileFailCrossing_of_transfer d C (tileTransfer_proof d C hC)))

/-- Uniform certificate input from the assembled box invariants. -/
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
