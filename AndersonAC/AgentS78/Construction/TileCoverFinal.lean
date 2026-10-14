import AndersonAC.AgentS78.Construction.TileCoverProof
import AndersonAC.AgentS78.Construction.TileCoverPlan
import AndersonAC.AgentS78.Construction.TorusKernel
import AndersonAC.AgentS78.Construction.GridPoincare

/-!
# Unconditional §5 tile covers

`tileCover_proof : ∀ d, TileCoverStatement d` and `tilePlan_exists` provide tile
plans with the `TileGoodCore` cover clauses, tile diameters, and restrictions
(`TileCoverPlan.lean`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

/-- **The §5 tile covers** (05:240–343). -/
theorem tileCover_proof (d : ℕ) : TileCoverStatement d :=
  tileCover_of_parts gridPoincare_proof torusConnected_proof torusMetric_proof d
    (torusShell_proof d) (torusKernel_proof d)

/-- **Tile plans for every box** with the cover clauses of `TileGoodCore`, the tile diameters
of `blockRun_of_runOps` and the restrictions to injective port families. -/
theorem tilePlan_exists (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m n₀ : ℕ) (u : ℝ), 1 ≤ n₀ → n₀ ≤ m → 1 / 4 < u → u ≤ 1 →
      ∃ P : TilePlan d m, P.n₀ = n₀ ∧ P.u = u ∧
        ∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j) :=
  exists_tilePlan (tileCover_proof d)

end AndersonAC.AgentS78
