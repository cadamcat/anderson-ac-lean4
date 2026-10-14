import AndersonAC.AgentS78.Construction.TileCoreAssembly
import AndersonAC.AgentS78.Construction.TileTrialHalt
import AndersonAC.AgentS78.Construction.TileCoreA3
import AndersonAC.AgentS78.Construction.TileCoreA0

/-! Slot recursion and budget-crossing statements for the tile-trial core, together
with their assembly. Each proposition `X` has a proof `X_proof` in its own module. -/

namespace AndersonAC.AgentS78

example : Prop := TileSlotDescriptionStatement
example : Prop := TileSlotLawStatement
example (d : ℕ) (C : ℝ) : Prop := TileMonitorBoundsStatement d C
example (d : ℕ) (C : ℝ) : Prop := TileFailCrossingStatement d C

/-- Assembly: the four pieces give the S45-route contract. -/
example (d : ℕ) (C : ℝ) : TileSlotDescriptionStatement → TileSlotLawStatement →
    TileMonitorBoundsStatement d C → TileFailCrossingStatement d C →
    TileCrossingStatement d C :=
  tileCrossing_of_pieces d C

/-- Whole chain to the first-trial bound (shape of `BlockRun.product_bound`). -/
theorem tile_first_trial_bound_of_pieces (d : ℕ) (C : ℝ) (h0 : TileSlotDescriptionStatement)
    (h1 : TileSlotLawStatement) (h2 : TileMonitorBoundsStatement d C)
    (h3 : TileFailCrossingStatement d C) :
    ∃ c > 0, ∃ N : ℕ, ∀ n₀ ≥ N, ∀ (m : ℕ) (u : ℝ), u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ (P : TilePlan d m), P.n₀ = n₀ → P.u = u →
      ∀ j, n₀ < j → j ≤ m + 1 → ∀ (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ),
      TileOrderSizes P j T M → ∀ x ∈ TileGood C P j T,
      AndersonAC.S2.sourcesLaw (AndersonAC.S78.Torus d m) M (localFirstFail M (tileBlock P j T) x) ≤
        ENNReal.ofReal (AndersonAC.S78.birthBound c j) :=
  tile_first_trial_bound d C (tileTrialBound_of_crossing d C (tileCrossing_of_pieces d C h0 h1 h2 h3))

/-- budget crossing from sweep transfer. -/
example (d : ℕ) (C : ℝ) : TileTransferStatement d C → TileFailCrossingStatement d C :=
  tileFailCrossing_of_transfer d C

/-- Whole chain from the remaining open pieces slot recursion, tile slot law, monitor bounds, sweep transfer. -/
theorem tile_first_trial_bound_of_open (d : ℕ) (C : ℝ) (h0 : TileSlotDescriptionStatement)
    (h1 : TileSlotLawStatement) (h2 : TileMonitorBoundsStatement d C)
    (h3b : TileTransferStatement d C) :
    ∃ c > 0, ∃ N : ℕ, ∀ n₀ ≥ N, ∀ (m : ℕ) (u : ℝ), u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ (P : TilePlan d m), P.n₀ = n₀ → P.u = u →
      ∀ j, n₀ < j → j ≤ m + 1 → ∀ (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ),
      TileOrderSizes P j T M → ∀ x ∈ TileGood C P j T,
      AndersonAC.S2.sourcesLaw (AndersonAC.S78.Torus d m) M (localFirstFail M (tileBlock P j T) x) ≤
        ENNReal.ofReal (AndersonAC.S78.birthBound c j) :=
  tile_first_trial_bound_of_pieces d C h0 h1 h2 (tileFailCrossing_of_transfer d C h3b)

/-- slot recursion, proved. -/
example : TileSlotDescriptionStatement := tileSlotDescription_proof

/-- Whole chain from the remaining open pieces tile slot law, monitor bounds, sweep transfer. -/
theorem tile_first_trial_bound_of_A1_A2_A3b (d : ℕ) (C : ℝ) (h1 : TileSlotLawStatement)
    (h2 : TileMonitorBoundsStatement d C) (h3b : TileTransferStatement d C) :
    ∃ c > 0, ∃ N : ℕ, ∀ n₀ ≥ N, ∀ (m : ℕ) (u : ℝ), u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ (P : TilePlan d m), P.n₀ = n₀ → P.u = u →
      ∀ j, n₀ < j → j ≤ m + 1 → ∀ (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ),
      TileOrderSizes P j T M → ∀ x ∈ TileGood C P j T,
      AndersonAC.S2.sourcesLaw (AndersonAC.S78.Torus d m) M (localFirstFail M (tileBlock P j T) x) ≤
        ENNReal.ofReal (AndersonAC.S78.birthBound c j) :=
  tile_first_trial_bound_of_open d C tileSlotDescription_proof h1 h2 h3b

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.tileSlotDescription_proof
#print axioms AndersonAC.AgentS78.tile_first_trial_bound_of_A1_A2_A3b
#print axioms AndersonAC.AgentS78.tileFailCrossing_of_transfer
#print axioms AndersonAC.AgentS78.tile_first_trial_bound_of_open
#print axioms AndersonAC.AgentS78.tileCrossing_of_pieces
#print axioms AndersonAC.AgentS78.tile_first_trial_bound_of_pieces
