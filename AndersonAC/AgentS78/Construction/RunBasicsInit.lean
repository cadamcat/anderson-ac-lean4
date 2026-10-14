import AndersonAC.AgentS78.Construction.RunBasics
import AndersonAC.AgentS78.Construction.InitialRecord
import AndersonAC.AgentS78.Construction.TilePhaseComplete

/-!
# `RunBasics` without hypotheses; the initial record (hInv0)

 .
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

/-- **`hInv0` for `RunBasics`**: the initial record (no terminal, no pending site, empty
prefixes, stage-start lift of the first sweep). -/
theorem initialRecord_runBasics (P : TilePlan d m) (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (θ t : ℝ)
    (lab : BirthLabel (Torus d m)) : initialRecord n₀ u E ρ θ t lab ∈ RunBasics P 0 :=
  runBasics_zero_of_start P θ t _ (fun i _ => Finset.notMem_empty i) rfl (fun _ _ => rfl)

/-- The completeness input of `runBasics_closed`: `tileComplete_proof`. -/
theorem runTileComplete : RunTileCompleteStatement :=
  fun d m P j T M x k ω h1 h2 h3 h4 h5 => tileComplete_proof d m P j T M x k ω h1 h2 h3 h4 h5

/-- **`RunBasics` is closed under every block of the schedule** (unconditional; the `hInv` of
`blockRun_of_runOps` for `Inv = RunBasics P` and `clr = fun j y => clearingBlock n₀ j u y`). -/
theorem runBasics_closed' (P : TilePlan d m) (n₀ : ℕ) (u : ℝ) (ts₀ : TileScratch d m)
    (cl₀ : ClearScratch d m) :
    ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ RunBasics P n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n).halted
        (localState (tileOrderSize P)
          (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n) x k' ω) =
            false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n).halted
        (localState (tileOrderSize P)
          (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n) x k ω) =
            true →
      (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n).exit
        (localState (tileOrderSize P)
          (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n) x k ω) ∈
        RunBasics P (n + 1) :=
  runBasics_closed runTileComplete P n₀ u ts₀ cl₀

end AndersonAC.AgentS78
