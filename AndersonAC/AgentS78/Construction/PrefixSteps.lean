import AndersonAC.AgentS78.StageStep
import AndersonAC.AgentS78.Construction.PrefixInduction

/-!
# WP10 construction: a history prefix from its stage steps

`prefix_of_steps` is `pathwise_of_steps` (StageStep.lean) for the stages `n₀ ≤ n ≤ K`: the
stage endpoints up to `K`, one `StageStep` per stage `n < K` (sweep, committed clearings,
reset: `stage_step_of_sections`) and the boundary facts at each stage `n ≤ K` give a
`PrefixStageInputs` with constant `8C+4`. With `PrefixStageBoundsStatement` this yields the
stage bounds at the current stage boundary of the run.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **`PrefixStageInputs` from the per-stage section conclusions.** -/
def prefix_of_steps {d m n₀ K : ℕ} {u C : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hC : 1 ≤ C)
    (hn₀ : 1 ≤ n₀) (hK : K ≤ m) (state : ℕ → Endpoint (Torus d m)) (r : ℕ → Torus d m → ℂ)
    (hsmall : C * stageScale u n₀ m ^ (0.10 * delta) ≤ 1 / 4)
    (step : ∀ n, n₀ ≤ n → n < K → StageStep d m C (stageScale u n m) (stageScale u (n + 1) m)
      (state n) (state (n + 1)) (r n) (r (n + 1)))
    (physical : ∀ n, n₀ ≤ n → n ≤ K → IsDampedEndpoint (state n) (r n) (stageScale u n m))
    (reset : ∀ n, n₀ ≤ n → n ≤ K → ∀ i ∈ (state n).active, (state n).g i i = r n i)
    (rows : ∀ n, n₀ ≤ n → n ≤ K → ∀ i,
      rowFour (normalizedInverse (state n) (stageScale u n m)) i ≤ stageScale u n m ^ (1 + delta))
    (kernels : ∀ n, n₀ ≤ n → n ≤ K →
      constantKernel (state n).active (endpointEnergy (state n) (r n) (stageScale u n m)))
    (counts : ∀ n, n₀ ≤ n → n ≤ K → Fintype.card (Torus d m) ≤ 2 * (state n).active.card)
    (metrics : ∀ n, n₀ ≤ n → n ≤ K → ∀ x y,
      physicalDistance d m x y / 2 - stageScale u n m ^ (-1.03 : ℝ) ≤
        terminalDistance (nnGraph d m) (Finset.univ \ (state n).active) x y) :
    PrefixStageInputs d m n₀ K u (8 * C + 4) where
  state := state
  r := r
  physical := physical
  nested := fun n h1 h2 =>
    (stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _) (stageScale_anti hu m (Nat.le_succ n))
      (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)).1
  reset := reset
  rows := rows
  normStep := fun n h1 h2 => by
    have F := stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _)
      (stageScale_anti hu m (Nat.le_succ n)) (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)
    have h0 : 0 ≤ stageScale u n m ^ (0.10 * delta) := Real.rpow_nonneg (stageScale_pos' hu _ _).le _
    have := F.2.1
    unfold Kn at this
    nlinarith
  rStep := fun n h1 h2 => by
    have F := stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _)
      (stageScale_anti hu m (Nat.le_succ n)) (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)
    have h0 : 0 ≤ stageScale u n m ^ (0.35 * delta) := Real.rpow_nonneg (stageScale_pos' hu _ _).le _
    have := F.2.2.1
    nlinarith
  kernels := kernels
  counts := counts
  metrics := metrics
  affineStep := fun n h1 h2 y hy => by
    have F := stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _)
      (stageScale_anti hu m (Nat.le_succ n)) (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)
    exact F.2.2.2 y hy

end AndersonAC.AgentS78
