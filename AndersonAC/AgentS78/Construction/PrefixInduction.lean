import AndersonAC.AgentS78.InitialStage
import AndersonAC.S78.Definitions

/-!
# WP10 construction: the deterministic induction on a history prefix (frozen contract)

The run checks the stage bounds block by block: when stage `K` ends, only the history up to
`K` exists. `PrefixStageInputs d m n₀ K u C` is `S78.PathwiseStageInputs` with every field
required only for stages `n ≤ K` (steps for `n < K`); the scales are still those of the box
`m`. `PrefixStageBoundsStatement` is `stage_bounds_of_initial` (StageInduction.lean) for such
prefixes: the induction of InductionGe.lean only uses the fields below the stage it proves.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- `PathwiseStageInputs` restricted to the stages `n₀ ≤ n ≤ K`. -/
structure PrefixStageInputs (d m n₀ K : ℕ) (u C : ℝ) where
  state : ℕ → Endpoint (Torus d m)
  r : ℕ → Torus d m → ℂ
  physical : ∀ n, n₀ ≤ n → n ≤ K → IsDampedEndpoint (state n) (r n) (stageScale u n m)
  nested : ∀ n, n₀ ≤ n → n < K → (state (n + 1)).active ⊆ (state n).active
  reset : ∀ n, n₀ ≤ n → n ≤ K → ∀ i ∈ (state n).active, (state n).g i i = r n i
  rows : ∀ n, n₀ ≤ n → n ≤ K → ∀ i,
    rowFour (normalizedInverse (state n) (stageScale u n m)) i ≤ stageScale u n m ^ (1 + delta)
  normStep : ∀ n, n₀ ≤ n → n < K →
    matrixNorm (squareKernel (normalizedInverse (state (n + 1)) (stageScale u (n + 1) m))) ≤
      matrixNorm (squareKernel (normalizedInverse (state n) (stageScale u n m))) +
        C * stageScale u n m ^ (0.10 * delta)
  rStep : ∀ n, n₀ ≤ n → n < K → ‖r (n + 1) - r n‖ ≤ C * stageScale u n m ^ (0.35 * delta)
  kernels : ∀ n, n₀ ≤ n → n ≤ K →
    constantKernel (state n).active (endpointEnergy (state n) (r n) (stageScale u n m))
  counts : ∀ n, n₀ ≤ n → n ≤ K → Fintype.card (Torus d m) ≤ 2 * (state n).active.card
  metrics : ∀ n, n₀ ≤ n → n ≤ K → ∀ x y,
    physicalDistance d m x y / 2 - stageScale u n m ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ (state n).active) x y
  affineStep : ∀ n, n₀ ≤ n → n < K → ∀ y, neutral (state (n + 1)).active y →
    let θ := stageScale u (n + 1) m / stageScale u n m
    let old := inverseEnergy (state n).active (endpointEnergy (state n) (r n) (stageScale u n m)) y
    let new := inverseEnergy (state (n + 1)).active
      (endpointEnergy (state (n + 1)) (r (n + 1)) (stageScale u (n + 1) m)) y
    let target := θ * old + (1 - θ) * (∑ i ∈ (state (n + 1)).active, (y i) ^ 2 / (r n i).im ^ 2)
    (1 - C * stageScale u n m ^ (0.10 * delta)) * target ≤ new ∧
    new ≤ (1 + C * stageScale u n m ^ (0.10 * delta)) * target

/-- A full history is a prefix history up to `m` (field-for-field consistency check). -/
def PrefixStageInputs.ofPathwise {d m n₀ : ℕ} {u C : ℝ} (H : PathwiseStageInputs d m n₀ u C) :
    PrefixStageInputs d m n₀ m u C where
  state := H.state
  r := H.r
  physical := H.physical
  nested := H.nested
  reset := H.reset
  rows := H.rows
  normStep := H.normStep
  rStep := H.rStep
  kernels := H.kernels
  counts := H.counts
  metrics := H.metrics
  affineStep := H.affineStep

/-- **Frozen contract.** `stage_bounds_of_initial_unconditional` (InitialStageFull.lean) for
history prefixes. -/
def PrefixStageBoundsStatement (d : ℕ) (e₂ C : ℝ) : Prop :=
  ∃ (N : ℕ) (cP CP cL CL C₀ : ℝ), 0 < cP ∧ cP ≤ CP ∧ 0 < cL ∧ 0 < CL ∧ 0 < C₀ ∧
    ∀ n₀ : ℕ, N ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m → ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
    ∃ ρ : ℝ → ℂ, ContinuousOn ρ (OAI.Anderson.energyWindow d e₂) ∧
    ∀ E ∈ OAI.Anderson.energyWindow d e₂,
      IsDampedEndpoint (initialEndpoint d m E (stageScale u n₀ m) (ρ E)) (fun _ => ρ E)
        (stageScale u n₀ m) ∧
      ∀ K : ℕ, K ≤ m → ∀ H : PrefixStageInputs d m n₀ K u C,
        H.state n₀ = initialEndpoint d m E (stageScale u n₀ m) (ρ E) →
        H.r n₀ = (fun _ => ρ E) →
        ∀ n, n₀ ≤ n → n ≤ K →
          StageBounds d m n₀ n u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀ (H.state n) (H.r n)

end AndersonAC.AgentS78
