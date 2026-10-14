import AndersonAC.AgentS78.Construction.StagePhaseStart

/-!
# The clearing-phase hand-over with a chosen scale radius

agent-s78phase2. `ClearPhaseData.ofSweepDs`: `ClearPhaseData.ofSweep` (agent-s78phase) with the
scale radius `Ds` of the stage chosen in the window `t^{-8-ν} ≤ Ds ≤ CA t^{-8-ν}`,
`400 Ds < L`. The clearing-phase record clauses (`ClearPhaseR`) need
`2 clearRadius ≤ Ds ≤ Ctr clearRadius`; `Ds = 2^9 t_j^{-8-ν}` satisfies both windows when
`CA ≥ 2^9` and `Ctr ≥ 2^25`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- **Clearing-phase data at the sweep end** (`k = 0`) with a chosen scale radius `Ds`. -/
def ClearPhaseData.ofSweepDs {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} {j : ℕ}
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hn₀ : 1 ≤ n₀) (hnj : n₀ < j) (hj : j ≤ m) (hm : 2 ≤ m)
    (hCA : 1 ≤ CA) (hcA : 0 < cA) (hPA : 0 ≤ PA) (Ds : ℝ)
    (hDs1 : stageScale u j m ^ (-8 - nu d) ≤ Ds) (hDs2 : Ds ≤ CA * stageScale u j m ^ (-8 - nu d))
    (hDsL : 400 * Ds < (OAI.Anderson.sideLength m : ℝ))
    (old sw : Endpoint (Torus d m)) (rOld : Torus d m → ℂ)
    (hist : BoundaryHist n₀ u E ρ C (j - 1) old rOld)
    (sweep : SweepFacts C (stageScale u (j - 1) m) (stageScale u j m) old sw rOld)
    (damping : ∀ i, cA ≤ (rOld i).im ∧ (rOld i).im ≤ CA ∧ ‖rOld i‖ ≤ CA)
    (physical : IsDampedEndpoint sw rOld (stageScale u j m))
    (activeCount : Fintype.card (Torus d m) ≤ 2 * sw.active.card)
    (metric : ∀ y z, physicalDistance d m y z / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ sw.active) y z)
    (resolventDecay : ∀ i i', ‖normalizedInverse sw (stageScale u j m) i i'‖ ≤
      CA / Real.sqrt (stageScale u j m) * Real.exp (-cA * stageScale u j m *
        max (physicalDistance d m i i' / 2 - stageScale u j m ^ (-1.03 : ℝ)) 0))
    (initialComparison : ∀ f,
      cA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f ≤
        endpointEnergy sw rOld (stageScale u j m) f ∧
      endpointEnergy sw rOld (stageScale u j m) f ≤
        CA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f)
    (initialRows : ∀ i, rowFour (normalizedInverse sw (stageScale u j m)) i ≤
      0.7 * stageScale u j m ^ (1 + delta))
    (initialLag : ∀ i ∈ sw.active, ‖sw.g i i - rOld i‖ ≤ CA * stageScale u j m ^ (0.42 * delta))
    (x : RunRecord d m) (hx : x.endpoint = sw) (hr : x.r = rOld) :
    ClearPhaseData n₀ u E ρ C CA cA PA j x where
  old := old
  rOld := rOld
  k := 0
  I :=
    { state := fun _ => sw
      anchor := fun a => a.elim0
      C := CA
      c := cA
      P := PA
      Ds := Ds
      positive := by
        have ht := stageScale_pos' hu j m
        have hm1 : 1 ≤ m := by omega
        have hj1 : stageScale u j m ≤ 1 := stageScale_le_one hu (by omega) hm1
        have hn1 : stageScale u n₀ m ≤ 1 := stageScale_le_one hu hn₀ hm1
        have hb := stageScale_pos' hu n₀ m
        refine ⟨ht, hj1, mul_pos hb ht, ?_, hcA, hCA, hPA⟩
        nlinarith
      scaleRadius := ⟨hDs1, hDs2⟩
      embedded := hDsL
      damping := damping
      physical := fun _ => physical
      nested := fun a => a.elim0
      activeCount := fun _ => activeCount
      distinct := fun a => a.elim0
      removedNonempty := fun a => a.elim0
      removedSize := fun a => a.elim0
      removedLocal := fun a => a.elim0
      haloOverlap := fun y => by
        have h0 : overlap (fun a : Fin 0 => cube d m (Fin.elim0 a) (200 * Ds)) y = 0 := by
          unfold overlap; simp
        rw [h0]
        have := Real.rpow_pos_of_pos (stageScale_pos' hu j m) (-(d : ℝ) * nu d)
        push_cast
        nlinarith
      metric := fun _ => metric
      resolventDecay := fun _ => resolventDecay
      initialComparison := initialComparison
      initialRows := initialRows
      initialLag := initialLag
      entryChange := fun a => a.elim0
      rowChange := fun a => a.elim0
      totalChange := fun a => a.elim0
      decay := fun a => a.elim0 }
  hist := hist
  sweep := sweep
  last := hx.symm
  frozen := hr
  constC := rfl
  constc := rfl
  constP := rfl

end AndersonAC.AgentS78
