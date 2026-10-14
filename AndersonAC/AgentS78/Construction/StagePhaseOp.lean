import AndersonAC.AgentS78.Construction.StagePhaseReset
import AndersonAC.AgentS78.Construction.RunOps

/-!
# WP10 construction: the stage operation of the schedule on the clearing-phase invariant

`stageMapA P j` is `stageMap P j` (RunOps.lean) with the active-block reset `resetMapA` in place
of `resetMap` (see StagePhaseResetDefect.lean). `stage_op_boundary`: for a non-aborted record
with clearing-phase data, the stage operation `guardMap (stageMapA P j)` yields a record with
`BoundaryInv … j`, the hypothesis list of the next stage (`BoundaryHist.extend`'s conclusion).
The cutoff and the start lift keep the endpoint and the damping.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- Reset of stage `j` on the active block, cutoff at `⌊m/2⌋`, and the lift for the next
sweep. -/
def stageMapA (P : TilePlan d m) (j : ℕ) : RunRecord d m → RunRecord d m :=
  sweepStartMap (sweepTheta P.u m (j + 1)) (sweepScale P.u m (j + 1)) ∘
    (if j = m / 2 then cutoffMap else id) ∘ resetMapA (stageScale P.u j m)

/-- Since the switch of 2026-10-14 the schedule's stage operation is `stageMapA`. -/
theorem stageMapA_eq_stageMap (P : TilePlan d m) (j : ℕ) : stageMapA P j = stageMap P j := rfl

theorem stageMapA_endpoint_r (P : TilePlan d m) (j : ℕ) (x : RunRecord d m) :
    (stageMapA P j x).endpoint = (resetMapA (stageScale P.u j m) x).endpoint ∧
    (stageMapA P j x).r = (resetMapA (stageScale P.u j m) x).r := by
  unfold stageMapA
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- **The stage operation of the schedule produces the next stage boundary.** -/
theorem stage_op_boundary (hd : 3 ≤ d) (CA cA PA CR : ℝ) (hCA : 1 ≤ CA) (hcA : 0 < cA)
    (hPA : 0 ≤ PA) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C → ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {m : ℕ} (P : TilePlan d m) (E : ℝ) (ρ : ℂ) (j : ℕ) (x : RunRecord d m)
      (D : ClearPhaseData P.n₀ P.u E ρ C CA cA PA j x),
      P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → stageScale P.u (j - 1) m < t₀ →
      Kn D.old (stageScale P.u (j - 1) m) ≤ 1 / 3 →
      (Kn x.endpoint (stageScale P.u j m) ≤ 1 / 2 →
        (∀ i ∈ x.endpoint.active,
          ‖x.endpoint.g i i - x.r i‖ ≤ stageScale P.u j m ^ (0.36 * delta)) →
        ResetRowBound CR x.endpoint x.r (stageScale P.u j m)) → x.aborted = false →
      BoundaryInv P.n₀ P.u E ρ C j (guardMap (stageMapA P j) x) := by
  obtain ⟨Cmin, hCmin, hmain⟩ := stage_end_resetA hd CA cA PA CR hCA hcA hPA
  refine ⟨Cmin, hCmin, fun C hC => ?_⟩
  obtain ⟨t₀, ht₀, h⟩ := hmain C hC
  refine ⟨t₀, ht₀, fun P E ρ j x D hu hj ht hK hrow hab => ?_⟩
  have hg : guardMap (stageMapA P j) x = stageMapA P j x := by simp [guardMap, hab]
  unfold BoundaryInv
  rw [hg, (stageMapA_endpoint_r P j x).1, (stageMapA_endpoint_r P j x).2]
  exact h P.n₀ P.u E ρ j x D hu hj ht hK hrow

/-- The stage-start bound `‖K‖ ≤ 1/3` of `stage_op_boundary` from the stage bounds
(clause 3 of `StageBounds`, given along every history by `stageBounds_of_hist`). -/
theorem Kn_le_of_stageBounds {n₀ k : ℕ} {u cP CP cL CL C₀ : ℝ} {s : Endpoint (Torus d m)}
    {r : Torus d m → ℂ} (h : StageBounds d m n₀ k u cP CP cL CL C₀ s r) :
    Kn s (stageScale u k m) ≤ 1 / 3 :=
  h.2.2.1

end AndersonAC.AgentS78
