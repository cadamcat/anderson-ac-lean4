import AndersonAC.AgentS78.Construction.TilePhaseEnd
import AndersonAC.AgentS78.Construction.Assembly

/-!
# the schedule indices of stage `j`. In the schedule (`opIndex d m j k y = (4j + k)·N + rank y`,
`N = siteCount d m`), the tile operations of stage `j` are the indices
`stageStartIdx d m j + r`, `r < N`, and the sweep end is `stageStartIdx d m j + N`. The run
invariant on these indices is `TileSweepInv … (doneUpTo P j r)`:

* `tileOps_hInv`: index `stageStartIdx d m j + r` maps `doneUpTo P j r` to `doneUpTo P j (r+1)`
  (the `hInv` shape of `blockRun_of_runOps`);
* `sweepEndOp_hInv`: index `stageStartIdx d m j + N` maps `TileSweepInv … (doneUpTo P j N)`
  into `ClearPhase … j` (digit stages `j ≤ m`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

theorem opIndex_tile (j r : ℕ) (hr : r < siteCount d m) :
    stageStartIdx d m j + r = opIndex d m j 0 ((siteRank d m).symm ⟨r, hr⟩) := by
  unfold stageStartIdx opIndex
  simp

theorem opIndex_sweepEnd (j : ℕ) :
    stageStartIdx d m j + siteCount d m = opIndex d m j 1 (site₀ d m) := by
  unfold stageStartIdx opIndex site₀
  simp; ring

section Ops
variable {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}
  {ClSc : Type} [MeasurableSpace ClSc]

/-- **The tile operations of stage `j` keep the tile-phase invariant** (schedule form). -/
theorem tileOps_hInv (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (hu : 0 < P.u) (hj : P.n₀ < j) (hjm : j ≤ m + 1) (r : ℕ) (hr : r < siteCount d m)
    (x : RunRecord d m) (hx : x ∈ TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j r))
    (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hrun : ∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) (stageStartIdx d m j + r)).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)
        (stageStartIdx d m j + r)) x k' ω) = false)
    (hh : (scheduleBlocks (runOp P ts₀ cl₀ clr) (stageStartIdx d m j + r)).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)
        (stageStartIdx d m j + r)) x k ω) = true) :
    (scheduleBlocks (runOp P ts₀ cl₀ clr) (stageStartIdx d m j + r)).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)
        (stageStartIdx d m j + r)) x k ω) ∈
      TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j (r + 1)) := by
  set y := (siteRank d m).symm ⟨r, hr⟩ with hy
  have hry : ((siteRank d m y : Fin (siteCount d m)) : ℕ) = r := by simp [hy]
  rw [opIndex_tile j r hr, scheduleBlocks_opIndex _ j 0 y (by norm_num)] at hrun hh ⊢
  rw [← hry] at hx ⊢
  exact tileOp_keeps' ts₀ cl₀ clr hu hj hjm y x hx k ω hrun hh

/-- **The sweep-end operation of a digit stage hands over to the clearing phase** (schedule
form; conditional on the analytic `SweepEndStatement`). -/
theorem sweepEndOp_hInv {CA cA cP CP cL CL C₀ : ℝ}
    (hend : SweepEndStatement d C Cb CA cA cP CP cL CL C₀) :
    ∃ t0 > 0, ∀ {m : ℕ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {PA : ℝ}
      {ClSc : Type} [MeasurableSpace ClSc] (ts₀ : TileScratch d m) (cl₀ : ClSc)
      (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc)),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → 1 ≤ n₀ → n₀ < j → j ≤ m → 2 ≤ m →
    1 ≤ CA → 0 < cA → 0 ≤ PA → sweepScale u m j < t0 →
    ∀ x : RunRecord d m, x ∈ TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j (siteCount d m)) →
    (x.aborted = false → ∀ i, cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA ∧ ‖x.r i‖ ≤ CA) →
    (x.aborted = false → StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r) →
    ∀ (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P)),
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) (stageStartIdx d m j + siteCount d m)).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)
        (stageStartIdx d m j + siteCount d m)) x k' ω) = false) →
    ClearPhase n₀ u E ρ Cb CA cA PA j
      ((scheduleBlocks (runOp P ts₀ cl₀ clr) (stageStartIdx d m j + siteCount d m)).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)
          (stageStartIdx d m j + siteCount d m)) x k ω)) := by
  obtain ⟨t0, ht0, hk⟩ := sweepEnd_keeps hend
  refine ⟨t0, ht0, ?_⟩
  intro m P j n₀ u E ρ PA ClSc _ ts₀ cl₀ clr hn hu' hu hn₀ hnj hj hm hCA hcA hPA hsmall x hx
    hdamp hSB k ω hrun
  have hop : runOp P ts₀ cl₀ clr j 1 (site₀ d m) =
      simpleBlock (ts₀, cl₀) (guardMap (endMap P j)) := by
    have hjj : P.n₀ < j ∧ j ≤ m + 1 := ⟨by rw [hn]; exact hnj, by omega⟩
    simp only [runOp, hjj, and_self, if_true, show (1 : ℕ) ≠ 0 by norm_num, if_false]
  rw [opIndex_sweepEnd j, scheduleBlocks_opIndex _ j 1 (site₀ d m) (by norm_num), hop] at hrun ⊢
  have hs := simpleBlock_reach (ts₀, cl₀) (guardMap (endMap P j)) x _
    (localState_reach _ _ x ω k hrun)
  rw [hs]
  rw [doneUpTo_all] at hx
  exact hk hn hu' hu hn₀ hnj hj hm hCA hcA hPA hsmall x hx hdamp hSB

end Ops

end AndersonAC.AgentS78
