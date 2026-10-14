import AndersonAC.AgentS78.Construction.NoEarlyAbort
import AndersonAC.AgentS78.Construction.StageDichotomyK

/-!
# WP10 construction: the snapshot dichotomy of the schedule

`hdich` of `blockRun_of_runOps` from `stage_dichotomy`, along the actual chain of entering
records `r n = blockPrestate … n ω` of a clearing stage `j`, from the block after the snapshot
(`a = opIndex j 1 site₀ + 1`) to the start of stage `j + 1`. Proved here: the chain relation
(`run_chain`), the label scales (`opLabel_scale`) and the keep-or-relabel rule (from
`runOps_mark`). The two clearing-specific inputs stay as hypotheses: an attempt relabels
(or clears) the sites of every small snapshot component (`hatt`), and no block of the stage
touches a site of a component above the schedule's threshold `⌊t_j^{-ν}⌋`,
`t_j = stageScale u j m` (`hloc`; `stage_dichotomy_K`); they follow from the clearing block's semantics
(muse-s78clear) and the snapshot.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

/-- The block after the snapshot of stage `j`. -/
def afterSnapshotIdx (d m j : ℕ) : ℕ := opIndex d m j 1 (site₀ d m) + 1

theorem afterSnapshotIdx_le (j : ℕ) : afterSnapshotIdx d m j ≤ stageStartIdx d m (j + 1) := by
  have hS := siteCount_pos d m
  have hr : (siteRank d m (site₀ d m)).val = 0 := by
    unfold site₀; rw [Equiv.apply_symm_apply]
  unfold afterSnapshotIdx opIndex stageStartIdx
  rw [hr]; nlinarith

theorem afterSnapshotIdx_ge (j : ℕ) : 4 * j * siteCount d m ≤ afterSnapshotIdx d m j := by
  unfold afterSnapshotIdx opIndex; nlinarith

open Classical in
/-- **The snapshot dichotomy of the schedule** (`hdich` of `blockRun_of_runOps`). -/
theorem runOps_dich (hd : 0 < d) (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (M : ℕ → ℕ) (rec₀ : RunRecord d m) (orderSet auxSet : ℕ → Set ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M (scheduleBlocks (runOp P ts₀ cl₀ clr)) orderSet)
    (haux : BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) auxSet)
    (Ch : ℝ) (hCh : 1 ≤ Ch) (hu : P.u ∈ Set.Ioc (0 : ℝ) 1)
    (hmark : ∀ n x s, BlockReach (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x s →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted s = true →
      ∀ y ∈ ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit s).pending,
        (y ∈ x.pending ∧ ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit s).latest y =
          x.latest y) ∨
        (((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit s).latest y = opLabel d m n ∧
          (scheduleBlocks (runOp P ts₀ cl₀ clr) n).firstFail s = true ∧
          (physicalDistance d m y (opLabel d m n).anchor ≤
            Ch * (4 : ℝ) ^ ((8 + nu d) * ((opLabel d m n).scale : ℝ)) ∧
            slotIndex (opLabel d m n) = n)))
    (hatt : ∀ j (ω : RandomSources (Torus d m) M), P.n₀ < j → clearingScheduled j m →
      blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤ →
      ∀ y (hy : y ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
          (afterSnapshotIdx d m j) ω).pending),
        (Finset.univ.filter ((snapshotGraph d m (blockPrestate M
          (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j) ω).pending
          (separationRadius j)).Reachable ⟨y, hy⟩)).card ≤ ⌊stageScale P.u j m ^ (-nu d)⌋₊ →
        ∃ n, afterSnapshotIdx d m j ≤ n ∧ n < stageStartIdx d m (j + 1) ∧ ∀ x',
          BlockStep (scheduleBlocks (runOp P ts₀ cl₀ clr)) n
            (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω) x' →
          y ∈ x'.pending → x'.latest y = opLabel d m n)
    (hloc : ∀ j (ω : RandomSources (Torus d m) M), P.n₀ < j → clearingScheduled j m →
      blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤ →
      ∀ y (hy : y ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
          (afterSnapshotIdx d m j) ω).pending),
        ⌊stageScale P.u j m ^ (-nu d)⌋₊ < (Finset.univ.filter ((snapshotGraph d m (blockPrestate M
          (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j) ω).pending
          (separationRadius j)).Reachable ⟨y, hy⟩)).card →
        ∀ n, afterSnapshotIdx d m j ≤ n → n < stageStartIdx d m (j + 1) → ∀ x',
          BlockStep (scheduleBlocks (runOp P ts₀ cl₀ clr)) n
            (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω) x' →
          y ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω).pending →
          y ∈ x'.pending ∧ x'.latest y =
            (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω).latest y) :
    ∀ j x (ω : RandomSources (Torus d m) M), P.n₀ < j → clearingScheduled j m →
      blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤ →
      x ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (j + 1)) ω).pending →
      ((blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (j + 1)) ω).latest x).scale = j ∨
      ∃ S : Finset (Torus d m), x ∈ S ∧ stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧
        (∀ y ∈ S, y ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
          (stageStartIdx d m (j + 1)) ω).pending) ∧
        (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))) := by
  intro j x ω hj hsch hreach hx
  set B := scheduleBlocks (runOp P ts₀ cl₀ clr)
  set r : ℕ → RunRecord d m := fun n => blockPrestate M B rec₀ n ω with hr
  have hchain := run_chain M B rec₀ orderSet auxSet hdisj horders haux ω _ hreach
  refine stage_dichotomy_K hd Ch hCh ⌊stageScale P.u j m ^ (-nu d)⌋₊ r (afterSnapshotIdx d m j)
    (stageStartIdx d m (j + 1)) j (afterSnapshotIdx_le j) (floor_threshold_le hu j m) (fun n x x' => BlockStep B n x x' ∧ x = r n) (opLabel d m)
    (fun n _ h2 => ⟨hchain n h2, rfl⟩) (fun n h1 h2 => ?_) ?_ ?_ ?_ x hx
  · apply opLabel_scale d m j n
    · exact le_trans (afterSnapshotIdx_ge j) h1
    · unfold stageStartIdx at h2; exact h2
  · rintro n x x' ⟨⟨s, hs, hh, rfl⟩, -⟩ y hy
    rcases hmark n x s hs hh y hy with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro y hy hsmall
    obtain ⟨n, h1, h2, h3⟩ := hatt j ω hj hsch hreach y hy hsmall
    exact ⟨n, h1, h2, fun x x' ⟨hst, hx⟩ hy' => by rw [hx] at hst; exact h3 x' hst hy'⟩
  · intro y hy hbig n h1 h2 x x' ⟨hst, hx⟩ hyx
    rw [hx] at hst hyx ⊢
    exact hloc j ω hj hsch hreach y hy hbig n h1 h2 x' hst hyx

end AndersonAC.AgentS78
