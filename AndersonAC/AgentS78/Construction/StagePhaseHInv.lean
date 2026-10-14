import AndersonAC.AgentS78.Construction.StagePhaseClrExit
import AndersonAC.AgentS78.Construction.BoxAssembly

/-!
# The clearing phase in the schedule's `hInv` shape (kind 2)

. Run invariant of `BoxInvariantK.hInv` (real local answers, BoxSplit.lean) on
the indices `opIndex j 2 y` (clearing attempts) and `opIndex j 3 y` (stage operation at `site₀`,
identity elsewhere):

* `clearOp_hInv`: a clearing index maps `ClearPhase … j` into `ClearPhase … j`, given the DONE
  step facts of the attempted clearing (`ClearingDoneFacts`, the analytic DONE output); FAIL and
  empty exits keep the endpoint (`ClearPhase.of_exit`);

Kind 3 is in StagePhaseStageOp.lean (it imports `resetRow_proof`, whose file ResetRowShell.lean
clashes with TileCoverPlan.lean on `shellBounds_mono`, so it cannot share imports with
BoxAssembly.lean).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-- The DONE step facts of the clearing attempt anchored at `y` from the record `x`: for every
clearing-phase datum of `x`, a DONE exit commits one clearing with its `ClearingStepFacts`. -/
def ClearingDoneFacts (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C CA cA PA : ℝ) (j : ℕ) (y : Torus d m)
    (x : RunRecord d m) : Prop :=
  ∀ D : ClearPhaseData n₀ u E ρ C CA cA PA j x, ∀ s : RunRecord d m × ClearScratch d m,
    BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s → x.aborted = false →
    clearingScheduled j m → s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
    ClearingStepFacts D.I (clearingDoneExit x s.2).endpoint y

/-- **One clearing attempt keeps the clearing-phase invariant** (block form). -/
theorem clearingBlock_keeps {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} (j : ℕ) (y : Torus d m)
    (x : RunRecord d m) (hx : ClearPhase n₀ u E ρ C CA cA PA j x)
    (hdone : ClearingDoneFacts n₀ u E ρ C CA cA PA j y x)
    (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    ClearPhase n₀ u E ρ C CA cA PA j (clearingExit (d := d) (m := m) j y s) := by
  have hx1 := (clr_reach n₀ j u y x s hs).1
  have hr : (clearingExit (d := d) (m := m) j y s).r = x.r := by rw [clr_exit_r, hx1]
  have hab : (clearingExit (d := d) (m := m) j y s).aborted = x.aborted := by
    rcases clr_exit_cases j y s with h | h | h <;> rw [h, hx1] <;> rfl
  refine ClearPhase.of_exit hx (fun h => hab ▸ h) (fun _ => hr) (fun hy D => ?_)
  rcases clr_exit_trichotomy n₀ j u y x s hs with h | h | ⟨hab', hsch, hne, hf, hd, h⟩
  · exact Or.inl (by rw [h])
  · exact Or.inl (by rw [h.2]; rfl)
  · exact Or.inr ⟨y, by rw [h]; exact hdone D s hs hab' hsch hne hf hd⟩

/-- The exit of a simple block reached from `x`. -/
theorem simpleBlock_exit_reach {Sc : Type} (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (x : RunRecord d m) (s : RunRecord d m × Sc) (h : BlockReach (simpleBlock sc₀ f) x s) :
    (simpleBlock sc₀ f).exit s = f x := by
  rw [simpleBlock_reach sc₀ f x s h]; rfl

theorem runOp_two {ClSc : Type} [MeasurableSpace ClSc] (P : TilePlan d m) (ts₀ : TileScratch d m)
    (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (j : ℕ) (y : Torus d m) :
    runOp P ts₀ cl₀ clr j 2 y = (if P.n₀ < j ∧ j ≤ m + 1 ∧ j ≤ m / 2 then
      (clr j y).embed (clearEmbed ts₀) clearProj else simpleBlock (ts₀, cl₀) id) := by
  unfold runOp
  by_cases h1 : P.n₀ < j ∧ j ≤ m + 1
  · rw [if_pos h1, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    by_cases h2 : j ≤ m / 2
    · rw [if_pos h2, if_pos ⟨h1.1, h1.2, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2.2)]
  · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, h.2.1⟩)]

/-- **Clearing indices keep the clearing-phase invariant** (schedule form, real local answers). -/
theorem clearOp_hInv (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} (j : ℕ) (y : Torus d m) (x : RunRecord d m)
    (hx : ClearPhase n₀ u E ρ C CA cA PA j x)
    (hdone : ClearingDoneFacts n₀ u E ρ C CA cA PA j y x)
    (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hrun : ∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) (opIndex d m j 2 y)).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
        (opIndex d m j 2 y)) x k' ω) = false) :
    ClearPhase n₀ u E ρ C CA cA PA j
      ((scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) (opIndex d m j 2 y)).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
          (opIndex d m j 2 y)) x k ω)) := by
  have hreach := localState_reach (tileOrderSize P) _ x ω k hrun
  revert hreach
  generalize localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))
    (opIndex d m j 2 y)) x k ω = s
  intro hreach
  rw [scheduleBlocks_opIndex _ j 2 y (by norm_num), runOp_two] at hreach ⊢
  split_ifs at hreach ⊢ with h1
  · obtain ⟨s0, hs0, rfl⟩ := blockReach_embed (clrOf n₀ u j y) (clearEmbed ts₀) clearProj
      (fun _ => rfl) x s hreach
    exact clearingBlock_keeps j y x hx hdone s0 hs0
  · rw [simpleBlock_exit_reach _ _ x s hreach]; exact hx

end AndersonAC.AgentS78
