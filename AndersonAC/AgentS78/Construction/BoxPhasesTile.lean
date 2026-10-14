import AndersonAC.AgentS78.Construction.BoxPhasesCore
import AndersonAC.AgentS78.Construction.TilePhaseSchedule
import AndersonAC.AgentS78.Construction.TileStartPrefix

/-!
# WP10 construction, global run invariant: the tile-phase obligations (agent-s78box)

The tile-phase set of the global invariant is
`boxTS … j r = TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j r) ∩ Damp cA CA`,
where `Damp cA CA` (the damping of `x.r` on **all** sites, needed by `sweepEnd_keeps`) is a
run-level clause: tile blocks never change `x.r` (`tileBlock_reach_r`).

* `boxTS_tileOp`: the tile operations (`OpKeeps … j 0 y`), from `tileOp_keeps'`;
* `boxTS_good`: `TileGood` for the unprocessed tile of the operation, from
  `tileGoodCore_of_sweep`;
* `planClauses_of_cover`: the plan facts of a sweep from the cover facts (`StageCoverFacts`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-! ## Tile blocks keep the damping values -/

section TileR
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

theorem scalarStep_r (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ) :
    (scalarStep P j T s i ζ).1.r = s.1.r := by
  unfold scalarStep failTrial markTile
  dsimp only
  split_ifs <;> rfl

theorem tileStep_r (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (a : Answer (Torus d m)) : (tileStep P j T s q a).1.r = s.1.r := by
  unfold tileStep
  cases q with
  | nextOrder o => rfl
  | decision =>
    dsimp only
    split <;> rfl
  | trueDigit i h =>
    dsimp only
    split
    · rfl
    · exact scalarStep_r P j T _ _ _
  | auxiliary k =>
    dsimp only
    split
    · rfl
    · exact scalarStep_r P j T _ _ _
  | trueSuffix i h =>
    dsimp only
    split
    · rfl
    · exact scalarStep_r P j T _ _ _

/-- **Tile blocks never change the damping values.** -/
theorem tileBlock_reach_r (x : RunRecord d m) (s : RunRecord d m × TileScratch d m)
    (h : BlockReach (tileBlock P j T) x s) : s.1.r = x.r := by
  induction h with
  | enter =>
    show ((tileBlock P j T).enter x).1.r = x.r
    cases hab : x.aborted <;> simp [tileBlock, hab]
  | step s a _ _ ih =>
    show ((tileBlock P j T).update s a).1.r = x.r
    simp only [tileBlock]
    split_ifs
    · exact ih
    · rw [tileStep_r]; exact ih

end TileR

/-- The exit of the tile operation `(j, 0, y)` has the damping values of the entering record. -/
theorem runOp_tile_exit_r {ClSc : Type} (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (j : ℕ) (y : Torus d m) (x : RunRecord d m) (k : ℕ) (M : ℕ → ℕ) (ω : RandomSources (Torus d m) M)
    (hrun : ∀ k' < k, (runOp P ts₀ cl₀ clr j 0 y).halted
      (localState M (runOp P ts₀ cl₀ clr j 0 y) x k' ω) = false) :
    ((runOp P ts₀ cl₀ clr j 0 y).exit (localState M (runOp P ts₀ cl₀ clr j 0 y) x k ω)).r =
      x.r := by
  by_cases hin : P.n₀ < j ∧ j ≤ m + 1
  · cases hT : tileAt P j y with
    | none =>
      have hop : runOp P ts₀ cl₀ clr j 0 y = simpleBlock (ts₀, cl₀) id := by
        unfold runOp; rw [if_pos hin, if_pos rfl, hT]
      rw [hop] at hrun ⊢
      exact congrArg RunRecord.r (simpleBlock_exit M (ts₀, cl₀) id x k ω hrun)
    | some T =>
      have hop : runOp P ts₀ cl₀ clr j 0 y =
          (tileBlock P j T).embed (tileEmbed cl₀) tileProj := by
        unfold runOp; rw [if_pos hin, if_pos rfl, hT]
      rw [hop] at hrun ⊢
      have hrun' : ∀ k' < k, (tileBlock P j T).halted
          (localState M (tileBlock P j T) x k' ω) = false := by
        intro k' hk'
        have := hrun k' hk'
        rw [localState_embed M _ _ _ (fun _ => rfl)] at this
        exact this
      rw [localState_embed M _ _ _ (fun _ => rfl)]
      exact tileBlock_reach_r P j T x _ (localState_reach M _ x ω k hrun')
  · have hop : runOp P ts₀ cl₀ clr j 0 y = simpleBlock (ts₀, cl₀) id := by
      unfold runOp; rw [if_neg hin]
    rw [hop] at hrun ⊢
    exact congrArg RunRecord.r (simpleBlock_exit M (ts₀, cl₀) id x k ω hrun)

/-! ## The tile-phase set -/

/-- Damping values of all sites in `[cA, CA]` (imaginary part) and of norm `≤ CA`. -/
def Damp (cA CA : ℝ) : Set (RunRecord d m) :=
  {x | ∀ i, cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA ∧ ‖x.r i‖ ≤ CA}

/-- **The tile-phase set of the global invariant.** -/
def boxTS (C : ℝ) (P : TilePlan d m) (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (Cb cA CA : ℝ) (j r : ℕ) :
    Set (RunRecord d m) :=
  TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j r) ∩ Damp cA CA

/-- **Tile operations** (`OpKeeps … j 0 y`). -/
theorem boxTS_tileOp {C : ℝ} (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (Cb cA CA : ℝ) (RB : ℕ → Set (RunRecord d m)) (hu : 0 < P.u)
    (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m + 1) :
    OpKeeps P ts₀ cl₀ n₀ u RB j 0 y (boxTS C P n₀ u E ρ Cb cA CA j (siteRank d m y))
      (boxTS C P n₀ u E ρ Cb cA CA j (siteRank d m y + 1)) := by
  intro x k ω _ hx hrun hh _
  refine ⟨tileOp_keeps' ts₀ cl₀ (clrOf n₀ u) hu hj hjm y x hx.1 k ω hrun hh, ?_⟩
  intro i
  rw [runOp_tile_exit_r P ts₀ cl₀ (clrOf n₀ u) j y x k (tileOrderSize P) ω hrun]
  exact hx.2 i

/-- **Goodness of the unprocessed tile** (`BoxInvariantK.hgoodT`). -/
theorem boxTS_good {C : ℝ} (P : TilePlan d m) (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (Cb cA CA : ℝ) (j : ℕ)
    (y : Torus d m) (T : Fin (P.cover j).cover.count) (hT : tileAt P j y = some T)
    (x : RunRecord d m) (hx : x ∈ boxTS C P n₀ u E ρ Cb cA CA j (siteRank d m y)) :
    x ∈ TileGood C P j T :=
  fun hab => tileGoodCore_of_sweep (hx.1 hab) (not_mem_doneUpTo P j hT)

/-! ## Plan facts from the cover facts -/

theorem shellBounds_mono_box {P : Type*} [Fintype P] {C C' : ℝ} {dist : P → P → ℝ} (h : C ≤ C')
    (hs : S45.ShellBounds d C dist) : S45.ShellBounds d C' dist where
  nonneg := hs.nonneg
  symmetric := hs.symmetric
  triangle := hs.triangle
  self := hs.self
  count := fun v hv hv1 i => (hs.count v hv hv1 i).trans
    (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hv.le _))
  second := fun v hv hv1 i => (hs.second v hv hv1 i).trans
    (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hv.le _))

/-- The plan facts of sweep `j` with any constant `Cg ≥ max 1 C`. -/
theorem planClauses_of_cover {C Ch Cg : ℝ} (P : TilePlan d m) (j : ℕ)
    (h : StageCoverFacts C Ch P.u P.n₀ j (P.cover j)) (hCg : C ≤ Cg) (hCg1 : 1 ≤ Cg) :
    PlanClauses Cg P j where
  one_le := hCg1
  cover_b := ⟨h.b_pos, h.b_le⟩
  cover_C := h.C_eq.le.trans hCg
  shell := shellBounds_mono_box hCg h.shell
  tile_card := fun T => (h.tile_card T).trans
    (mul_le_mul_of_nonneg_right hCg (Real.rpow_nonneg (h.b_pos.le.trans h.b_le) _))
  inner_card := fun T => (h.inner_card T).trans
    (mul_le_mul_of_nonneg_right hCg (Real.rpow_nonneg (h.b_pos.le.trans h.b_le) _))

end AndersonAC.AgentS78
