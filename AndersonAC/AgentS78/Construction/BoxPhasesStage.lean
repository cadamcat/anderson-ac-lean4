import AndersonAC.AgentS78.Construction.BoxPhasesTile
import AndersonAC.AgentS78.Construction.StagePhaseOpRow
import AndersonAC.AgentS78.Construction.RunBasicsInit

/-!
# sweep ends, stage operations, initial record


Per box (`P`, energy `E`, initial damping `ρ`, history constant `Cb`, assembly constants
`CA cA PA`, damping window `[cA, CA]`), with the run-level set `RB n = RunBasics P n ∩ Xg n`:

* `boxCL … Xc j = ClearPhase … j ∩ Damp ∩ PhysSet ∩ Xc j` — the clearing-phase set; `Xc` is the
  record-level part of the clearing phase supplied by the clearing package;
* `boxFG` — the final record (`FinalGood`) on non-aborted records;
* `boxTS_endOp` — the sweep end of a digit stage (`sweepEnd_keeps` in specialized form);
* `boxTS_finalEndOp` — the final sweep end (`finalSweep_good` in specialized form);
* `boxCL_stageOp` — the stage operation: `stage_op_boundary_of_row` (specialized), then the
  sweep start `tileSweepInv_start'` with the RunBasics projections `runBasics_afterStage_pre`;
* `initialRecord_boxTS` — `hInv0`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

/-- The physical identity on non-aborted records. -/
def PhysSet (E : ℝ) : Set (RunRecord d m) := {x | x.aborted = false → PhysicalIdentity E x}

/-- **The clearing-phase set** of the global invariant. -/
def boxCL (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (Cb CA cA PA dlo dhi : ℝ)
    (Xc : ℕ → ℕ → Set (RunRecord d m)) (j r : ℕ) : Set (RunRecord d m) :=
  {x | ClearPhase n₀ u E ρ Cb CA cA PA j x} ∩ Damp dlo dhi ∩ PhysSet E ∩ Xc j r

/-- **The final set** of the global invariant. -/
def boxFG (u E Cr cp cg : ℝ) : Set (RunRecord d m) :=
  {x | x.aborted = false → x ∈ FinalGood (d := d) (m := m) u E Cr cp cg}

/-- The exit of a query-free operation. -/
theorem runOp_simple_exit (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (n₀ : ℕ) (u : ℝ) (j k : ℕ) (y : Torus d m) (f : RunRecord d m → RunRecord d m)
    (hop : runOp P ts₀ cl₀ (clrOf n₀ u) j k y = simpleBlock (ts₀, cl₀) f)
    (x : RunRecord d m) (k' : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hrun : ∀ k'' < k', (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k'' ω) = false) :
    (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).exit
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k' ω) = f x := by
  rw [hop] at hrun ⊢
  exact simpleBlock_exit (tileOrderSize P) (ts₀, cl₀) f x k' ω hrun

theorem guardMap_aborted (f : RunRecord d m → RunRecord d m) (x : RunRecord d m)
    (h : x.aborted = true) : guardMap f x = x := by
  simp [guardMap, h]

theorem guardMap_live (f : RunRecord d m → RunRecord d m) (x : RunRecord d m)
    (h : x.aborted = false) : guardMap f x = f x := by
  simp [guardMap, h]

section Box
variable (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (E : ℝ) (ρ : ℂ)
  (Cg Cb CA cA PA : ℝ) (cP CP cL CL C₀ : ℝ)
  (Xg : ℕ → Set (RunRecord d m)) (Xc : ℕ → ℕ → Set (RunRecord d m))

/-- **The sweep end of a digit stage** `(j, 1, site₀)`, `n₀ < j ≤ m`: tile phase → clearing
phase. -/
theorem boxTS_endOp (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m) (hy : y = site₀ d m)
    (hSBh : ∀ k s rk, P.n₀ ≤ k → k ≤ m → BoundaryHist P.n₀ P.u E ρ Cb k s rk →
      StageBounds d m P.n₀ k P.u cP CP cL CL C₀ s rk)
    (hcA : cA ≤ cP) (hCA : CP ≤ CA)
    (hkeep : ∀ x : RunRecord d m, x ∈ TileSweepInv Cg P j P.n₀ P.u E ρ Cb Finset.univ →
      (x.aborted = false → ∀ i, cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA ∧ ‖x.r i‖ ≤ CA) →
      (x.aborted = false → StageBounds d m P.n₀ (j - 1) P.u cP CP cL CL C₀ x.endpoint x.r) →
      ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (guardMap (endMap P j) x))
    (hXc : OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 1 y
      (boxTS Cg P P.n₀ P.u E ρ Cb cP CP j (siteCount d m)) (Xc j 0)) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 1 y
      (boxTS Cg P P.n₀ P.u E ρ Cb cP CP j (siteCount d m))
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j 0) := by
  intro x k ω hxRB hx hrun hh hexRB
  have hXcx := hXc x k ω hxRB hx hrun hh hexRB
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 1 y =
      simpleBlock (ts₀, cl₀) (guardMap (endMap P j)) := by
    subst hy
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩), if_neg (show (1 : ℕ) ≠ 0 by norm_num),
      if_pos (show (1 : ℕ) = 1 from rfl), if_pos (show site₀ d m = site₀ d m from rfl)]
  have hex := runOp_simple_exit P ts₀ cl₀ P.n₀ P.u j 1 y _ hop x k ω hrun
  rw [hex] at hXcx ⊢
  have hT : x ∈ TileSweepInv Cg P j P.n₀ P.u E ρ Cb Finset.univ := by
    have := hx.1; rwa [doneUpTo_all] at this
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hXcx⟩
  · exact hkeep x hT (fun _ i => ⟨hcA.trans (hx.2 i).1, (hx.2 i).2.1.trans hCA,
      (hx.2 i).2.2.trans hCA⟩)
      (fun hab => hSBh (j - 1) _ _ (by omega) (by omega) (hT hab).hist)
  · intro i
    cases hab : x.aborted
    · rw [guardMap_live _ x hab, (endMap_endpoint P j x).2.1]; exact hx.2 i
    · rw [guardMap_aborted _ x hab]; exact hx.2 i
  · intro hab'
    cases hab : x.aborted
    · rw [guardMap_live _ x hab]
      have h := (hT hab).physical_end
      unfold endMap
      split_ifs <;> exact h
    · rw [guardMap_aborted _ x hab] at hab'; rw [hab] at hab'; cases hab'

/-- **The final sweep end** `(m + 1, 1, site₀)`: tile phase → final record. -/
theorem boxTS_finalEndOp (Cr cp cg : ℝ) (y : Torus d m) (hnm : P.n₀ ≤ m) (hy : y = site₀ d m)
    (hfin : ∀ x : RunRecord d m, x ∈ TileSweepInv Cg P (m + 1) P.n₀ P.u E ρ Cb Finset.univ →
      (guardMap (endMap P (m + 1)) x).aborted = false →
      guardMap (endMap P (m + 1)) x ∈ FinalGood (d := d) (m := m) P.u E Cr cp cg) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) (m + 1) 1 y
      (boxTS Cg P P.n₀ P.u E ρ Cb cP CP (m + 1) (siteCount d m)) (boxFG P.u E Cr cp cg) := by
  intro x k ω _ hx hrun _ _
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (m + 1) 1 y =
      simpleBlock (ts₀, cl₀) (guardMap (endMap P (m + 1))) := by
    subst hy
    unfold runOp
    rw [if_pos (show P.n₀ < m + 1 ∧ m + 1 ≤ m + 1 from ⟨by omega, le_rfl⟩),
      if_neg (show (1 : ℕ) ≠ 0 by norm_num),
      if_pos (show (1 : ℕ) = 1 from rfl), if_pos (show site₀ d m = site₀ d m from rfl)]
  rw [runOp_simple_exit P ts₀ cl₀ P.n₀ P.u (m + 1) 1 y _ hop x k ω hrun]
  have hT : x ∈ TileSweepInv Cg P (m + 1) P.n₀ P.u E ρ Cb Finset.univ := by
    have := hx.1; rwa [doneUpTo_all] at this
  exact hfin x hT

/-- **The stage operation** `(j, 3, site₀)`, `n₀ < j ≤ m`: clearing phase → start of the sweep
into stage `j + 1`. -/
theorem boxCL_stageOp (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m) (hy : y = site₀ d m)
    (hSBh : ∀ k s rk, P.n₀ ≤ k → k ≤ m → BoundaryHist P.n₀ P.u E ρ Cb k s rk →
      StageBounds d m P.n₀ k P.u cP CP cL CL C₀ s rk)
    (hstage : ∀ (x : RunRecord d m) (D : ClearPhaseData P.n₀ P.u E ρ Cb CA cA PA j x),
      Kn D.old (stageScale P.u (j - 1) m) ≤ 1 / 3 → x.aborted = false →
      BoundaryInv P.n₀ P.u E ρ Cb j (guardMap (stageMapA P j) x))
    (hstart : ∀ z : RunRecord d m, StageBounds d m P.n₀ j P.u cP CP cL CL C₀ z.endpoint z.r →
      IsDampedEndpoint z.endpoint z.r (sweepScale P.u m (j + 1)) → PhysicalIdentity E z →
      StageStartInputs Cg P (j + 1)
        (sweepStartMap (sweepTheta P.u m (j + 1)) (sweepScale P.u m (j + 1)) z)) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 3 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteCount d m))
      (boxTS Cg P P.n₀ P.u E ρ Cb cP CP (j + 1) 0) := by
  intro x k ω _ hx hrun _ hexRB
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 3 y =
      simpleBlock (ts₀, cl₀) (guardMap (stageMap P j)) := by
    subst hy
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩), if_neg (show (3 : ℕ) ≠ 0 by norm_num),
      if_neg (show (3 : ℕ) ≠ 1 by norm_num), if_neg (show (3 : ℕ) ≠ 2 by norm_num),
      if_pos (show j ≤ m ∧ site₀ d m = site₀ d m from ⟨hjm, rfl⟩)]
  have hex := runOp_simple_exit P ts₀ cl₀ P.n₀ P.u j 3 y _ hop x k ω hrun
  rw [hex] at hexRB ⊢
  obtain ⟨⟨⟨hCP, hD⟩, hPh⟩, -⟩ := hx
  cases hab : x.aborted
  swap
  · rw [guardMap_aborted _ x hab]
    refine ⟨?_, hD⟩
    intro hab'
    rw [hab] at hab'; cases hab'
  -- the record before the start lift
  set z : RunRecord d m :=
    (if j = m / 2 then cutoffMap else id) (resetMapA (stageScale P.u j m) x) with hzdef
  have hg : guardMap (stageMap P j) x =
      sweepStartMap (sweepTheta P.u m (j + 1)) (sweepScale P.u m (j + 1)) z := by
    rw [guardMap_live _ x hab]; rfl
  have hzr : z.r = x.r + padV x.endpoint.active (activeReset (stageScale P.u j m) x) := by
    rw [hzdef]; split_ifs <;> rfl
  have hzA : z.endpoint.active = x.endpoint.active := by
    rw [hzdef]; split_ifs <;> rfl
  have hzP : PhysicalIdentity E z := by
    have h := hPh hab
    rw [hzdef]; split_ifs <;> exact h
  obtain ⟨D⟩ := hCP hab
  have hK : Kn D.old (stageScale P.u (j - 1) m) ≤ 1 / 3 :=
    Kn_le_of_stageBounds (hSBh (j - 1) D.old D.rOld (by omega) (by omega) D.hist)
  have hBI := hstage x D hK hab
  rw [stageMapA_eq_stageMap, hg] at hBI
  have hist : BoundaryHist P.n₀ P.u E ρ Cb j z.endpoint z.r := hBI
  have hSB := hSBh j _ _ (by omega) hjm hist
  rw [hg] at hexRB ⊢
  refine ⟨fun hab' => ?_, fun i => ?_⟩
  · have hrb := runBasics_afterStage_pre P (sweepTheta P.u m (j + 1)) (sweepScale P.u m (j + 1))
      (j + 1) (by omega) (by omega) z
      (by rw [Nat.add_sub_cancel, ← hy]; exact hexRB.1) hab'
    have hdamp : IsDampedEndpoint z.endpoint z.r (sweepScale P.u m (j + 1)) := by
      rw [sweepScale_eq_stage P.u (by omega : j + 1 ≤ m + 1), Nat.add_sub_cancel]
      exact hist.damped (by omega)
    refine tileSweepInv_start' (C := Cg) (P := P) (j := j + 1) (sweepScale P.u m (j + 1)) z hab'
      (by omega) (by rw [Nat.add_sub_cancel]; exact hist) (hstart z hSB hdamp hzP) hzP
      hrb.1 hrb.2.1 hrb.2.2
  · show cP ≤ (z.r i).im ∧ (z.r i).im ≤ CP ∧ ‖z.r i‖ ≤ CP
    by_cases hi : i ∈ x.endpoint.active
    · obtain ⟨-, h1, h2, h3⟩ := hSB.1 i (by rw [hzA]; exact hi)
      exact ⟨h1, h2, h3⟩
    · have : z.r i = x.r i := by
        rw [hzr]; simp [padV, hi]
      rw [this]; exact hD i

end Box

/-! ## The initial record -/

/-- The initial committed record before the start lift of the first sweep. -/
def initialPre (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (lab : BirthLabel (Torus d m)) : RunRecord d m :=
  { stage := n₀
    endpoint := initialEndpoint d m E (stageScale u n₀ m) ρ
    r := fun _ => ρ
    sweep := emptyRunSweep
    installed := fun _ => 0
    prefixLength := fun _ => 0
    terminal := ∅
    pending := ∅
    latest := fun _ => lab
    components := ∅
    aborted := false }

theorem initialRecord_eq (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (θ t : ℝ) (lab : BirthLabel (Torus d m)) :
    initialRecord n₀ u E ρ θ t lab = sweepStartMap θ t (initialPre n₀ u E ρ lab) := rfl

/-- **`hInv0`, tile-phase part**: the initial record lies in the tile-phase set of the first
sweep. -/
theorem initialRecord_boxTS (P : TilePlan d m) (E : ℝ) (ρ : ℂ) (Cg Cb cA CA : ℝ)
    (cP CP cL CL C₀ : ℝ) (lab : BirthLabel (Torus d m)) (hnm : P.n₀ < m)
    (hdamp : IsDampedEndpoint (initialEndpoint d m E (stageScale P.u P.n₀ m) ρ) (fun _ => ρ)
      (stageScale P.u P.n₀ m))
    (hSB0 : BoundaryHist P.n₀ P.u E ρ Cb P.n₀ (initialEndpoint d m E (stageScale P.u P.n₀ m) ρ)
      (fun _ => ρ))
    (hSB : StageBounds d m P.n₀ P.n₀ P.u cP CP cL CL C₀
      (initialEndpoint d m E (stageScale P.u P.n₀ m) ρ) (fun _ => ρ))
    (hcA : cA ≤ cP) (hCA : CP ≤ CA)
    (hphys : PhysicalIdentity E (initialPre P.n₀ P.u E ρ lab))
    (hstart : StageStartInputs Cg P (P.n₀ + 1)
      (sweepStartMap (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1))
        (initialPre P.n₀ P.u E ρ lab))) :
    initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab ∈
      boxTS Cg P P.n₀ P.u E ρ Cb cA CA (P.n₀ + 1) 0 := by
  rw [initialRecord_eq]
  refine ⟨fun hab => ?_, fun i => ?_⟩
  · refine tileSweepInv_start' (C := Cg) (P := P) (j := P.n₀ + 1) _ _ rfl (by omega)
      (by rw [Nat.add_sub_cancel]; exact hSB0) hstart hphys
      (fun i _ => Finset.notMem_empty i) (fun _ i _ => Finset.notMem_empty i) ?_
    intro hf
    unfold IsFinalSweep at hf
    exact absurd hf (by omega)
  · obtain ⟨-, h1, h2, h3⟩ := hSB.1 i (Finset.mem_univ i)
    exact ⟨hcA.trans h1, h2.trans hCA, h3.trans hCA⟩

end AndersonAC.AgentS78
