import AndersonAC.AgentS78.Construction.BoxPhasesStage

/-!
# WP10 construction, global run invariant: `BoxInvariantK` of one box (agent-s78box)

`boxInvariantK_of_box`: for one box (tile plan `P`, energy `E`, initial damping `ρ`) and fixed
constants, the kind-split package `BoxInvariantK` with

* `Inv = boxInv P RB TS CL FG` (BoxPhasesCore.lean), `RB n = RunBasics P n ∩ Xg n`,
  `TS = boxTS …`, `CL = boxCL … Xc`, `FG = boxFG …`;
* `rec₀ = initialRecord` (the start lift of the first sweep);

from the per-box forms of the phase facts. The uniform theorem (BoxPhases.lean) supplies them
from the proved phase lemmas and the open contracts.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-- **`BoxInvariantK` of one box from the per-box phase facts.** -/
def boxInvariantK_of_box (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (E : ℝ) (ρ : ℂ) (Cg Cb CA cA PA cP CP cL CL C₀ Cr cp cg c : ℝ)
    (lab : BirthLabel (Torus d m)) (Xg : ℕ → Set (RunRecord d m))
    (Xc : ℕ → ℕ → Set (RunRecord d m))
    (hnm : P.n₀ < m) (hu : 0 < P.u)
    -- run-level part of the clearing package
    (hXg0 : initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1))
      lab ∈ Xg 0)
    (hXg : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ RunBasics P n ∩ Xg n →
      (∀ j r, boxPhase P n = .clear j r → x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j r) →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) ∈
          Xg (n + 1))
    -- stage bounds along every history, damping window
    (hSBh : ∀ k s rk, P.n₀ ≤ k → k ≤ m → BoundaryHist P.n₀ P.u E ρ Cb k s rk →
      StageBounds d m P.n₀ k P.u cP CP cL CL C₀ s rk)
    (hcA : cA ≤ cP) (hCA : CP ≤ CA)
    -- sweep ends
    (hkeep : ∀ j, P.n₀ < j → j ≤ m → ∀ x : RunRecord d m,
      x ∈ TileSweepInv Cg P j P.n₀ P.u E ρ Cb Finset.univ →
      (x.aborted = false → ∀ i, cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA ∧ ‖x.r i‖ ≤ CA) →
      (x.aborted = false → StageBounds d m P.n₀ (j - 1) P.u cP CP cL CL C₀ x.endpoint x.r) →
      ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (guardMap (endMap P j) x))
    (hXcE : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
      OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 1 y
        (boxTS Cg P P.n₀ P.u E ρ Cb cP CP j (siteCount d m)) (Xc j 0))
    (hfinOp : ∀ x : RunRecord d m, x ∈ TileSweepInv Cg P (m + 1) P.n₀ P.u E ρ Cb Finset.univ →
      (guardMap (endMap P (m + 1)) x).aborted = false →
      guardMap (endMap P (m + 1)) x ∈ FinalGood (d := d) (m := m) P.u E Cr cp cg)
    -- clearing operations and the clearing bound
    (hClr : ∀ j y, P.n₀ < j → j ≤ m →
      OpKeepsZ P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n)
        (fun ω => {x | ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) ∧
          x ∈ TrueValues P.n₀ P.u ω}) j 2 y
        (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y))
        (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y + 1)))
    (hbound : ∀ j (y : Torus d m), P.n₀ < j → j ≤ m / 2 →
      ∀ x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y),
      sourcesLaw (Torus d m) (tileOrderSize P)
        (localFirstFail (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x) ≤
          ENNReal.ofReal (birthBound c j))
    -- stage operations and sweep starts
    (hstage : ∀ j, P.n₀ < j → j ≤ m → ∀ (x : RunRecord d m)
      (D : ClearPhaseData P.n₀ P.u E ρ Cb CA cA PA j x),
      Kn D.old (stageScale P.u (j - 1) m) ≤ 1 / 3 → x.aborted = false →
      BoundaryInv P.n₀ P.u E ρ Cb j (guardMap (stageMapA P j) x))
    (hstart : ∀ j, P.n₀ ≤ j → j ≤ m → ∀ z : RunRecord d m,
      StageBounds d m P.n₀ j P.u cP CP cL CL C₀ z.endpoint z.r →
      IsDampedEndpoint z.endpoint z.r (sweepScale P.u m (j + 1)) → PhysicalIdentity E z →
      StageStartInputs Cg P (j + 1)
        (sweepStartMap (sweepTheta P.u m (j + 1)) (sweepScale P.u m (j + 1)) z))
    -- the initial record
    (hdamp0 : IsDampedEndpoint (initialEndpoint d m E (stageScale P.u P.n₀ m) ρ) (fun _ => ρ)
      (stageScale P.u P.n₀ m))
    (hhist0 : BoundaryHist P.n₀ P.u E ρ Cb P.n₀ (initialEndpoint d m E (stageScale P.u P.n₀ m) ρ)
      (fun _ => ρ))
    (hphys0 : PhysicalIdentity E (initialPre P.n₀ P.u E ρ lab))
    -- the true installed values: closure along every block, all terminal at the end
    (hTVop : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      x ∈ TrueValues P.n₀ P.u ω → x ∈ RunBasics P n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) ∈
          TrueValues P.n₀ P.u ω)
    (hAT : ∀ ω : RandomSources (Torus d m) (tileOrderSize P),
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
        (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
        (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
      (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
        (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
        (stageStartIdx d m (m + 2)) ω).aborted = false →
      ∀ i, i ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
        (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
        (stageStartIdx d m (m + 2)) ω).terminal) :
    BoxInvariantK d m P.n₀ P.u E Cr cp cg c Cg P :=
  boxInvariantK_of_core (n₀ := P.n₀) (u := P.u) P hnm.le ts₀ cl₀
    (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
    rfl rfl
    (fun n => RunBasics P n ∩ Xg n)
    (fun j r => boxTS Cg P P.n₀ P.u E ρ Cb cP CP j r)
    (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc)
    (boxFG P.u E Cr cp cg)
    (fun n x k ω hx hrun hh =>
      ⟨runBasics_closed' P P.n₀ P.u ts₀ cl₀ n x k ω hx.1.1 hrun hh,
        hXg n x k ω hx.1 (fun j r hph => by
          have h2 := hx.2
          rw [hph] at h2
          exact h2) hrun hh⟩)
    (fun j y h1 h2 => boxTS_tileOp P ts₀ cl₀ P.n₀ P.u E ρ Cb cP CP _ hu j y h1 h2)
    (fun j y h1 h2 hy => boxTS_endOp P ts₀ cl₀ E ρ Cg Cb CA cA PA cP CP cL CL C₀ Xg Xc j y h1 h2 hy
      hSBh hcA hCA (hkeep j h1 h2) (hXcE j y h1 h2 hy))
    (fun y hy => boxTS_finalEndOp P ts₀ cl₀ E ρ Cg Cb cP CP Xg Cr cp cg y hnm.le hy hfinOp)
    hClr
    (fun j y h1 h2 hy => boxCL_stageOp P ts₀ cl₀ E ρ Cg Cb CA cA PA cP CP cL CL C₀ Xg Xc j y h1 h2 hy
      hSBh (hstage j h1 h2) (hstart j h1.le h2))
    ⟨⟨initialRecord_runBasics P P.n₀ P.u E ρ _ _ lab, hXg0⟩,
      initialRecord_boxTS P E ρ Cg Cb cP CP cP CP cL CL C₀ lab hnm hdamp0 hhist0
        (hSBh P.n₀ _ _ le_rfl hnm.le hhist0) le_rfl le_rfl hphys0
        (hstart P.n₀ le_rfl hnm.le _ (hSBh P.n₀ _ _ le_rfl hnm.le hhist0)
          (by rw [sweepScale_eq_stage P.u (by omega : P.n₀ + 1 ≤ m + 1), Nat.add_sub_cancel]
              exact hdamp0)
          hphys0)⟩
    (fun ω => initialRecord_trueValues P.n₀ P.u E ρ _ _ lab ω)
    (fun n x k ω htv hx hrun hh => hTVop n x k ω htv hx.1 hrun hh)
    hAT
    (fun j y T h1 h2 hT x hx => boxTS_good P P.n₀ P.u E ρ Cb cP CP j y T hT x hx)
    hbound
    (fun ω x hFG hab hinst => by
      obtain ⟨hphys, hdamp, hcard, hr, hlag⟩ := hFG hab
      exact ⟨_, _, hdamp, trueSchurIdentity_of_physical P.n₀ P.u E (trueConfig ω) _
        hinst hphys, hcard, hr, hlag⟩)

end AndersonAC.AgentS78
