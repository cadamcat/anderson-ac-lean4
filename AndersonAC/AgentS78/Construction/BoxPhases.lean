import AndersonAC.AgentS78.Construction.BoxPhasesBox
import AndersonAC.AgentS78.Construction.BoxPhasesClear
import AndersonAC.AgentS78.Construction.ResetRowProof
import AndersonAC.AgentS78.InitialStageFull
import AndersonAC.AgentS78.StageInduction
import AndersonAC.AgentS78.Construction.SweepClosed

/-!
# WP10 construction: the global run invariant and the `BoxInvariantK` assembly (agent-s78box)

DISPATCH 2026-10-14 02:58:56 (agent-s78con3). **`boxInvariantK_of_phases`** is exactly the
`hbox` hypothesis of `uniformCertificateInput_of_boxInvariantsK'` (ClearingSix.lean), from the
proved phase lemmas and the open contracts below (taken as explicit hypotheses):

| contract | owner (status 03:1x) |
|---|---|
| `ActiveCTStatement d` (stage start, Combes–Thomas) | luna-s78actct |
| `StartBridgeStatement` (`startClauses_of_live`, verbatim type) | luna-s78sbridge |
| `SweepEndUniformStatement d` (= `sweepEnd_proof''` with `CA₀ cA₀` chosen before `Cb`) | agent-s78send / agent-s78stransp + luna-s78actct |
| (final sweep: unconditional via `finalSweep_closed` + `finalSweep_good_SB`, lead agent-s78con4) | — |
| `ClearingPhasePackage d` (run-level clauses, DONE step, clearing bound) | agent-s78phase2 + clearing-bound DISPATCH 02:51:56 |
| `RunTrueValuesStatement d` (installed values at the final record, pathwise) | luna-s78truev + clearing true values |

Proved and plugged in: the index bookkeeping and closure (`boxInv_closed`), RunBasics
(`runBasics_closed` with `tileComplete_proof`), tile operations (`tileOp_keeps'`), sweep ends
(`sweepEnd_keeps`, `finalSweep_good`), stage operations (`stage_op_boundary_of_row` with
`resetRow_proof`, `tileSweepInv_start'`, `runBasics_afterStage_pre`), the stage start up to the
two contracts (`tileStartAlgebraic_proof`, `tileStartDecay_of_parts prefixPhys_proof`), the
initial stage (`initial_stage_unconditional`, `boundaryHist_initial`, `stageBounds_of_hist`),
`hgoodT` (`tileGoodCore_of_sweep`), the initial physical identity (`initialPhysical_proof`), `hfinal` (pathwise prestate + `trueSchurIdentity_of_physical`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

/-! ## The open contracts -/

/-- **Stage-start bridge** (luna-s78sbridge, `startClauses_of_live`, verbatim type). -/
def StartBridgeStatement : Prop :=
  ∀ {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ) (z : RunRecord d m),
    StartAlgebraicLive C P j (sweepStartLiveState (sweepTheta P.u m j) z) z.r →
    StartDecayLive C P j (sweepStartLiveState (sweepTheta P.u m j) z) z.r →
    StartClauses C P j z.endpoint z.r (sweepStartLiveState (sweepTheta P.u m j) z)

/-- **The sweep end with uniform assembly constants.** `sweepEnd_proof''` (SweepEndReserve.lean)
concludes `∃ Cb₀, ∀ Cb ≥ Cb₀, ∃ CA₀ cA₀, …`; its proof (`sweepEnd_proof`, SweepEnd.lean:446)
chooses `CA₀ = max (max CA₁ CA₂) cc⁻¹` and `cA₀ = min cA₂ CC⁻¹` independently of `Cb`. The
assembly needs that order, because the stage operation needs `Cb ≥ Cmin(CA, cA, PA)`
(`stage_op_boundary_of_row`). -/
def SweepEndUniformStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
  ∃ CA₀ > (0 : ℝ), ∃ cA₀ > (0 : ℝ), ∃ Cb₀ > (0 : ℝ), ∀ Cb ≥ Cb₀, ∀ CA ≥ CA₀, ∀ cA : ℝ,
    0 < cA → cA ≤ cA₀ → SweepEndStatement d C Cb CA cA cP CP cL CL C₀

/-- **The final residual sweep** (agent-s78final) for some final constants. -/
def FinalSweepUniformStatement (d : ℕ) : Prop :=
  ∀ C Cb : ℝ, 1 ≤ C → 1 ≤ Cb →
  ∃ Cr cp cg : ℝ, 0 < cp ∧ 0 < cg ∧ FinalSweepStatement d C Cb Cr cp cg

/-- **Physical identity of the initial record** (02-state.tex:231–247 at the initial stage:
`M = H₀ − E` on the whole torus, nothing installed). -/
def InitialPhysicalStatement : Prop :=
  ∀ (d m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (lab : BirthLabel (Torus d m)),
    PhysicalIdentity E (initialPre n₀ u E ρ lab)

/-- **Installed values at the final record** (02-state.tex:96–110, pathwise): along the actual
run from the initial record, the record entering stage `m + 2` carries `λ V(ω)`. -/
def RunTrueValuesStatement (d : ℕ) : Prop :=
  ∀ (m : ℕ) (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (E : ℝ) (ρ : ℂ)
    (lab : BirthLabel (Torus d m)) (ω : RandomSources (Torus d m) (tileOrderSize P)),
    1 ≤ P.n₀ → 4 * P.n₀ ≤ m → P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
      (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
      (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
    (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
      (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
      (stageStartIdx d m (m + 2)) ω).aborted = false →
    ∀ i, (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
      (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
      (stageStartIdx d m (m + 2)) ω).installed i =
        OAI.Anderson.scaleCoupling P.n₀ P.u * (trueConfig ω i : ℝ)

/-- **Every site is terminal at the final record** (new contract): along the actual run from the
initial record, the non-aborted record entering stage `m + 2` has all sites terminal (inactive
sites became terminal at their clearing; the final residual sweep makes the active ones
terminal). -/
def RunAllTerminalStatement (d : ℕ) : Prop :=
  ∀ (m : ℕ) (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (E : ℝ) (ρ : ℂ)
    (lab : BirthLabel (Torus d m)) (ω : RandomSources (Torus d m) (tileOrderSize P)),
    1 ≤ P.n₀ → 4 * P.n₀ ≤ m → P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
      (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
      (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
    (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
      (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
      (stageStartIdx d m (m + 2)) ω).aborted = false →
    ∀ i, i ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
      (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
      (stageStartIdx d m (m + 2)) ω).terminal

/-- **The true installed values are kept by every block** (route R2), along the answers of `ω`,
from `RunBasics` records (`runTVClosure_of_parts`, BoxPhasesTrue.lean). -/
def RunTVClosureStatement (d : ℕ) : Prop :=
  ∀ (m : ℕ) (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (ω : RandomSources (Torus d m) (tileOrderSize P)) (n : ℕ) (x : RunRecord d m) (k : ℕ),
    x ∈ RunBasics P n → x ∈ TrueValues P.n₀ P.u ω →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k' ω) =
        false) →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) =
        true →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) ∈
        TrueValues P.n₀ P.u ω

/-- **The clearing phase of one box**: a run-level invariant `Xg` (closed under every block
together with `RunBasics`), the record-level part `Xc j` of the clearing phase of stage `j`
(entered at the sweep end, kept by the clearing operations), the DONE step, and the clearing
first-failure bound on the clearing-phase set (C4b through the S6 bridge). The clearing-phase
set itself, `boxCL = ClearPhase ∩ Damp ∩ PhysSet ∩ Xc`, is kept by `boxCL_clearOp`
(BoxPhasesClear.lean). -/
structure ClearingBoxFacts {d m : ℕ} (P : TilePlan d m) (ts₀ : TileScratch d m)
    (cl₀ : ClearScratch d m) (E : ℝ) (ρ : ℂ) (Cg Cb CA cA PA cP CP c : ℝ)
    (lab : BirthLabel (Torus d m)) where
  Xg : ℕ → Set (RunRecord d m)
  Xc : ℕ → ℕ → Set (RunRecord d m)
  hXg0 : initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1))
    lab ∈ Xg 0
  hXg : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ RunBasics P n ∩ Xg n →
    (∀ j r, boxPhase P n = .clear j r → x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j r) →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k' ω) =
        false) →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) =
        true →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) ∈
        Xg (n + 1)
  hXcE : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 1 y
      (boxTS Cg P P.n₀ P.u E ρ Cb cP CP j (siteCount d m)) (Xc j 0)
  /-- The clearing operations keep the record part of the clearing phase (scan position
  `rank y → rank y + 1`). -/
  hXcC : ∀ j y, P.n₀ < j → j ≤ m / 2 →
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ Xg n) j 2 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y)) (Xc j (siteRank d m y + 1))
  /-- On non-clearing stages the record part is monotone in the scan position. -/
  hXcId : ∀ j r, P.n₀ < j → m / 2 < j → j ≤ m → Xc j r ⊆ Xc j (r + 1)
  /-- **The DONE step** (07-assembly.tex:390–433; agent-s78phase2's `ClearingDoneStatement`):
  the committed endpoint extends the stage assembly by one clearing, and the DONE record
  satisfies the physical identity (02-state.tex:231–247). Route R2: along the answers of
  `ω ∉ exceptionalSet`, from records with the true installed values. -/
  hDone : ∀ j (y : Torus d m), P.n₀ < j → j ≤ m / 2 →
    ∀ (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P)),
      ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
      x ∈ TrueValues P.n₀ P.u ω →
      x ∈ RunBasics P (opIndex d m j 2 y) ∩ Xg (opIndex d m j 2 y) →
      x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y) → x.aborted = false →
      (∀ k' < k, (clearingBlock (d := d) (m := m) P.n₀ j P.u y).halted
        (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k' ω) =
          false) →
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.core
        ≠ ∅ →
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.failed
        = false →
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.done
        = true →
      ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (clearingDoneExit x
        (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2) ∧
        PhysicalIdentity E (clearingDoneExit x
          (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2)
  hbound : ∀ j (y : Torus d m), P.n₀ < j → j ≤ m / 2 →
    ∀ x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA cP CP Xc j (siteRank d m y),
    sourcesLaw (Torus d m) (tileOrderSize P)
      (localFirstFail (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x) ≤
        ENNReal.ofReal (birthBound c j)

/-- **The clearing-phase package** (agent-s78phase2 + the clearing-bound DISPATCH 02:51:56):
the clearing facts of every large box, for assembly constants `CA ≥ CA₀`, `cA ≤ cA₀`,
`PA ≥ PA₀` and history constants `Cb ≥ Cb₀`, uniformly in the boxes. -/
def ClearingPhasePackage (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ Cg : ℝ, 1 ≤ Cg →
  ∃ CA₀ cA₀ PA₀ : ℝ, 0 < cA₀ ∧ 0 ≤ PA₀ ∧
  ∀ CA cA PA : ℝ, CA₀ ≤ CA → 0 < cA → cA ≤ cA₀ → PA₀ ≤ PA →
  ∃ Cb₀ : ℝ, ∀ Cb : ℝ, Cb₀ ≤ Cb → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
  ∀ (n₀ m : ℕ), N ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
  ∀ (E : ℝ) (ρ : ℂ) (P : TilePlan d m), P.n₀ = n₀ → P.u = u →
  (∀ k s rk, n₀ ≤ k → k ≤ m → BoundaryHist n₀ u E ρ Cb k s rk →
    StageBounds d m n₀ k u cP CP cL CL C₀ s rk) →
  ∀ (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (lab : BirthLabel (Torus d m)),
  Nonempty (ClearingBoxFacts P ts₀ cl₀ E ρ Cg Cb CA cA PA cP CP c lab)


/-- The Schur complement onto the whole index set is the matrix itself. -/
theorem activeSchur_univ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    SolS78.activeSchur B Finset.univ = B.submatrix (fun i : (Finset.univ : Finset ι) => i.val)
      (fun i : (Finset.univ : Finset ι) => i.val) := by
  haveI : IsEmpty {i : ι // i ∉ (Finset.univ : Finset ι)} :=
    ⟨fun ⟨i, hi⟩ => hi (Finset.mem_univ i)⟩
  unfold SolS78.activeSchur
  ext a b
  simp [Matrix.mul_apply]

/-- **`InitialPhysicalStatement` holds**: `M = H₀ − E` on the whole torus and nothing is
installed. -/
theorem initialPhysical_proof : InitialPhysicalStatement := by
  intro d m n₀ u E ρ lab
  unfold PhysicalIdentity
  show (initialEndpoint d m E (stageScale u n₀ m) ρ).M.submatrix
      (fun i : (Finset.univ : Finset (Torus d m)) => i.val)
      (fun i : (Finset.univ : Finset (Torus d m)) => i.val) =
    SolS78.activeSchur (installedShifted E (initialPre n₀ u E ρ lab)) Finset.univ
  rw [activeSchur_univ]
  ext a b
  simp [initialEndpoint, installedShifted, initialPre, OAI.Anderson.periodicHamiltonian,
    AndersonAC.S3.freeHopping, AndersonAC.S3.basisStep, OAI.Anderson.torusBasisVector]
  all_goals rfl

/-! ## Scales -/

/-- All stage scales from `n₀` on are small for large `n₀`. -/
theorem stageScale_small {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, ∀ n₀ m j : ℕ, N ≤ n₀ → n₀ ≤ j → n₀ ≤ m → ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      stageScale u j m < t := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos ht) (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨N, fun n₀ m j hN0 hj hm u hu => ?_⟩
  have hk : ∀ k, N ≤ k → u / (4 : ℝ) ^ k < t / 2 := by
    intro k hk
    calc u / (4 : ℝ) ^ k ≤ 1 / (4 : ℝ) ^ k := by gcongr; exact hu.2
      _ = (1 / 4 : ℝ) ^ k := by rw [one_div_pow]
      _ ≤ (1 / 4 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ < t / 2 := hN
  unfold stageScale
  linarith [hk j (by omega), hk m (by omega)]

/-- The sweep scales of the sweeps `n₀ < j ≤ m + 1` are small for large `n₀`. -/
theorem sweepScale_small {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, ∀ n₀ m j : ℕ, N ≤ n₀ → n₀ < j → j ≤ m + 1 → n₀ ≤ m →
      ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1, sweepScale u m j < t := by
  obtain ⟨N, hN⟩ := stageScale_small ht
  refine ⟨N, fun n₀ m j h1 h2 h3 h4 u hu => ?_⟩
  rw [sweepScale_eq_stage u h3]
  exact hN n₀ m (j - 1) h1 (by omega) h4 u hu

/-- `stageBounds_of_hist` with the threshold `N` uniform in the torus size `m` (same proof). -/
theorem stageBounds_of_hist_unif {d : ℕ} (hd : 3 ≤ d) (cP CP cL CL C : ℝ) (hcP : 0 < cP)
    (hCP : cP ≤ CP) (hcL : 0 < cL) (hCL : 0 < CL) (hC : 1 ≤ C) (C₀ : ℝ)
    (hC₀ : 4 / cP ^ 2 + 1 ≤ C₀) :
    ∃ N : ℕ, ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (k : ℕ) (s : Endpoint (Torus d m))
      (rk : Torus d m → ℂ),
      N ≤ n₀ → 1 ≤ n₀ → 4 * n₀ ≤ m → k ≤ m → n₀ ≤ k → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      C * stageScale u n₀ m ^ (0.10 * delta) ≤ 1 / 4 →
      StageBounds d m n₀ n₀ u cP CP cL CL C₀
        (initialEndpoint d m E (stageScale u n₀ m) ρ) (fun _ => ρ) →
      matrixNorm (squareKernel (normalizedInverse (initialEndpoint d m E (stageScale u n₀ m) ρ)
        (stageScale u n₀ m))) ≤ 1 / 4 →
      BoundaryHist n₀ u E ρ C k s rk →
      StageBounds d m n₀ k u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀ s rk := by
  obtain ⟨N, hN⟩ := PrefixInduction.prefix_deterministic_induction_ge d hd cP CP cL CL (8 * C + 4)
    hcP hCP hcL hCL (by linarith) C₀ hC₀
  refine ⟨N, fun m n₀ u E ρ k s rk hN0 hn₀ hm hkm hk hu hsmall hSB hK hist => ?_⟩
  obtain ⟨state, r, h0, hr0, hk1, hk2, hst, hph, hre, hro, hke, hco, hme⟩ := hist
  have := hN m n₀ k u (prefix_of_steps hu hC hn₀ hkm state r hsmall
    (fun n h1 h2 => (hst n h1 h2).some) hph hre hro hke hco hme) hN0 hm hkm hu
    (by show StageBounds d m n₀ n₀ u cP CP cL CL C₀ (state n₀) (r n₀); rw [h0, hr0]; exact hSB)
    (by show matrixNorm (squareKernel (normalizedInverse (state n₀) (stageScale u n₀ m))) ≤ 1 / 4
        rw [h0]; exact hK) k hk le_rfl
  rw [← hk1, ← hk2]
  exact this

/-! ## The assembly -/

/-- **WP10: the per-box run invariant packages** (`hbox` of
`uniformCertificateInput_of_boxInvariantsK'`), from the open contracts. -/
theorem boxInvariantK_of_phases (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hCT : ActiveCTStatement d) (hbridge : StartBridgeStatement)
    (hend : SweepEndUniformStatement d)
    (hclr : ClearingPhasePackage d) (hRTV : RunTVClosureStatement d)
    (hAT : RunAllTerminalStatement d) :
    ∀ C : ℝ, 1 ≤ C → ∃ Cg : ℝ, 1 ≤ Cg ∧ ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariantK d m n₀ u E Cr cp cg c Cg P) := by
  intro C hC
  -- the initial stage and the stage constants
  obtain ⟨nmin, cP0, CP0, cL0, CL0, C₀S, -, hcP0, hCP0, hcL0, hCL0, hC0S, hinit⟩ :=
    initial_stage_unconditional hd e₂ he₂
  set C₀ := max C₀S (4 / cP0 ^ 2 + 1) with hC₀def
  have hC₀ : 0 < C₀ := lt_of_lt_of_le hC0S (le_max_left _ _)
  have hcP : 0 < cP0 / 2 := by positivity
  have hCPle : cP0 / 2 ≤ 2 * CP0 := by linarith
  have hcL : 0 < cL0 / 2 := by positivity
  have hCL : 0 < 2 * CL0 := by positivity
  -- the stage start (monotone constants)
  obtain ⟨Ca, hCa, ta, hta, ha⟩ := tileStartAlgebraic_proof d hd (cP0 / 2) (2 * CP0) (cL0 / 2)
    (2 * CL0) C₀ hcP hCPle hcL hCL hC₀
  obtain ⟨Cd, hCd, td, htd, hdc⟩ := tileStartDecay_of_parts prefixPhys_proof hCT (cP0 / 2)
    (2 * CP0) (cL0 / 2) (2 * CL0) C₀ hcP hCPle hcL hCL hC₀
  set Cg := max (max Ca Cd) C with hCgdef
  have hCg1 : 1 ≤ Cg := hCa.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCaCg : Ca ≤ Cg := (le_max_left _ _).trans (le_max_left _ _)
  have hCdCg : Cd ≤ Cg := (le_max_right _ _).trans (le_max_left _ _)
  have hCCg : C ≤ Cg := le_max_right _ _
  -- the sweep end and the clearing package: assembly constants
  obtain ⟨CA₀, hCA₀, cA₀, hcA₀, Cb₀, hCb₀, hSE⟩ := hend (cP0 / 2) (2 * CP0) (cL0 / 2) (2 * CL0) C₀
    hcP hCPle hcL hCL hC₀ Cg hCg1
  obtain ⟨CAc, cAc, PAc, hcAc, hPAc, hpkg⟩ := hclr (cP0 / 2) (2 * CP0) (cL0 / 2) (2 * CL0) C₀
    hcP hCPle hcL hCL hC₀ Cg hCg1
  set CA := max (max CA₀ CAc) (max (2 * CP0) 1) with hCAdef
  set cA := min (min cA₀ cAc) (cP0 / 2) with hcAdef
  have hCA1 : 1 ≤ CA := (le_max_right _ _).trans (le_max_right _ _)
  have hCAP : 2 * CP0 ≤ CA := (le_max_left _ _).trans (le_max_right _ _)
  have hcApos : 0 < cA := lt_min (lt_min hcA₀ hcAc) hcP
  have hcAP : cA ≤ cP0 / 2 := min_le_right _ _
  obtain ⟨Cmin, hCmin, hst⟩ := stage_op_boundary_of_row hd (resetRow_proof d hd) CA cA PAc hCA1
    hcApos hPAc
  obtain ⟨Cbc, hpkg2⟩ := hpkg CA cA PAc ((le_max_right _ _).trans (le_max_left _ _)) hcApos
    ((min_le_left _ _).trans (min_le_right _ _)) le_rfl
  set Cb := max (max Cb₀ Cmin) (max Cbc 1) with hCbdef
  have hCb1 : 1 ≤ Cb := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨tst, htst, hst'⟩ := hst Cb ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨c, hc, Nc, hpkg3⟩ := hpkg2 Cb ((le_max_left _ _).trans (le_max_right _ _))
  have hSEs := hSE Cb ((le_max_left _ _).trans (le_max_left _ _)) CA
    ((le_max_left _ _).trans (le_max_left _ _)) cA hcApos ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨tse, htse, hkeepU⟩ := sweepEnd_keeps hSEs
  -- the final sweep (unconditional, `finalSweep_closed`; stage bounds at `m` from the history)
  obtain ⟨tfs, htfs, hfinU⟩ := finalSweep_good_SB (finalSweep_closed d (cP0 / 2) (2 * CP0)
    (cL0 / 2) (2 * CL0) C₀ hcP hCPle hcL hCL hC₀ Cg hCg1 Cb)
  have hcg : 0 < cP0 / 2 / 2 := by positivity
  -- stage bounds along every history
  obtain ⟨Nh, hNh⟩ := stageBounds_of_hist_unif hd cP0 CP0 cL0 CL0 Cb hcP0 hCP0 hcL0 hCL0 hCb1 C₀
    (le_max_right _ _)
  -- smallness of the scales
  obtain ⟨tpow, htpow, hpow⟩ := AgentS45.power_small (e := 0.10 * delta) (a := 1 / (4 * Cb))
    (by norm_num [delta]) (by positivity)
  set tt := min (min (min ta td) (min tst tse)) (min tfs tpow) with htt
  have htt0 : 0 < tt := lt_min (lt_min (lt_min hta htd) (lt_min htst htse)) (lt_min htfs htpow)
  have htta : tt ≤ ta := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have httd : tt ≤ td := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have httst : tt ≤ tst := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have httse : tt ≤ tse := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have httfs : tt ≤ tfs := (min_le_right _ _).trans (min_le_left _ _)
  have httpow : tt ≤ tpow := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Ns, hNs⟩ := stageScale_small htt0
  obtain ⟨Nw, hNw⟩ := sweepScale_small htt0
  refine ⟨Cg, hCg1, 2 * CP0, cP0 / 2, cP0 / 2 / 2, c, hcP, hcg, hc, max (max (max nmin Nh) (max Nc Ns)) (max Nw 1), ?_⟩
  intro n₀ m hN hm u hu E hE P hPn hPu hfacts
  subst hPn hPu
  have hn1 : 1 ≤ P.n₀ := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNmin : nmin ≤ P.n₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN))
  have hNh' : Nh ≤ P.n₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN))
  have hNc' : Nc ≤ P.n₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
  have hNs' : Ns ≤ P.n₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
  have hNw' : Nw ≤ P.n₀ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hnm : P.n₀ < m := by omega
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  have hsw : ∀ j, P.n₀ < j → j ≤ m + 1 → sweepScale P.u m j < tt :=
    fun j h1 h2 => hNw P.n₀ m j hNw' h1 h2 hnm.le P.u hu
  have hss : ∀ j, P.n₀ ≤ j → stageScale P.u j m < tt :=
    fun j h1 => hNs P.n₀ m j hNs' h1 hnm.le P.u hu
  -- the initial damping
  obtain ⟨ρf, -, hρ⟩ := hinit P.n₀ hNmin m hm P.u hu
  obtain ⟨hdamp0, hSB0, hK0⟩ := hρ E hE
  have hsmall : Cb * stageScale P.u P.n₀ m ^ (0.10 * delta) ≤ 1 / 4 := by
    have hs := stageScale_pos' hu P.n₀ m
    have hlt := hpow _ hs ((hss P.n₀ le_rfl).trans_le httpow)
    have hCbpos : 0 < Cb := lt_of_lt_of_le one_pos hCb1
    have h' : stageScale P.u P.n₀ m ^ (0.10 * delta) ≤ 1 / (4 * Cb) := le_of_lt hlt
    calc Cb * stageScale P.u P.n₀ m ^ (0.10 * delta) ≤ Cb * (1 / (4 * Cb)) :=
          mul_le_mul_of_nonneg_left h' hCbpos.le
      _ = 1 / 4 := by field_simp
  have hSB0' := stageBounds_mono_C0 (le_max_left C₀S (4 / cP0 ^ 2 + 1)) hSB0
  have hSBh : ∀ k s rk, P.n₀ ≤ k → k ≤ m → BoundaryHist P.n₀ P.u E (ρf E) Cb k s rk →
      StageBounds d m P.n₀ k P.u (cP0 / 2) (2 * CP0) (cL0 / 2) (2 * CL0) C₀ s rk :=
    fun k s rk h1 h2 hh => hNh m P.n₀ P.u E (ρf E) k s rk hNh' hn1 hm h2 h1 hu hsmall hSB0' hK0 hh
  have hhist0 := boundaryHist_initial P.n₀ P.u E (ρf E) Cb cP0 CP0 cL0 CL0 C₀S hdamp0 hSB0
  -- the scratch defaults and the initial label
  let lab : BirthLabel (Torus d m) := ⟨0, BirthType.tile, site₀ d m⟩
  let rec₀ := initialRecord P.n₀ P.u E (ρf E) (sweepTheta P.u m (P.n₀ + 1))
    (sweepScale P.u m (P.n₀ + 1)) lab
  let ts₀ : TileScratch d m := initScratch rec₀
  let cl₀ : ClearScratch d m := clearInitScratch 0 P.u (site₀ d m) rec₀
  obtain ⟨F⟩ := hpkg3 P.n₀ m hNc' hm P.u hu E (ρf E) P rfl rfl hSBh ts₀ cl₀ lab
  refine ⟨boxInvariantK_of_box P ts₀ cl₀ E (ρf E) Cg Cb CA cA PAc (cP0 / 2) (2 * CP0) (cL0 / 2)
    (2 * CL0) C₀ (2 * CP0) (cP0 / 2) (cP0 / 2 / 2) c lab F.Xg F.Xc hnm hu0 F.hXg0 F.hXg hSBh hcAP hCAP ?_ F.hXcE ?_
    (fun j y h1 h2 => if hjc : j ≤ m / 2 then
        boxCL_clearOpZ P ts₀ cl₀ E (ρf E) Cb CA cA PAc (cP0 / 2) (2 * CP0) F.Xg F.Xc j y h1 hjc
          (F.hDone j y h1 hjc) (F.hXcC j y h1 hjc)
      else (boxCL_clearId P ts₀ cl₀ E (ρf E) Cb CA cA PAc (cP0 / 2) (2 * CP0) F.Xg F.Xc j y hjc
          (fun r => F.hXcId j r h1 (by omega) h2)).toZ _ _ _ _ _ _ _)
    F.hbound ?_ ?_ hdamp0 hhist0 (initialPhysical_proof d m P.n₀ P.u E (ρf E) lab)
    (fun n x k ω htv hx hrun hh => hRTV m P ts₀ cl₀ ω n x k hx htv hrun hh)
    (fun ω => hAT m P ts₀ cl₀ E (ρf E) lab ω hn1 hm hu)⟩
  · -- sweep ends of digit stages
    intro j h1 h2 x hx hdx hsb
    exact hkeepU rfl rfl hu hn1 h1 h2 (by omega) hCA1 hcApos hPAc
      ((hsw j h1 (by omega)).trans_le httse) x hx hdx hsb
  · -- the final sweep end
    intro x hx hab
    exact hfinU rfl rfl hu hnm.le ((hsw (m + 1) (by omega) le_rfl).trans_le httfs) x hx
      (fun hab' => hSBh m x.endpoint x.r hnm.le le_rfl (hx hab').hist) hab
  · -- stage operations
    intro j h1 h2 x D hK hab
    exact hst' P E (ρf E) j x D hu h1 ((hss (j - 1) (by omega)).trans_le httst) hK hab
  · -- sweep starts
    intro j h1 h2 z hSB hdz hpz
    have hSB' : StageBounds d m P.n₀ (j + 1 - 1) P.u (cP0 / 2) (2 * CP0) (cL0 / 2) (2 * CL0) C₀
        z.endpoint z.r := by
      rw [Nat.add_sub_cancel]; exact hSB
    have hsj := hsw (j + 1) (by omega) (by omega)
    obtain ⟨hA1, hA3⟩ := ha Cg hCaCg m P.n₀ P.u P (j + 1) z rfl rfl hu (by omega) (by omega)
      (hsj.trans_le htta) hSB' hdz (hfacts (j + 1)).energy_eq (hfacts (j + 1)).b_eq
      (hfacts (j + 1)).site_eq
    have hA2 := hdc Cg hCdCg m P.n₀ P.u E P (j + 1) z rfl rfl hu (by omega) (by omega)
      (hsj.trans_le httd) hSB' hdz hpz (hfacts (j + 1)).dist_eq
    exact ⟨planClauses_of_cover P (j + 1) (hfacts (j + 1)) hCCg hCg1,
      hbridge Cg P (j + 1) z hA1 hA2, hA3⟩

end AndersonAC.AgentS78
