import AndersonAC.AgentS78.Construction.RunOpsData
import AndersonAC.AgentS78.Construction.RunOpsAttempt
import AndersonAC.AgentS78.Construction.RunOpsFinite
import AndersonAC.AgentS78.Construction.RunOpsFiniteTV

/-!
# Per-box run inputs after discharging the dichotomy

`RunOpsInputs` is `RunOpsData` with (i) the almost-sure reaching `hfinite` replaced by halting
bounds on the invariant, tile halting patterns, and deterministic halting of the clearing
blocks by step `Kc` (`runOps_finite_det`), and (ii) the snapshot dichotomy
`hdich` replaced by three properties of the clearing block (keeps the components; relabels or clears the eligible
component it attempts; keeps every other pending site and its label), through `runOps_dich`,
`runOps_att` and `runOps_loc`. `uniformCertificateInput_of_runOpsInputs` assembles
these conditions into a uniform certificate input.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources sourcesLaw querySigns)

/-- Per-box run inputs after discharging the schedule dichotomy. -/
structure RunOpsInputs (d m n₀ : ℕ) (u E Cr cp cg Ch c : ℝ) where
  P : TilePlan d m
  hu : 0 < P.u
  ClSc : Type
  [mClSc : MeasurableSpace ClSc]
  ts₀ : TileScratch d m
  cl₀ : ClSc
  clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc)
  clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m)
  rec₀ : RunRecord d m
  hpend₀ : rec₀.pending = ∅
  hrec₀ : rec₀.aborted = false
  htmark : TileMarkingStatement
  htquery : TileQueryStatement
  htpat : TilePatternStatement
  htabort : TileAbortStatement
  hdiam : ∀ j (T : Fin (P.cover j).cover.count), ∀ y ∈ tileSites (P.cover j) T, physicalDistance d m y (tileAnchor (P.cover j) T) ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))
  hcmeas : ∀ j y, (clr j y).IsMeasurable
  hcorders : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω o, (clr j y).halted (localState M (clr j y) x k ω) = false → (clr j y).next (localState M (clr j y) x k ω) = Query.nextOrder o → o ∈ S ∧ ((List.range k).filter fun k' => (clr j y).halted (localState M (clr j y) x k' ω) = false ∧ (clr j y).next (localState M (clr j y) x k' ω) = Query.nextOrder o).length < M o
  hcaux : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω a, (clr j y).halted (localState M (clr j y) x k ω) = false → (clr j y).next (localState M (clr j y) x k ω) = Query.auxiliary a → a ∈ S ∧ ∀ k' < k, (clr j y).halted (localState M (clr j y) x k' ω) = false → (clr j y).next (localState M (clr j y) x k' ω) ≠ Query.auxiliary a
  hcpatm : ∀ j y, Measurable (clrPat j y)
  hclocal : ∀ j y x, DependsOnly (Torus d m) (M := tileOrderSize P) (clrPat j y x) (localFirstFail (tileOrderSize P) (clr j y) x)
  hcmark : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true → ∀ z ∈ ((clr j y).exit s).pending, (z ∈ x.pending ∧ ((clr j y).exit s).latest z = x.latest z) ∨ (((clr j y).exit s).latest z = ⟨j, BirthType.clearing, y⟩ ∧ (clr j y).firstFail s = true ∧ physicalDistance d m z y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
  hcabort : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true → ((clr j y).exit s).aborted = true → x.aborted = true
  hcquery : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)), (∀ k' < k, (clr j y).halted (localState (tileOrderSize P) (clr j y) x k' ω) = false) → (clr j y).halted (localState (tileOrderSize P) (clr j y) x k ω) = true → declaredFresh ((clr j y).exit (localState (tileOrderSize P) (clr j y) x k ω)) ⊆ declaredFresh x ∧ ∀ k' < k, ∀ z ∈ declaredFresh ((clr j y).exit (localState (tileOrderSize P) (clr j y) x k ω)), z ∉ querySigns (Torus d m) ((clr j y).next (localState (tileOrderSize P) (clr j y) x k' ω))
  hcpat : ∀ j y x, (∀ z ∈ (clrPat j y x).signs, z ∈ declaredFresh x) ∧ (clrPat j y x).orders = ∅
  Inv : ℕ → Set (RunRecord d m)
  hInv0 : rec₀ ∈ Inv 0
  /-- route R2: kept only off the null `exceptionalSet`, on records with the true values of `ω` -/
  hInv : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
    ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
    x ∈ TrueValues P.n₀ P.u ω → x ∈ Inv n →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω) = false) →
    (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) = true →
    (scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) ∈ Inv (n + 1)
  hTV0 : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), rec₀ ∈ TrueValues P.n₀ P.u ω
  /-- the true installed values are kept jointly with `Inv` -/
  hTV : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
    ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
    x ∈ TrueValues P.n₀ P.u ω → x ∈ Inv n →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω) = false) →
    (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) = true →
    (scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) ∈
        TrueValues P.n₀ P.u ω
  hbound : ∀ n, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P) (localFirstFail (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x) ≤ ENNReal.ofReal (birthBound c (slotScaleOf d m n))
  hfinal : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) → blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (m + 2)) ω ≠ ⊤ → (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (m + 2)) ω).aborted = false → ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ), IsDampedEndpoint s r (OAI.Anderson.scaleHeight m P.u) ∧ TrueSchurIdentity P.n₀ P.u E (trueConfig ω) s ∧ Fintype.card (Torus d m) ≤ 2 * s.active.card ∧ (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧ (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)
  hthalt : TileHaltPatternStatement
  /-- clearing blocks halt deterministically by step `Kc` (heat limit plus core size) -/
  Kc : ℕ
  hchalt : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)), Kc ≤ k → ω ∉ notHalted (tileOrderSize P) (clr j y) x k
  ε : ℕ → ℕ → ℝ
  hε0 : ∀ n k, 0 ≤ ε n k
  hε : ∀ n, Filter.Tendsto (ε n) Filter.atTop (nhds 0)
  hhalt : ∀ n k, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P) (notHalted (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k) ≤ ENNReal.ofReal (ε n k)
  hCh : 1 ≤ Ch
  huI : P.u ∈ Set.Ioc (0 : ℝ) 1
  hccomp : ∀ j y x s, BlockReach (clr j y) x s → (clr j y).halted s = true → ((clr j y).exit s).components = x.components
  hcrelabel : ∀ j (z : Torus d m) x s, BlockReach (clr j z) x s → (clr j z).halted s = true → x.aborted = false → clearingScheduled j m → (∃ R : Finset (Torus d m), x.components = snapshotComponents R (separationRadius j)) → ∀ Bc ∈ x.components, z ∈ Bc → (∀ v ∈ Bc, (siteRank d m z).val ≤ (siteRank d m v).val) → (Bc.card : ℝ) ≤ stageScale P.u j m ^ (-nu d) → ∀ w ∈ Bc, w ∈ ((clr j z).exit s).pending → ((clr j z).exit s).latest w = ⟨j, BirthType.clearing, z⟩
  hckeep : ∀ j (z : Torus d m) x s, BlockReach (clr j z) x s → (clr j z).halted s = true → ∀ w ∈ x.pending, (∀ Bc ∈ x.components, w ∈ Bc → z ∈ Bc → (∀ v ∈ Bc, (siteRank d m z).val ≤ (siteRank d m v).val) → ¬ ((Bc.card : ℝ) ≤ stageScale P.u j m ^ (-nu d))) → w ∈ ((clr j z).exit s).pending ∧ ((clr j z).exit s).latest w = x.latest w
  hn₀ : P.n₀ = n₀
  hu' : P.u = u

attribute [instance] RunOpsInputs.mClSc

theorem blockRun_of_runOpsInputs {d m n₀ : ℕ} {u E Cr cp cg Ch c : ℝ} (hd : 3 ≤ d)
    (D : RunOpsInputs d m n₀ u E Cr cp cg Ch c) :
    Nonempty (BlockRun d m n₀ u E Cr cp cg Ch c 1) := by
  have horders := runOps_orders D.P D.ts₀ D.cl₀ D.clr D.hcorders
  have haux := runOps_aux D.P D.ts₀ D.cl₀ D.clr (tileOrderSize D.P) (fun j y S => D.hcaux j y _ S)
  have h := blockRun_of_runOps D.P E Cr cp cg Ch c D.hu D.ts₀ D.cl₀ D.clr D.clrPat D.rec₀ D.hpend₀ D.hrec₀ D.htmark D.htquery D.htpat D.htabort D.hdiam D.hcmeas D.hcorders D.hcaux D.hcpatm D.hclocal D.hcmark D.hcabort D.hcquery D.hcpat (runOps_finite_det_tv D.P D.ts₀ D.cl₀ D.clr D.rec₀ D.hcmeas D.hcorders D.hcaux D.htquery D.hcquery D.hthalt D.Kc D.hchalt D.hu E D.Inv D.hInv0 D.hInv D.hTV0 D.hTV D.ε D.hε0 D.hε D.hhalt) D.Inv D.hInv0 D.hInv D.hTV0 D.hTV D.hbound (runOps_dich (by omega) D.P D.ts₀ D.cl₀ D.clr (tileOrderSize D.P) D.rec₀ _ _ (runOrderSet_disjoint D.P) horders haux Ch D.hCh D.huI (runOps_mark D.P D.ts₀ D.cl₀ D.clr Ch D.htmark D.hdiam D.hcmark) (runOps_att D.P D.ts₀ D.cl₀ D.clr (tileOrderSize D.P) D.rec₀ _ _ D.huI (runOrderSet_disjoint D.P) horders haux D.hrec₀ D.htabort D.hcabort D.hccomp D.hcrelabel) (runOps_loc D.P D.ts₀ D.cl₀ D.clr (tileOrderSize D.P) D.rec₀ _ _ (runOrderSet_disjoint D.P) horders haux D.hrec₀ D.htabort D.hcabort D.hccomp D.hckeep)) D.hfinal
  rw [D.hn₀, D.hu'] at h
  exact h

/-- **UniformCertificateInput from the per-box inputs** (dichotomy discharged). -/
theorem uniformCertificateInput_of_runOpsInputs
    (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (Cr cp cg Ch c : ℝ) (hcp : 0 < cp) (hcg : 0 < cg) (hCh : 1 ≤ Ch) (hc : 0 < c) (N₀ : ℕ)
    (hbox : ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      Nonempty (RunOpsInputs d m n₀ u E Cr cp cg Ch c)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_blockRuns' d hd e₂ Cr cp cg Ch c 1 hcp hcg hCh hc zero_le_one N₀
    (fun n₀ m h1 h2 u hu E hE => by
      obtain ⟨D⟩ := hbox n₀ m h1 h2 u hu E hE
      exact blockRun_of_runOpsInputs hd D)

end AndersonAC.AgentS78
