import AndersonAC.AgentS78.Construction.RunAssembly

/-!
# Per-box inputs for a uniform certificate

`RunOpsData d m n₀ u E Cr cp cg Ch c` collects the hypotheses of `blockRun_of_runOps`
for one box: tile and clearing disciplines, halting, the run invariant and first-trial
bounds, the snapshot dichotomy, and the final record. `uniformCertificateInput_of_runOpsData`
assembles these data for all sufficiently large boxes with uniform constants.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources sourcesLaw querySigns)

/-- Inputs for one box in the finite-volume construction. -/
structure RunOpsData (d m n₀ : ℕ) (u E Cr cp cg Ch c : ℝ) where
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
  hfinite : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) (tileOrderSize P), blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω ≠ ⊤
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
  hdich : ∀ j x (ω : RandomSources (Torus d m) (tileOrderSize P)), P.n₀ < j → clearingScheduled j m → blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤ → x ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω).pending → ((blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω).latest x).scale = j ∨ ∃ S : Finset (Torus d m), x ∈ S ∧ stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, y ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω).pending) ∧ (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
  hfinal : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) → blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (m + 2)) ω ≠ ⊤ → (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (m + 2)) ω).aborted = false → ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ), IsDampedEndpoint s r (OAI.Anderson.scaleHeight m P.u) ∧ TrueSchurIdentity P.n₀ P.u E (trueConfig ω) s ∧ Fintype.card (Torus d m) ≤ 2 * s.active.card ∧ (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧ (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)
  hn₀ : P.n₀ = n₀
  hu' : P.u = u

attribute [instance] RunOpsData.mClSc

theorem blockRun_of_runOpsData {d m n₀ : ℕ} {u E Cr cp cg Ch c : ℝ}
    (D : RunOpsData d m n₀ u E Cr cp cg Ch c) :
    Nonempty (BlockRun d m n₀ u E Cr cp cg Ch c 1) := by
  have h := blockRun_of_runOps D.P E Cr cp cg Ch c D.hu D.ts₀ D.cl₀ D.clr D.clrPat D.rec₀ D.hpend₀ D.hrec₀ D.htmark D.htquery D.htpat D.htabort D.hdiam D.hcmeas D.hcorders D.hcaux D.hcpatm D.hclocal D.hcmark D.hcabort D.hcquery D.hcpat D.hfinite D.Inv D.hInv0 D.hInv D.hTV0 D.hTV D.hbound D.hdich D.hfinal
  rw [D.hn₀, D.hu'] at h
  exact h

/-- **UniformCertificateInput from the per-box inputs.** -/
theorem uniformCertificateInput_of_runOpsData
    (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (Cr cp cg Ch c : ℝ) (hcp : 0 < cp) (hcg : 0 < cg) (hCh : 1 ≤ Ch) (hc : 0 < c) (N₀ : ℕ)
    (hbox : ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      Nonempty (RunOpsData d m n₀ u E Cr cp cg Ch c)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_blockRuns' d hd e₂ Cr cp cg Ch c 1 hcp hcg hCh hc zero_le_one N₀
    (fun n₀ m h1 h2 u hu E hE => by
      obtain ⟨D⟩ := hbox n₀ m h1 h2 u hu E hE
      exact blockRun_of_runOpsData D)

end AndersonAC.AgentS78
