import AndersonAC.AgentS78.Construction.StagePhasePkgBase
import AndersonAC.AgentS78.Construction.StagePhaseKind2
import AndersonAC.AgentS78.Construction.BoxPhasesSweepEnd
import AndersonAC.AgentS78Geo.PhysicalBridge

/-!
# Clearing-phase package: the sets and the per-operation facts.

* `TraceSet`, `RunG`, `gIdx`, `pkgXg` — the run-level part `Xg` of `ClearingBoxFacts`: every site
  is active or terminal, pending sites are active, and a Lemma 7.2 trace of index `≤ k` has the
  terminal set as its edits (`k = j − 1` during the tile phase of stage `j`, `k = j` from the sweep
  end on);
* `pkgXc` — the clearing-phase part `Xc j r := ClearPhaseR … j r` on clearing stages;
* `ClearingDonePhysHyp` — the physical identity after a DONE clearing. At singular
  real pivots this identity is used almost surely;
* `ClearingBoundR` — the clearing first-failure bound on `ClearPhaseR` records (`hB`, in the
  `ClearingBoxFacts.hbound` shape; statement replaces it);
* `clrOp_keeps` (`hClr`), `clrOp_bound` (`hbound`), `sweepEnd_clear` (`hXcE`).
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf physicalDistance_symm)
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-! ## Named hypotheses -/

/-- **The physical identity after a DONE clearing** (named hypothesis; see the module doc). -/
def ClearingDonePhysHyp (d : ℕ) : Prop :=
  ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (y : Torus d m) (x : RunRecord d m)
    (s : RunRecord d m × ClearScratch d m),
    BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s → x.aborted = false →
    clearingScheduled j m → s.2.core ≠ ∅ → s.2.failed = false → s.2.done = true →
    PhysicalIdentity E x → PhysicalIdentity E (clearingDoneExit x s.2)

/-- **The physical identity after a DONE clearing, off the exceptional set** (route R2,
replaces `ClearingDonePhysHyp`): along the answers of `ω ∉ exceptionalSet`, from a record with true
installed values whose inactive sites are terminal. -/
def ClearingDonePhysZ (d : ℕ) : Prop :=
  ∀ {m : ℕ} (n₀ j : ℕ) (u E : ℝ) (y : Torus d m) (M : ℕ → ℕ) (ω : RandomSources (Torus d m) M)
    (x : RunRecord d m) (k : ℕ), 0 < u →
    ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M → x ∈ TrueValues n₀ u ω →
    x.aborted = false → clearingScheduled j m →
    (∀ i, i ∈ x.endpoint.active ∨ i ∈ x.terminal) → PhysicalIdentity E x →
    (∀ k' < k, (clearingBlock (d := d) (m := m) n₀ j u y).halted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k' ω) = false) →
    (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω).2.core ≠ ∅ →
    (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω).2.failed = false →
    (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω).2.done = true →
    PhysicalIdentity E
      (clearingDoneExit x (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω).2)

/-- **The clearing first-failure bound on clearing-phase records** (`hB`). -/
def ClearingBoundR (d : ℕ) : Prop :=
  ∀ cB CB Ctr CA cA PA Cb : ℝ, 0 < cB → cB ≤ CB → 2 ≤ Ctr → 1 ≤ CA → 0 < cA → 0 ≤ PA →
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (M : ℕ → ℕ) (j : ℕ)
    (y : Torus d m) (x : RunRecord d m),
    N ≤ n₀ → 4 * n₀ ≤ m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m / 2 →
    ClearPhaseR cB CB Ctr n₀ u E ρ Cb CA cA PA j (siteRank d m y) x →
    (x.aborted = false → Disjoint x.endpoint.active x.terminal) →
    (x.aborted = false → theCore (d := d) (m := m) j u y x ⊆ x.endpoint.active) →
    sourcesLaw (Torus d m) M (localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u y) x) ≤
      ENNReal.ofReal (birthBound c j)

/-! ## The run-level set -/

/-- A Lemma 7.2 trace of index `≤ k` whose edits are the terminal set. -/
def TraceSet (Ctr : ℝ) (n₀ : ℕ) (u : ℝ) (k : ℕ) (x : RunRecord d m) : Prop :=
  ∃ l, ∃ T : ClearingGeometry d m n₀ k l u Ctr, geometryTerminals T = x.terminal ∧
    ∀ a, T.index a ≤ k

/-- **The run-level clauses** with trace index `k`. -/
def RunG (Ctr : ℝ) (n₀ : ℕ) (u : ℝ) (k : ℕ) (x : RunRecord d m) : Prop :=
  (∀ i, i ∈ x.endpoint.active ∨ i ∈ x.terminal) ∧ x.pending ⊆ x.endpoint.active ∧
    TraceSet Ctr n₀ u k x

/-- The trace index of block `n`. -/
def gIdx (P : TilePlan d m) (n : ℕ) : Option ℕ :=
  if decodeJ d m n ≤ P.n₀ then some P.n₀
  else if decodeJ d m n ≤ m then
    (if decodeK d m n = 0 ∨ (decodeK d m n = 1 ∧ n % siteCount d m = 0) then
      some (decodeJ d m n - 1) else some (decodeJ d m n))
  else none

/-- **`Xg` of the package.** -/
def pkgXg (Ctr : ℝ) (P : TilePlan d m) (n : ℕ) : Set (RunRecord d m) :=
  {x | x.aborted = false → ∀ k, gIdx P n = some k → RunG Ctr P.n₀ P.u k x}

/-- **`Xc` of the package.** -/
def pkgXc (cB CB Ctr : ℝ) (P : TilePlan d m) (E : ℝ) (ρ : ℂ) (Cb CA cA PA : ℝ) (j r : ℕ) :
    Set (RunRecord d m) :=
  {x | j ≤ m / 2 → ClearPhaseR cB CB Ctr P.n₀ P.u E ρ Cb CA cA PA j r x}

theorem traceSet_lift {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {k k' : ℕ} {x : RunRecord d m}
    (h : TraceSet Ctr n₀ u k x) (hk : k ≤ k') : TraceSet Ctr n₀ u k' x := by
  obtain ⟨l, T, h1, h2⟩ := h
  exact ⟨l, clearingGeometryLift T hk, h1, fun a => (h2 a).trans hk⟩

theorem runG_lift {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {k k' : ℕ} {x : RunRecord d m}
    (h : RunG Ctr n₀ u k x) (hk : k ≤ k') : RunG Ctr n₀ u k' x :=
  ⟨h.1, h.2.1, traceSet_lift h.2.2 hk⟩

theorem runG_of_fields {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {k : ℕ} {x y : RunRecord d m}
    (h : RunG Ctr n₀ u k x) (ha : y.endpoint.active = x.endpoint.active)
    (ht : y.terminal = x.terminal) (hp : y.pending ⊆ x.pending ∪ x.endpoint.active) :
    RunG Ctr n₀ u k y := by
  obtain ⟨h1, h2, l, T, h3, h4⟩ := h
  refine ⟨fun i => by rw [ha, ht]; exact h1 i, ?_, l, T, h3.trans ht.symm, h4⟩
  rw [ha]
  exact hp.trans (Finset.union_subset h2 (Finset.Subset.refl _))

/-- The run-level clauses from the record clauses of the clearing phase. -/
theorem runG_of_clearRec {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} {x : RunRecord d m} {k : ℕ}
    {anchor : Fin k → Torus d m} (h : ClearRec Ctr n₀ u j x anchor) : RunG Ctr n₀ u j x := by
  refine ⟨fun i => ?_, h.pendingActive, ?_⟩
  · by_cases hi : i ∈ x.terminal
    · exact Or.inr hi
    · left; rw [h.activeCompl]; simpa using hi
  · obtain ⟨l, T, -, hT, -⟩ := h.trace
    exact ⟨l, T, hT, fun a => (T.stages a).2⟩

/-- The empty trace. -/
def emptyGeometry (n₀ k : ℕ) (u Ctr : ℝ) : ClearingGeometry d m n₀ k 0 u Ctr where
  index := Fin.elim0
  core := Fin.elim0
  edits := Fin.elim0
  anchor := Fin.elim0
  stages a := a.elim0
  anchorMem a := a.elim0
  eligible a := a.elim0
  coreRadius a := a.elim0
  separated a := a.elim0
  groupSize a := a.elim0
  locations a := a.elim0

theorem geometryTerminals_empty (n₀ k : ℕ) (u Ctr : ℝ) :
    geometryTerminals (emptyGeometry (d := d) (m := m) n₀ k u Ctr) = ∅ := by
  unfold geometryTerminals
  simp

/-- The trace index across one block: unchanged except at the sweep end and after stage `m`. -/
theorem gIdx_succ (P : TilePlan d m) (n k' : ℕ) (h : gIdx P (n + 1) = some k') :
    gIdx P n = some k' ∨
      (decodeK d m n = 1 ∧ n % siteCount d m = 0 ∧ P.n₀ < decodeJ d m n ∧
        decodeJ d m n ≤ m ∧ k' = decodeJ d m n ∧ gIdx P n = some (decodeJ d m n - 1)) := by
  have hN := siteCount_pos d m
  unfold gIdx at h ⊢
  rcases decode_succ (d := d) (m := m) n with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3, h4, h5⟩
  · rw [h2, h3, h4] at h
    generalize decodeJ d m n = J at *
    generalize decodeK d m n = K at *
    generalize n % siteCount d m = R at *
    split_ifs at h ⊢ <;> simp_all <;> omega
  · rw [h3, h4, h5] at h
    generalize decodeJ d m n = J at *
    generalize decodeK d m n = K at *
    generalize n % siteCount d m = R at *
    split_ifs at h ⊢ <;> simp_all <;> omega
  · rw [h3, h4, h5] at h
    generalize decodeJ d m n = J at *
    generalize decodeK d m n = K at *
    generalize n % siteCount d m = R at *
    split_ifs at h ⊢ <;> simp_all <;> omega

end AndersonAC.AgentS78
