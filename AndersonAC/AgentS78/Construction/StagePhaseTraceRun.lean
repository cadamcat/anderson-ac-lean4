import AndersonAC.AgentS78.Construction.StagePhaseSnap
import AndersonAC.AgentS78.Construction.StagePhaseOp

/-!
# The Lemma 7.2 trace across the stage transitions. `TraceInv Ctr n₀ u j x`: a trace `T` of successful clearing groups of index
`≤ j` whose edits are the terminal set of `x` and whose hop structure holds for `x.endpoint.M` on
the active set (the `trace` clause of `ClearRec`, without the stage-`j` freshness). It is kept by
the transitions between clearing phases:

* `traceInv_lift`: a stage-`j` trace is a stage-`j'` trace for `j ≤ j'` (indices `≤ j < j'`, so
  the freshness clause of stage `j'` is vacuous: `traceInv_fresh_start`);
* `traceInv_stageMapA`: the stage operation keeps `M`, the active set and the terminal set;
* `traceInv_sweepEnd`: the sweep end adds a diagonal to `M` (hops are off-diagonal) and, under
  the tile phase, keeps the active set (`sweepEndActive x ⊆ x.endpoint.active` suffices);
* `traceInv_snapshot`: the snapshot changes only the components.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf)

variable {d m : ℕ}

/-- A trace of stage `j` read at a later stage `j'`. -/
def clearingGeometryLift {n₀ j l : ℕ} {u C : ℝ} (T : ClearingGeometry d m n₀ j l u C) {j' : ℕ}
    (h : j ≤ j') : ClearingGeometry d m n₀ j' l u C where
  index := T.index
  core := T.core
  edits := T.edits
  anchor := T.anchor
  stages a := ⟨(T.stages a).1, (T.stages a).2.trans h⟩
  anchorMem := T.anchorMem
  eligible := T.eligible
  coreRadius := T.coreRadius
  separated := T.separated
  groupSize := T.groupSize
  locations := T.locations

/-- **The trace clause of the run** (all groups of index `≤ j`). -/
def TraceInv (Ctr : ℝ) (n₀ : ℕ) (u : ℝ) (j : ℕ) (x : RunRecord d m) : Prop :=
  ∃ l, ∃ T : ClearingGeometry d m n₀ j l u Ctr,
    (∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
      (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
      ∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active, x.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
        terminalDistance (nnGraph d m) (geometryTerminals T) a b = 0) ∧
    geometryTerminals T = x.terminal ∧ ∀ a, T.index a ≤ j

theorem traceInv_lift {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j j' : ℕ} {x : RunRecord d m}
    (h : TraceInv Ctr n₀ u j x) (hj : j ≤ j') : TraceInv Ctr n₀ u j' x := by
  obtain ⟨l, T, hops, hterm, hidx⟩ := h
  exact ⟨l, clearingGeometryLift T hj, hops, hterm, fun a => (hidx a).trans hj⟩

/-- At the start of stage `j + 1` the trace of stage `j` has no group of index `j + 1`, as
`clearRecPos_snapshot` needs. -/
theorem traceInv_fresh_start {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} {x : RunRecord d m}
    (h : TraceInv Ctr n₀ u j x) :
    ∃ l, ∃ T : ClearingGeometry d m n₀ (j + 1) l u Ctr,
      (∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
        (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
        ∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active, x.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
          terminalDistance (nnGraph d m) (geometryTerminals T) a b = 0) ∧
      geometryTerminals T = x.terminal ∧ ∀ a, T.index a ≠ j + 1 := by
  obtain ⟨l, T, hops, hterm, hidx⟩ := h
  exact ⟨l, clearingGeometryLift T (Nat.le_succ j), hops, hterm, fun a => by
    have := hidx a; show T.index a ≠ j + 1; omega⟩

/-- A record map keeping the active set, the matrix off the diagonal and the terminal set keeps
the trace clause. -/
theorem traceInv_of_map {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} {x y : RunRecord d m}
    (h : TraceInv Ctr n₀ u j x) (hact : y.endpoint.active ⊆ x.endpoint.active)
    (hM : ∀ a b, a ≠ b → y.endpoint.M a b = x.endpoint.M a b) (hterm : y.terminal = x.terminal) :
    TraceInv Ctr n₀ u j y := by
  obtain ⟨l, T, ⟨J, hJs, hJ1, hJadj, hJh⟩, hT, hidx⟩ := h
  refine ⟨l, T, ⟨J, hJs, hJ1, hJadj, fun a ha b hb hab => ?_⟩, hT.trans hterm.symm, hidx⟩
  by_cases hab' : a = b
  · subst hab'; exact AndersonAC.AgentS78Geo.terminalDistance_self _ _ _
  · rw [hM a b hab'] at hab
    exact hJh a (hact ha) b (hact hb) hab

/-- **The stage operation keeps the trace clause.** -/
theorem traceInv_stageMapA {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} (P : TilePlan d m) (j' : ℕ)
    {x : RunRecord d m} (h : TraceInv Ctr n₀ u j x) : TraceInv Ctr n₀ u j (stageMapA P j' x) := by
  have he := (stageMapA_endpoint_r P j' x).1
  have ht : (stageMapA P j' x).terminal = x.terminal := by
    unfold stageMapA; split_ifs <;> rfl
  refine traceInv_of_map h ?_ (fun a b _ => ?_) ht
  · rw [he]; exact le_of_eq rfl
  · rw [he]; rfl

/-- **The sweep end keeps the trace clause** when it does not enlarge the active set. -/
theorem traceInv_sweepEnd {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} (θ : ℝ) {x : RunRecord d m}
    (h : TraceInv Ctr n₀ u j x) (hact : sweepEndActive x ⊆ x.endpoint.active) :
    TraceInv Ctr n₀ u j (sweepEndMapTheta θ x) := by
  refine traceInv_of_map h hact (fun a b hab => ?_) rfl
  show sweepEndMTheta θ x a b = x.endpoint.M a b
  unfold sweepEndMTheta
  rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hab, add_zero]

/-- **The snapshot keeps the trace clause.** -/
theorem traceInv_snapshot {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} (j' : ℕ) {x : RunRecord d m}
    (h : TraceInv Ctr n₀ u j x) : TraceInv Ctr n₀ u j (snapshotMap j' x) := h

/-- The trace clause of `ClearRecPos` gives `TraceInv` (for the stage operation at the end of
the clearing phase). -/
theorem ClearRec.traceInv {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} {x : RunRecord d m} {k : ℕ}
    {anchor : Fin k → Torus d m} (h : ClearRec Ctr n₀ u j x anchor) : TraceInv Ctr n₀ u j x := by
  obtain ⟨l, T, hTr, hT, -⟩ := h.trace
  exact ⟨l, T, hTr.hops, hT, fun a => (T.stages a).2⟩

end AndersonAC.AgentS78
