import AndersonAC.AgentS78.Construction.Record

/-!
# query-free blocks

A query-free block applies a measurable map to the committed record and halts at once:
empty (skipped) slots, the snapshot of the clearing graph, the end-of-sweep restriction to
the reserve ports, the diagonal reset (a measurable fixed point,
`measurable_contraction_reset`), and the cutoff check (abort if a site is pending). The
common internal state of all blocks is `RunRecord d m × Sc`, the second factor holding the
scratch data of the trial blocks.

Proved here: such blocks are measurable, issue no query (so they satisfy every order and
auxiliary discipline), never have a first-trial failure, and their failure event depends
on no coordinate.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ} {Sc : Type} [MeasurableSpace Sc]

/-- The query-free block applying `f` to the committed record. -/
def simpleBlock (sc₀ : Sc) (f : RunRecord d m → RunRecord d m) :
    Block (Torus d m) (RunRecord d m) (RunRecord d m × Sc) where
  enter x := (f x, sc₀)
  next _ := Query.decision
  update s _ := s
  halted _ := true
  exit s := s.1
  firstFail _ := false

theorem simpleBlock_measurable (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (hf : Measurable f) : (simpleBlock (d := d) (m := m) sc₀ f).IsMeasurable where
  enter := hf.prodMk measurable_const
  next := measurable_const
  update := measurable_fst
  halted := measurable_const
  exit := measurable_fst
  firstFail := measurable_const

theorem simpleBlock_localFirstFail (M : ℕ → ℕ) (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (x : RunRecord d m) : localFirstFail M (simpleBlock sc₀ f) x = ∅ := by
  ext ω
  simp [localFirstFail, simpleBlock]

theorem simpleBlock_dependsOnly (M : ℕ → ℕ) (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (π : FreshPattern (Torus d m)) (x : RunRecord d m) :
    DependsOnly (Torus d m) (M := M) π (localFirstFail M (simpleBlock sc₀ f) x) := by
  intro ω ω' _ _
  simp [simpleBlock_localFirstFail]

/-- A query-free block never issues an order query while running. -/
theorem simpleBlock_orders (M : ℕ → ℕ) (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (S : Set ℕ) : ∀ x k ω o,
    (simpleBlock sc₀ f).halted (localState M (simpleBlock sc₀ f) x k ω) = false →
    (simpleBlock sc₀ f).next (localState M (simpleBlock sc₀ f) x k ω) = Query.nextOrder o →
    o ∈ S ∧
    ((List.range k).filter fun k' =>
      (simpleBlock sc₀ f).halted (localState M (simpleBlock sc₀ f) x k' ω) = false ∧
      (simpleBlock sc₀ f).next (localState M (simpleBlock sc₀ f) x k' ω) =
        Query.nextOrder o).length < M o := by
  intro x k ω o h
  simp [simpleBlock] at h

/-- A query-free block never issues an auxiliary query while running. -/
theorem simpleBlock_aux (M : ℕ → ℕ) (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (S : Set ℕ) : ∀ x k ω a,
    (simpleBlock sc₀ f).halted (localState M (simpleBlock sc₀ f) x k ω) = false →
    (simpleBlock sc₀ f).next (localState M (simpleBlock sc₀ f) x k ω) = Query.auxiliary a →
    a ∈ S ∧ ∀ k' < k, (simpleBlock sc₀ f).halted (localState M (simpleBlock sc₀ f) x k' ω) =
      false → (simpleBlock sc₀ f).next (localState M (simpleBlock sc₀ f) x k' ω) ≠
        Query.auxiliary a := by
  intro x k ω a h
  simp [simpleBlock] at h

end AndersonAC.AgentS78
