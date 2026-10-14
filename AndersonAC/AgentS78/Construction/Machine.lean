import AndersonAC.AgentS78.Construction.Freezing

/-!
# Query strategies from measurable machines

The machine statement formalizes the query measurability condition in
02-state.tex:136–160: "Before a query, its
type and source index are chosen measurably from the current history … numerical updates,
choices, and failure decisions must be measurable from the information recorded by that
time". The whole run is a machine: a state (control position, committed and provisional
numerical records, partition, marks, labels, retained answers needed later), a measurable
choice of the next query, and a measurable update by the answer. `MachineStrategyStatement`
says that every such machine defines an S2 query strategy whose states are measurable for
the retained σ-fields.

The run machine supplies
`ObeysQueryRules` (first clause from this contract; the auxiliary-freshness and order-count
clauses are run invariants) and the `prestate_measurable` field of `QueryRun`.
Route: define the states with the list of earlier queries carried along, so that the answer
at step `q` (`S2.answer`, which reads `Q j` only for `j ≤ q` through `orderCount`) is
computed without circularity; prove `answer ι Q q ω` agrees; measurability by induction,
using that `retained ι Q (q+1)` contains the comap of `(Q q, answer ι Q q)`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2

/-- **machine run (contract).** Measurable machines define admissible query strategies. -/
def MachineStrategyStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) (St : Type) [MeasurableSpace St]
    (init : St) (next : St → Query ι) (_hnext : Measurable next)
    (update : St → Answer ι → St)
    (_hupdate : Measurable (fun p : St × Answer ι => update p.1 p.2)),
    ∃ (Q : ℕ → RandomSources ι M → Query ι) (state : ℕ → RandomSources ι M → St),
      (∀ ω, state 0 ω = init) ∧ (∀ q ω, Q q ω = next (state q ω)) ∧
      (∀ q ω, state (q + 1) ω = update (state q ω) (answer ι Q q ω)) ∧
      (∀ q, Measurable[retained ι Q q] (state q))

end AndersonAC.AgentS78
