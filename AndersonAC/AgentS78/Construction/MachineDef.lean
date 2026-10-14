import AndersonAC.AgentS78.Construction.Machine

/-!
# the explicit machine run

sub-contract, the definitional form of machine run used by the
run machine and by the trial events of `QueryRun` (which need joint measurability in
the starting state). `machineRun` carries the list of earlier queries, so the answer at
step `q` (`localAnswer`, the same formula as `S2.answer` with `orderCount` replaced by the
count in that list) is defined without circularity.

`MachineRunStatement`: the explicit run satisfies the `S2.answer` recursion for its own
strategy `machineQ`, its states are measurable for the retained σ-fields, and the run is
jointly measurable in a measurably parametrized initial state. It implies
`MachineStrategyStatement` (take `Q := machineQ`, `state := machineState`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2

section
variable (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ)

/-- The answer to query `c` after the earlier queries `L` (as `S2.answer`). -/
def localAnswer (L : List (Query ι)) (c : Query ι) (ω : RandomSources ι M) : Answer ι := by
  classical
  exact (fun x => if x ∈ querySigns ι c then some (ω.1 x) else none,
    match c with
    | .nextOrder o => if h : L.count (Query.nextOrder o) < M o then
        some ((ω.2 o ⟨L.count (Query.nextOrder o), h⟩).val) else none
    | _ => none)

/-- The explicit run of a machine: state and the list of queries issued so far. -/
def machineRun {St : Type} (init : St) (next : St → Query ι) (update : St → Answer ι → St) :
    ℕ → RandomSources ι M → St × List (Query ι)
  | 0, _ => (init, [])
  | q + 1, ω =>
    ((update (machineRun init next update q ω).1
        (localAnswer ι M (machineRun init next update q ω).2
          (next (machineRun init next update q ω).1) ω)),
      (machineRun init next update q ω).2 ++ [next (machineRun init next update q ω).1])

/-- The machine state after `q` operations. -/
def machineState {St : Type} (init : St) (next : St → Query ι) (update : St → Answer ι → St)
    (q : ℕ) (ω : RandomSources ι M) : St := (machineRun ι M init next update q ω).1

/-- The machine's query strategy. -/
def machineQ {St : Type} (init : St) (next : St → Query ι) (update : St → Answer ι → St)
    (q : ℕ) (ω : RandomSources ι M) : Query ι := next (machineState ι M init next update q ω)

end

/-- **machine run (contract).** The explicit run is the S2 run of its strategy, is
retained-measurable, and is jointly measurable in a parametrized initial state. -/
def MachineRunStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) (St : Type) [MeasurableSpace St]
    (next : St → Query ι) (_hnext : Measurable next)
    (update : St → Answer ι → St)
    (_hupdate : Measurable (fun p : St × Answer ι => update p.1 p.2)),
    (∀ (init : St) (q : ℕ) (ω : RandomSources ι M),
      machineState ι M init next update (q + 1) ω =
        update (machineState ι M init next update q ω)
          (answer ι (machineQ ι M init next update) q ω)) ∧
    (∀ (init : St) (q : ℕ),
      Measurable[retained ι (machineQ ι M init next update) q]
        (machineState ι M init next update q)) ∧
    (∀ (P : Type) [MeasurableSpace P] (init : P → St), Measurable init → ∀ q : ℕ,
      Measurable (fun p : P × RandomSources ι M => machineState ι M (init p.1) next update q p.2))

end AndersonAC.AgentS78
