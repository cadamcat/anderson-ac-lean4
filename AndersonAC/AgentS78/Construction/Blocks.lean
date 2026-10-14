import AndersonAC.AgentS78.Construction.MachineDef

/-!
# the run as a composition of blocks

Design. The run of one finite box is a list of *blocks*, one per
bookkeeping slot / schedule operation (tile trial with its retries, clearing attempt,
snapshot, reset, cutoff, final-sweep tile; 02-state.tex:349–362, 07-assembly.tex:18–34,
08-history.tex:52–63). A block is a measurable sub-machine on a common internal state type
`St`, entered from the committed record `Rec` and leaving a committed record. A halted
block hands over to the next one through one information-free `decision` operation.

`firstFail` is the latched flag "the first trial of this block has failed" (a birth at a
tile/clearing slot, a late failure after the cutoff).

The block-local run (`localState`) is the same sub-machine run on its own; it reads true
and auxiliary signs exactly as the global run does, and orders with fresh counts.
`BlockCompositionStatement` (contract) says that, when blocks use pairwise
disjoint order indices and never reuse an auxiliary sign or exhaust an order, the global
run is an admissible strategy, block starts are retained stopping times, the entering
records are measurable at those times, the global first-trial failure of block `n` is the
block-local failure from the entering record, and it is known at the next block start.
These are exactly the skeleton fields of `QueryRun` (QueryRun.lean).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2

/-- A block of the run on the common internal state type `St`. -/
structure Block (ι : Type) [Fintype ι] [DecidableEq ι] (Rec St : Type) where
  enter : Rec → St
  next : St → Query ι
  update : St → Answer ι → St
  halted : St → Bool
  exit : St → Rec
  firstFail : St → Bool

/-- Measurability of a block. -/
structure Block.IsMeasurable {ι : Type} [Fintype ι] [DecidableEq ι] {Rec St : Type}
    [MeasurableSpace Rec] [MeasurableSpace St] (B : Block ι Rec St) : Prop where
  enter : Measurable B.enter
  next : Measurable B.next
  update : Measurable (fun p : St × Answer ι => B.update p.1 p.2)
  halted : Measurable B.halted
  exit : Measurable B.exit
  firstFail : Measurable B.firstFail

section Composition
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Rec St : Type}

/-- Global state: block index, record at block entry, block state. -/
abbrev GState (Rec St : Type) := ℕ × Rec × St

def gnext (blocks : ℕ → Block ι Rec St) (g : GState Rec St) : Query ι :=
  if (blocks g.1).halted g.2.2 then Query.decision else (blocks g.1).next g.2.2

def gupdate (blocks : ℕ → Block ι Rec St) (g : GState Rec St) (a : Answer ι) : GState Rec St :=
  if (blocks g.1).halted g.2.2 then
    (g.1 + 1, (blocks g.1).exit g.2.2, (blocks (g.1 + 1)).enter ((blocks g.1).exit g.2.2))
  else (g.1, g.2.1, (blocks g.1).update g.2.2 a)

def gInit (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) : GState Rec St :=
  (0, rec₀, (blocks 0).enter rec₀)

variable (M : ℕ → ℕ)

/-- The global strategy of the run. -/
def runQ (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) : ℕ → RandomSources ι M → Query ι :=
  machineQ ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks)

/-- The global state after `q` operations. -/
def runState (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) :
    ℕ → RandomSources ι M → GState Rec St :=
  machineState ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks)

/-- The operation at which block `n` is entered (`⊤` if never). -/
def blockStart (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (n : ℕ)
    (ω : RandomSources ι M) : WithTop ℕ := by
  classical
  exact if h : ∃ q, (runState M blocks rec₀ q ω).1 = n then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

/-- The committed record with which block `n` is entered. -/
def blockPrestate (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (n : ℕ)
    (ω : RandomSources ι M) : Rec :=
  (runState M blocks rec₀ ((blockStart M blocks rec₀ n ω).untopD 0) ω).2.1

/-- The global first-trial failure of block `n`. -/
def globalFirstFail (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (n : ℕ) :
    Set (RandomSources ι M) :=
  {ω | ∃ q, (runState M blocks rec₀ q ω).1 = n ∧
    (blocks n).firstFail (runState M blocks rec₀ q ω).2.2 = true}

/-- The block-local run from a committed record. -/
def localState (B : Block ι Rec St) (x : Rec) (k : ℕ) (ω : RandomSources ι M) : St :=
  machineState ι M (B.enter x) B.next B.update k ω

/-- The block-local first-trial failure from a committed record. -/
def localFirstFail (B : Block ι Rec St) (x : Rec) : Set (RandomSources ι M) :=
  {ω | ∃ k, (∀ k' < k, B.halted (localState M B x k' ω) = false) ∧
    B.firstFail (localState M B x k ω) = true}

end Composition

/-- **block composition (contract).** Composition of blocks: skeleton of a `QueryRun`. -/
def BlockCompositionStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) (Rec St : Type)
    [MeasurableSpace Rec] [MeasurableSpace St]
    (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (_hmeas : ∀ n, (blocks n).IsMeasurable)
    (orderSet : ℕ → Set ℕ) (_hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (auxSet : ℕ → Set ℕ) (_hauxdisj : Pairwise fun n n' => Disjoint (auxSet n) (auxSet n'))
    -- local query discipline of each block, from every entering record
    (_horders : ∀ n x k ω o, (blocks n).halted (localState M (blocks n) x k ω) = false →
      (blocks n).next (localState M (blocks n) x k ω) = Query.nextOrder o →
      o ∈ orderSet n ∧
      ((List.range k).filter fun k' =>
        (blocks n).halted (localState M (blocks n) x k' ω) = false ∧
        (blocks n).next (localState M (blocks n) x k' ω) = Query.nextOrder o).length < M o)
    (_haux : ∀ n x k ω a, (blocks n).halted (localState M (blocks n) x k ω) = false →
      (blocks n).next (localState M (blocks n) x k ω) = Query.auxiliary a →
      a ∈ auxSet n ∧ ∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false →
        (blocks n).next (localState M (blocks n) x k' ω) ≠ Query.auxiliary a),
    ∃ hQ : ObeysQueryRules ι (runQ M blocks rec₀),
    ∃ hstart : ∀ n, IsStoppingTime (retainedFiltration ι hQ) (blockStart M blocks rec₀ n),
      (∀ n, blockStart M blocks rec₀ n ≤ blockStart M blocks rec₀ (n + 1)) ∧
      (∀ n, Measurable[(hstart n).measurableSpace] (blockPrestate M blocks rec₀ n)) ∧
      (∀ n, ∀ ω, blockStart M blocks rec₀ n ω ≠ ⊤ →
        (ω ∈ globalFirstFail M blocks rec₀ n ↔
          ω ∈ localFirstFail M (blocks n) (blockPrestate M blocks rec₀ n ω))) ∧
      (∀ n, MeasurableSet[(hstart (n + 1)).measurableSpace]
        (globalFirstFail M blocks rec₀ n ∩ {ω | blockStart M blocks rec₀ n ω ≠ ⊤}))

end AndersonAC.AgentS78
