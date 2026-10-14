import AndersonAC.AgentS78.Construction.Record
import AndersonAC.AgentS78.Construction.Schedule
import AndersonAC.AgentS78.Construction.Freezing
import AndersonAC.AgentS78.Construction.TrueSpace
import AndersonAC.AgentS78.Construction.ClearingTrial
import AndersonAC.S6.Definitions
import AndersonAC.S6.RidgeSelection
import AndersonAC.AgentS6.LeverageFacts
import AndersonAC.S2.Binary

/-!
# WP10 random construction, C3b-clear: the clearing-attempt block

The clearing attempt of one snapshot component (`AgentS78.clearingBlock`),
for the schedule slot `opIndex d m j 2 x` (`Schedule.lean`: kind 2 is
`BirthType.clearing`, `slotIndex_eq_opIndex`).

Paper: `07-assembly.tex:18-34` (schedule: after the ordinary sweep into
stage `j ≤ ⌊m/2⌋`, freeze the snapshot graph of pending active sites at
radius `R_j = 4^{8j}`; in anchor order attempt each component `B` with
`|B| ≤ t_j^{-ν}` once; on DONE reveal the still-unknown core values, apply
the deterministic core completion and commit core + heat pivots as
terminal; on FAIL restore the prestate, retain all answers, and mark the
core plus every inspected exterior site pending). The heat trial itself is
the §6 stopped trial: `chooseRidge`, maximal `trialWeights` with the fixed
site order as tie-break (`S6.leastMaximizer`), `heat_update` with the
pivot's whole true residual from a `trueSuffix` query at height
`prefixLength`, stop at the S6 budgets / `heatLimit` / `projectionReady`
(`06-clearing.tex:757-857`; `S6.Definitions.StoppedTrial`).

Design decisions and their TeX sources:
- Eligibility (`theCore`): `x` is the least site (anchor for the fixed
  total order `siteRank`, `Schedule.lean`) of a component
  `B ∈ record.components` with `(B.card : ℝ) ≤ t_j^{-ν}`
  (`07-assembly.tex:18-34`; `S78.eligibleCore`). If `x` anchors no
  eligible component, or the record is aborted, or `j` is not a clearing
  stage, the block is empty (halts at once, no queries, no failure),
  like `SimpleBlocks.simpleBlock`.
- Guard (`guardHolds`; 07-assembly pivot paragraph and
  `S78.clearing_locality`): a candidate pivot that is not a coupled
  active site, or lies farther than `inspectionRadius j / 2` from `B`,
  FAILs the block without being queried (the pivot is still marked).
  On good prestates this never triggers (`S78.clearing_locality`), and
  it makes the read pattern exactly the coupled active sites.
- Coupled active sites (`coupledActive = endpoint.active \ pending`)
  keep untouched true suffixes from `prefixLength` (07-assembly: the
  ordinary-sweep invariant; `02-state.tex:96-113`). The pattern
  (`clearingPattern`) is those sites at those heights, with no `aux`
  and no orders, so `orderSet = auxSet = ∅`.
- Heat dynamics mirror `S6.StoppedTrial` field by field
  (`running_budgets`, `finite_stop`, `running_cap`, `pivot_max`,
  `pivot_tie`, `heat`, `ridge_rule`, `done_iff`, `fail_reason`).
- DONE (`07-assembly.tex:18-34`): the still-unknown suffixes on `B` are
  queried and eliminated by the same Schur step (sequential form of the
  deterministic core completion, Lemma 6.1; closed form
  `S6.completedInverse`), and core + heat pivots become committed
  terminals.
- FAIL: the record is restored, `B` and all inspected exterior sites
  (including the first breaking pivot) are marked pending with label
  `⟨j, .clearing, x⟩`, and the block-level `firstFail` latches.
- The bridge to §6 (`clearingBlock_bridge`): for a fixed good record,
  the block-local first failure is `{q.outcome = .fail}` for the S6
  `StoppedTrial` of the frozen data on `(RandomSources, sourcesLaw)`
  with `F0 = ⊥`, so C4b is `S6.preparation_of_small_component` there.
  The probability bound itself is not proved here.
-/

open MeasureTheory
open scoped NNReal

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw SignIndex)
open Classical

/-! ## Scratch state and eligibility -/

/-- Scratch state of a clearing attempt at `(j, x)`.
`core` is the eligible component (or `∅` for an empty block);
`active`/`Mnum`/`hatG` are the provisional heat-trial data
(`S6.TrialState` in full-matrix form, avoiding dependent subtypes);
`g0` is the frozen initial inverse for the S6 budgets;
`resids` records revealed residuals; `inspected` the exterior sites
queried so far (pending-marked on FAIL); `corePhase`/`coreLeft` run the
DONE-phase core-suffix queries; `failed`/`done` latch the outcome. -/
structure ClearScratch (d m : ℕ) where
  core : Finset (Torus d m)
  step : ℕ
  active : Finset (Torus d m)
  inspected : Finset (Torus d m)
  ridge : ℝ
  Mnum : Matrix (Torus d m) (Torus d m) ℝ
  hatG : Matrix (Torus d m) (Torus d m) ℂ
  g0 : Matrix (Torus d m) (Torus d m) ℂ
  resids : Torus d m → ℝ
  failed : Bool
  done : Bool
  corePhase : Bool
  coreLeft : Finset (Torus d m)

/-- Coordinate encoding of the scratch state, mirroring
`RunRecord.code` (`Record.lean`): finite sets as indicators, so the
comap σ-algebra has the expected measurable projections. -/
def ClearScratch.code {d m : ℕ} (sc : ClearScratch d m) :=
  (finsetCode sc.core, finsetCode sc.active, finsetCode sc.inspected,
    finsetCode sc.coreLeft,
    (sc.step, sc.ridge, sc.Mnum, sc.hatG, sc.g0, sc.resids,
      sc.failed, sc.done, sc.corePhase))

instance (d m : ℕ) : MeasurableSpace (ClearScratch d m) :=
  MeasurableSpace.comap ClearScratch.code inferInstance

theorem ClearScratch.measurable_code (d m : ℕ) :
    Measurable (ClearScratch.code (d := d) (m := m)) :=
  comap_measurable _

/-- Coupled active sites of a record: active but not pending.
07-assembly: these keep untouched true suffixes. -/
def coupledActive {d m : ℕ} (rec : RunRecord d m) : Finset (Torus d m) :=
  rec.endpoint.active \ rec.pending

theorem coupledActive_subset_active {d m : ℕ} (rec : RunRecord d m) :
    coupledActive rec ⊆ rec.endpoint.active :=
  Finset.sdiff_subset

theorem coupledActive_not_pending {d m : ℕ} (rec : RunRecord d m)
    {p : Torus d m} (h : p ∈ coupledActive rec) : p ∉ rec.pending := by
  simp only [coupledActive, Finset.mem_sdiff] at h
  exact h.2

/-- Anchor of a component for the fixed total order `siteRank`
(`Schedule.lean`): `x` is the least site of `B`. -/
def isAnchor {d m : ℕ} (B : Finset (Torus d m)) (x : Torus d m) : Prop :=
  x ∈ B ∧ ∀ y ∈ B, (siteRank d m x).val ≤ (siteRank d m y).val

/-- Radius of an eligible component around its anchor (correction (6)(b), agent-s78con3):
`t_j^{-ν} R_j`, which every snapshot component with at most `t_j^{-ν}` sites satisfies
(`Dichotomy.component_radius`). -/
def clearRadius (d m j : ℕ) (u : ℝ) : ℝ := stageScale u j m ^ (-nu d) * separationRadius j

/-- Eligibility candidate predicate for one set (`07-assembly.tex:18-34`), with the radius
clause of correction (6)(b). -/
def eligibleCand {d m : ℕ} (j : ℕ) (u : ℝ) (x : Torus d m)
    (B : Finset (Torus d m)) : Prop :=
  x ∈ B ∧ isAnchor (d := d) (m := m) B x ∧
    eligibleCore d B (stageScale u j m) ∧
    ∀ v ∈ B, physicalDistance d m v x ≤ clearRadius d m j u

/-- The eligible snapshot component anchored at `x`
(`07-assembly.tex:18-34`): the unique `B ∈ rec.components` with
`eligibleCand j u x B`, or `∅` if there is not exactly one.
`∅` also covers the aborted / unscheduled cases via the callers;
an eligible component is always nonempty (`x ∈ B`). -/
def theCore {d m : ℕ} (j : ℕ) (u : ℝ) (x : Torus d m)
    (rec : RunRecord d m) : Finset (Torus d m) :=
  let S := rec.components.filter (fun B => eligibleCand (d := d) (m := m) j u x B);
  if S.card = 1 then S.biUnion id else ∅

/-- Eligibility as a proposition (spec for `theCore`). -/
def clearingEligible {d m : ℕ} (j : ℕ) (u : ℝ) (x : Torus d m)
    (rec : RunRecord d m) : Prop :=
  rec.aborted = false ∧ clearingScheduled j m ∧ ∃ B ∈ rec.components,
    x ∈ B ∧ isAnchor (d := d) (m := m) B x ∧
      eligibleCore d B (stageScale u j m)

/-- The λ coupling of the installed potential (`PhysicalIdentity.lean`,
`OAI.Anderson.scaleCoupling`; lead correction (2)). -/
def clearingLam (n₀ : ℕ) (u : ℝ) : ℝ :=
  OAI.Anderson.scaleCoupling n₀ u

/-- Read pattern of the clearing block: the coupled active sites at
their prefix heights, no auxiliary signs, no orders
(`02-state.tex:96-113`, `Freezing.lean`; lead correction (3): empty when
the record is aborted or when no eligible core exists, and terminal
sites excluded so the pattern ⊆ `declaredFresh`). -/
def clearingPattern {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m)
    (rec : RunRecord d m) : FreshPattern (Torus d m) where
  sites := if rec.aborted then ∅
    else if clearingScheduled j m then
      if theCore (d := d) (m := m) j u x rec = ∅ then ∅
      else coupledActive rec \ rec.terminal
    else ∅
  height := rec.prefixLength
  aux := ∅
  orders := ∅

/-! ## S6 trial data attached to the scratch state -/

/-! ## Inlined §6 trial data (explicit sets/matrices, no proofs) -/

/-- Inlined S6 cross block: mirrors S6.trialCross exactly
(06-clearing.tex), but takes the active set, hopping matrix, damping
and core as explicit values. No TrialState, no symmetry proofs
(those enter only at the §6 bridge, from the good invariant). -/
def xCross {d m : ℕ} (t : ℝ) (r : Torus d m → ℂ)
    (A : Finset (Torus d m))
    (Msub : Matrix {i // i ∈ A} {i // i ∈ A} ℝ)
    (B : Finset (Torus d m)) : Matrix (Torus d m) {b // b ∈ B} ℂ :=
  fun i b => if hi : i ∈ A then
    if i ∈ B then 0 else
      if hb : b.val ∈ A then
        AndersonAC.S6.scatteringOfDamping t
          (AndersonAC.S6.imagDamping (fun i : {i // i ∈ A} => r i.val))
          (AndersonAC.S6.activeInverse Msub t (fun i : {i // i ∈ A} => r i.val))
          ⟨i, hi⟩ ⟨b.val, hb⟩
      else 0
    else 0

/-- Inlined S6 trial weights (mirrors S6.trialWeights). -/
def xWeights {d m : ℕ} (t : ℝ) (r : Torus d m → ℂ)
    (A : Finset (Torus d m))
    (Msub : Matrix {i // i ∈ A} {i // i ∈ A} ℝ)
    (B : Finset (Torus d m)) (τ : ℝ) : Torus d m → ℝ :=
  AndersonAC.S6.leverage (xCross t r A Msub B) τ

/-- Inlined S6 projection-readiness (mirrors S6.projectionReady). -/
def xReady {d m : ℕ} (t : ℝ) (r : Torus d m → ℂ)
    (A : Finset (Torus d m))
    (Msub : Matrix {i // i ∈ A} {i // i ∈ A} ℝ)
    (B : Finset (Torus d m)) : Prop :=
  ∀ i, AndersonAC.S6.projectionWeight (xCross t r A Msub B) i ≤
    2 * AndersonAC.S6.leverageScale t

/-- Restriction helper: full hopping matrix to a fixed active set. -/
def restrictM {d m : ℕ} (A : Finset (Torus d m))
    (Mnum : Matrix (Torus d m) (Torus d m) ℝ) :
    Matrix {i // i ∈ A} {i // i ∈ A} ℝ :=
  Mnum.submatrix (fun i : {i // i ∈ A} => Subtype.val i)
    (fun i : {i // i ∈ A} => Subtype.val i)

/-- S6 trial weights of the scratch state at ridge `τ` (total). -/
def scratchWeights {d m : ℕ} (t : ℝ) (r : Torus d m → ℂ)
    (sc : ClearScratch d m) (τ : ℝ) : Torus d m → ℝ :=
  xWeights t r sc.active (restrictM sc.active sc.Mnum) sc.core τ

/-- Candidate heat pivot: maximal `trialWeights` with the fixed site
order as tie-break (`S6.leastMaximizer`, `06-clearing.tex:684`;
total version). -/
def candPivot {d m : ℕ} (r : Torus d m → ℂ)
    (sc : ClearScratch d m) (t τ : ℝ) : Option (Torus d m) :=
  AndersonAC.S6.leastMaximizer (siteRank d m) (scratchWeights t r sc τ)

/-- Pivot guard (07-assembly, pivot paragraph; `S78.clearing_locality`):
the pivot must be a coupled active site outside `terminal` within
`inspectionRadius j / 2` of `B`. Never violated on good prestates
(where `active ∩ terminal = ∅`); the terminal clause makes heat
queries lie exactly in `clearingPattern` (so `fail_local` holds for
every record). -/
def guardHolds {d m : ℕ} (j : ℕ) (B : Finset (Torus d m))
    (coupled terminal : Finset (Torus d m)) (p : Torus d m) : Prop :=
  p ∈ coupled ∧ p ∉ terminal ∧
    ∃ y ∈ B, physicalDistance d m p y ≤ inspectionRadius j / 2

/-- Residual recorded from a `trueSuffix` answer: the binary suffix of
the revealed digits (`S2.answer` reveals exactly the queried signs),
with coupling λ (lead correction (2)). `binarySuffix lam h a` reads `a (h + k)`, so the digit
function is indexed by the absolute digit position (lead correction (9), agent-s78runinv). -/
def residOfAnswer {d m : ℕ} (lam : ℝ) (y : Torus d m) (h : ℕ)
    (ans : Answer (Torus d m)) : ℝ :=
  AndersonAC.S2.binarySuffix lam h
    (fun k => (ans.1 (Sum.inl (y, k))).getD false)

/-- Full-matrix Schur update at `x` with shift `ξ`: the sequential form
of `S6.HeatTransition` (heats) and Lemma 6.1 (core completion).
Entries at the removed row/column are junk (zeroed/diagonal);
`x` leaves `active`. Total (division by zero gives junk, never used on
good prestates by standing invertibility, 07-assembly). -/
def schurStepM {d m : ℕ} (Mnum : Matrix (Torus d m) (Torus d m) ℝ)
    (x : Torus d m) (ξ : ℝ) : Matrix (Torus d m) (Torus d m) ℝ :=
  fun i j => if i = x ∨ j = x then (if i = j then 1 else 0)
    else Mnum i j - Mnum i x * Mnum x j / (Mnum x x + ξ)

/-- One elimination step on the scratch data: Schur-update `Mnum`,
refresh `hatG` from the successor active inverse on surviving pairs
(`S6.HeatTransition` hatG clause, sequential Lemma 6.1 form), drop `x`
from `active`. Total and proof-free. -/
def elimStep {d m : ℕ} (t : ℝ) (r : Torus d m → ℂ)
    (sc : ClearScratch d m) (x : Torus d m) (ξ : ℝ) :
    Matrix (Torus d m) (Torus d m) ℝ ×
      Matrix (Torus d m) (Torus d m) ℂ :=
  let Mfull := schurStepM sc.Mnum x ξ
  let act' := sc.active.erase x
  let Msub' := restrictM act' Mfull
  let hatG' : Matrix (Torus d m) (Torus d m) ℂ := fun i j =>
    if h : i ∈ act' ∧ j ∈ act' then
      AndersonAC.S6.activeInverse Msub' t
        (fun i : {i // i ∈ act'} => r i.val) ⟨i, h.1⟩ ⟨j, h.2⟩
    else sc.hatG i j
  (Mfull, hatG')

/-- A failure candidate is marked only if it passes the pivot guard (correction (6)(a),
agent-s78con3; 07-assembly.tex:31–33 marks inspected exterior sites, which are guarded). -/
def guardedCand {d m : ℕ} (j : ℕ) (rec : RunRecord d m) (sc : ClearScratch d m)
    (o : Option (Torus d m)) : Option (Torus d m) :=
  o.bind fun p => if guardHolds (d := d) (m := m) j sc.core (coupledActive rec) rec.terminal p
    then some p else none

/-! ## Block dynamics -/

/-- Clearing action at the current scratch state. `fail p` latches
failure (marking `p` if given); `coreReady` ends the heats and starts
the core-suffix phase; `heat p` queries the heat pivot, carrying the
provisioning, exteriority and guard evidence its successors need;
`coreQuery y` queries a core suffix, carrying the provisioning
evidence; `finish` ends the block successfully. -/
inductive ClearingAction (d m j : ℕ) (rc : RunRecord d m) (sc : ClearScratch d m) where
  | fail : Option (Torus d m) → ClearingAction d m j rc sc
  | coreReady : ClearingAction d m j rc sc
  | heat : (p : Torus d m) →
      guardHolds (d := d) (m := m) j sc.core (coupledActive rc) rc.terminal p →
      ClearingAction d m j rc sc
  | coreQuery : (y : Torus d m) → sc.corePhase = true → ClearingAction d m j rc sc
  | finish : ClearingAction d m j rc sc

/-- Action computed from the S6 stop data (`S6.StoppedTrial` fields
`running_budgets`, `finite_stop`, `running_cap`, `done_iff`,
`fail_reason`): FAIL if the core is not provisioned, the budgets break,
the heat limit is reached, or the cap breaks (the candidate is kept for
marking); READY if budgets hold and the projection is ready; otherwise
HEAT at the guarded candidate pivot (heat pivots in the core are
rejected defensively). In the core phase, query the least remaining
core site by site rank, else finish. -/
def actionOf {d m : ℕ} (j : ℕ) (u : ℝ) (rec : RunRecord d m)
    (sc : ClearScratch d m) : ClearingAction d m j rec sc :=
  if sc.failed then .fail none
  else if sc.done then .finish
  else if sc.core = ∅ then .finish
  else if hc : sc.corePhase then
    match (sc.coreLeft.toList.mergeSort
        (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? with
    | some y => .coreQuery y hc
    | none => .finish
  else
    let t := stageScale u j m
    let l := AndersonAC.S6.leverageScale t
    if sc.core ⊆ sc.active then
      if AndersonAC.S6.BudgetsHold t sc.g0 sc.hatG then
        if sc.step < AndersonAC.S6.heatLimit t then
          let w := scratchWeights t rec.r sc sc.ridge
          if AndersonAC.S6.maxWeight w ≤ 4 * l then
            if xReady t rec.r sc.active (restrictM sc.active sc.Mnum) sc.core then
              .coreReady
            else match candPivot rec.r sc t sc.ridge with
              | some p =>
                if hg : guardHolds (d := d) (m := m) j sc.core
                    (coupledActive rec) rec.terminal p then
                  if p ∈ sc.core then .fail (some p) else .heat p hg
                else .fail none
              | none => .coreReady
          else .fail (guardedCand j rec sc (candPivot rec.r sc t sc.ridge))
        else .fail none
      else .fail (guardedCand j rec sc (candPivot rec.r sc t sc.ridge))
    else .fail none

/-- Initial scratch from the entering record: the eligible component
(or `∅`, ending the block at once), the committed active set and
endpoint data, the S6 start ridge
(`S6.StoppedTrial.start_ridge`: `chooseRidge` at `l_*^{-2}`).
Empty (halts at once) when the record is aborted, `j` is not a
clearing stage, or no eligible core exists (`07-assembly.tex:18-34`;
like `SimpleBlocks.simpleBlock`). -/
def clearInitScratch {d m : ℕ} (j : ℕ) (u : ℝ) (x : Torus d m)
    (rec : RunRecord d m) : ClearScratch d m :=
  let core := theCore (d := d) (m := m) j u x rec
  let act := rec.endpoint.active
  let Mnum : Matrix (Torus d m) (Torus d m) ℝ := fun i j => (rec.endpoint.M i j).re
  let empty := decide (core = ∅) || rec.aborted || !decide (clearingScheduled j m)
  let sc0 : ClearScratch d m :=
    { core := core, step := 0, active := act, inspected := ∅,
      ridge := 0, Mnum := Mnum, hatG := rec.endpoint.g, g0 := rec.endpoint.g,
      resids := fun _ => 0, failed := false, done := empty,
      corePhase := false, coreLeft := core }
  let t := stageScale u j m
  let l := AndersonAC.S6.leverageScale t
  let ridge0 : ℝ := AndersonAC.S6.chooseRidge
    (xCross t rec.r act (restrictM act Mnum) core)
    l (l ^ (-2 : ℤ))
  { sc0 with ridge := ridge0 }

/-! ## The block -/

/-- `next`: HEAT queries are `trueSuffix` at the record's prefix
height (coupled sites, lead correction (2)); CORE queries are
`trueSuffix y 0` (full true value, lead correction (4):
`07-assembly.tex:26-27, 246-252`; pending core sites may carry aux
digits so the suffix from `prefixLength` is not exact); anything else
is the information-free `decision`. In particular no order and no
auxiliary query is ever issued. -/
def clearingNext {d m : ℕ} (n₀ j : ℕ) (u : ℝ)
    (s : RunRecord d m × ClearScratch d m) : Query (Torus d m) :=
  match actionOf (d := d) (m := m) j u s.1 s.2 with
  | .fail _ => .decision
  | .coreReady => .decision
  | .heat p _ => .trueSuffix p (s.1.prefixLength p)
  | .coreQuery y _ => .trueSuffix y 0
  | .finish => .decision

/-- `update`: latch FAIL (marking the breaking pivot), start the core
phase, advance heats with the revealed residual, or advance core
elimination. Halted states are fixed. The committed record is never
modified mid-block (restore/commit happen in `exit`).
Heat residuals use coupling λ from `prefixLength` (lead correction (2));
core residuals use the full true value minus installed
(lead correction (4)). -/
def clearingUpdate {d m : ℕ} (n₀ j : ℕ) (u : ℝ)
    (s : RunRecord d m × ClearScratch d m)
    (ans : Answer (Torus d m)) : RunRecord d m × ClearScratch d m :=
  let rc := s.1
  let sc := s.2
  let lam := clearingLam n₀ u
  if sc.failed ∨ sc.done then s
  else match actionOf (d := d) (m := m) j u rc sc with
  | .fail po =>
    let insp := po.elim sc.inspected (fun p => insert p sc.inspected)
    (rc, { sc with failed := true, inspected := insp })
  | .coreReady => (rc, { sc with corePhase := true })
  | .heat p _ =>
    let ξ := residOfAnswer (d := d) (m := m) lam p (rc.prefixLength p) ans
    let t := stageScale u j m
    let l := AndersonAC.S6.leverageScale t
    let (Mfull, hatG') :=
      elimStep (d := d) (m := m) t rc.r sc p ξ
    let sc1raw : ClearScratch d m := { sc with Mnum := Mfull, hatG := hatG', active := sc.active.erase p, resids := Function.update sc.resids p ξ, inspected := insert p sc.inspected, step := sc.step + 1 }
    let ridge1 : ℝ := AndersonAC.S6.chooseRidge
      (xCross t rc.r sc1raw.active (restrictM sc1raw.active sc1raw.Mnum) sc1raw.core)
      l sc.ridge
    let sc1 : ClearScratch d m := { sc1raw with ridge := ridge1 }
    if ¬ AndersonAC.S6.BudgetsHold t sc.g0 sc1.hatG then
      (rc, { sc1 with failed := true })
    else if sc1.step ≥ AndersonAC.S6.heatLimit t then
      (rc, { sc1 with failed := true })
    else
      let w := scratchWeights (d := d) (m := m) t rc.r sc1 sc1.ridge
      if 4 * l < AndersonAC.S6.maxWeight w then
        (rc, { sc1 with failed := true })
      else if xReady t rc.r sc1.active (restrictM sc1.active sc1.Mnum) sc1.core then
        (rc, { sc1 with corePhase := true })
      else (rc, sc1)
  | .coreQuery y _ =>
    let full := residOfAnswer (d := d) (m := m) lam y 0 ans
    let ξ := full - rc.installed y
    let t := stageScale u j m
    let (Mfull, hatG') :=
      elimStep (d := d) (m := m) t rc.r sc y ξ
    let left' := sc.coreLeft.erase y
    (rc, { sc with Mnum := Mfull, hatG := hatG', active := sc.active.erase y, resids := Function.update sc.resids y ξ, coreLeft := left', done := decide (left' = ∅) })
  | .finish => (rc, { sc with done := true })

/-- Halted iff the outcome latched. -/
def clearingHalted {d m : ℕ} (s : RunRecord d m × ClearScratch d m) : Bool :=
  s.2.failed || s.2.done

/-- FAIL exit (`07-assembly.tex:18-34`): restore the record, mark `B`
and all inspected exterior sites pending with `⟨j, .clearing, x⟩`. -/
def clearingFailExit {d m : ℕ} (j : ℕ) (x : Torus d m)
    (rec : RunRecord d m) (sc : ClearScratch d m) : RunRecord d m :=
  { rec with
    pending := rec.pending ∪ sc.core ∪ sc.inspected,
    latest := fun y =>
      if y ∈ sc.core ∪ sc.inspected then ⟨j, .clearing, x⟩
      else rec.latest y }

/-- DONE exit: commit core + heat pivots as terminal with revealed
values; the provisional survivor data become the endpoint.
Lead correction (5) (`02-state.tex:109-110`, `07-assembly.tex:26-31`):
cleared sites leave the pending class; `components` is kept (later
attempts of the stage read the snapshot). With correction (4),
`installed + resids = λ·V` on core ∪ pivots. -/
def clearingDoneExit {d m : ℕ}
    (rec : RunRecord d m) (sc : ClearScratch d m) : RunRecord d m :=
  { rec with
    endpoint := { rec.endpoint with
      active := sc.active \ sc.core,
      M := sc.Mnum.map Complex.ofReal,
      -- correction (8) (agent-s78phase): zero off the committed active set
      g := fun i k => if i ∈ sc.active \ sc.core ∧ k ∈ sc.active \ sc.core then sc.hatG i k
        else 0 },
    terminal := rec.terminal ∪ sc.core ∪ sc.inspected,
    pending := rec.pending \ (sc.core ∪ sc.inspected),
    installed := fun y =>
      if y ∈ sc.core ∪ sc.inspected then rec.installed y + sc.resids y
      else rec.installed y }

/-- `exit`: empty blocks (aborted, unscheduled, or no core) and running
states restore the record. -/
def clearingExit {d m : ℕ} (j : ℕ) (x : Torus d m)
    (s : RunRecord d m × ClearScratch d m) : RunRecord d m :=
  if s.1.aborted then s.1
  else if !decide (clearingScheduled j m) then s.1
  else if s.2.core = ∅ then s.1
  else if s.2.failed then clearingFailExit (d := d) (m := m) j x s.1 s.2
  else if s.2.done then clearingDoneExit s.1 s.2
  else s.1

/-- `firstFail`: latched block-level failure. -/
def clearingFirstFail {d m : ℕ} (s : RunRecord d m × ClearScratch d m) : Bool :=
  s.2.failed

/-- The clearing-attempt block for slot `opIndex d m j 2 x`
(`07-assembly.tex:18-34`). `n₀` is the initial stage (coupling
`λ = scaleCoupling n₀ u`, lead correction (2)). -/
def clearingBlock {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Block (Torus d m) (RunRecord d m)
      (RunRecord d m × ClearScratch d m) where
  enter rec := (rec, clearInitScratch (d := d) (m := m) j u x rec)
  next := clearingNext (d := d) (m := m) n₀ j u
  update := clearingUpdate (d := d) (m := m) n₀ j u
  halted := clearingHalted
  exit := clearingExit (d := d) (m := m) j x
  firstFail := clearingFirstFail

/-- Block projections unfold to the underlying definitions. -/
theorem clearingBlock_halted_eq {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    (clearingBlock (d := d) (m := m) n₀ j u x).halted = clearingHalted := rfl

theorem clearingBlock_firstFail_eq {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    (clearingBlock (d := d) (m := m) n₀ j u x).firstFail = clearingFirstFail := rfl

theorem clearingBlock_next_eq {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    (clearingBlock (d := d) (m := m) n₀ j u x).next =
      clearingNext (d := d) (m := m) n₀ j u := rfl

theorem clearingBlock_enter_eq {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    (clearingBlock (d := d) (m := m) n₀ j u x).enter =
      fun rec => (rec, clearInitScratch (d := d) (m := m) j u x rec) := rfl

/-! ## BlockRun disciplines: no order or auxiliary queries -/

theorem clearing_next_ne_order {d m : ℕ} (n₀ j : ℕ) (u : ℝ)
    (s : RunRecord d m × ClearScratch d m) (o : ℕ) :
    clearingNext (d := d) (m := m) n₀ j u s ≠ Query.nextOrder o := by
  intro hcon
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po => simp [clearingNext, hact] at hcon
  | coreReady => simp [clearingNext, hact] at hcon
  | heat p _ => simp [clearingNext, hact] at hcon
  | coreQuery y _ => simp [clearingNext, hact] at hcon
  | finish => simp [clearingNext, hact] at hcon

theorem clearing_next_ne_aux {d m : ℕ} (n₀ j : ℕ) (u : ℝ)
    (s : RunRecord d m × ClearScratch d m) (a : ℕ) :
    clearingNext (d := d) (m := m) n₀ j u s ≠ Query.auxiliary a := by
  intro hcon
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po => simp [clearingNext, hact] at hcon
  | coreReady => simp [clearingNext, hact] at hcon
  | heat p _ => simp [clearingNext, hact] at hcon
  | coreQuery y _ => simp [clearingNext, hact] at hcon
  | finish => simp [clearingNext, hact] at hcon

/-- Clearing queries are never `trueDigit` (only suffixes/decision). -/
theorem clearing_next_ne_digit {d m : ℕ} (n₀ j : ℕ) (u : ℝ)
    (s : RunRecord d m × ClearScratch d m) (i : Torus d m) (k : ℕ) :
    clearingNext (d := d) (m := m) n₀ j u s ≠ Query.trueDigit i k := by
  intro hcon
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po => simp [clearingNext, hact] at hcon
  | coreReady => simp [clearingNext, hact] at hcon
  | heat p _ => simp [clearingNext, hact] at hcon
  | coreQuery y _ => simp [clearingNext, hact] at hcon
  | finish => simp [clearingNext, hact] at hcon

/-- The clearing block never issues an order query (hence satisfies
every `BlockRun` order discipline, in particular the vacuous one for
`orderSet = ∅`). -/
theorem clearingBlock_orders {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m)
    (M : ℕ → ℕ) (S : Set ℕ) : ∀ r k ω o,
    (clearingBlock (d := d) (m := m) n₀ j u x).halted
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) = false →
    (clearingBlock (d := d) (m := m) n₀ j u x).next
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) =
        Query.nextOrder o →
    o ∈ S ∧
    ((List.range k).filter fun k' =>
      (clearingBlock (d := d) (m := m) n₀ j u x).halted
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) = false ∧
      (clearingBlock (d := d) (m := m) n₀ j u x).next
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) =
        Query.nextOrder o).length < M o := by
  intro r k ω o _ hq
  exact absurd hq (clearing_next_ne_order n₀ j u _ o)

/-- The clearing block never issues an auxiliary query (hence satisfies
every `BlockRun` aux discipline, in particular the vacuous one for
`auxSet = ∅`). -/
theorem clearingBlock_aux {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m)
    (M : ℕ → ℕ) (S : Set ℕ) : ∀ r k ω a,
    (clearingBlock (d := d) (m := m) n₀ j u x).halted
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) = false →
    (clearingBlock (d := d) (m := m) n₀ j u x).next
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) =
        Query.auxiliary a →
    a ∈ S ∧ ∀ k' < k,
      (clearingBlock (d := d) (m := m) n₀ j u x).halted
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) =
        false →
      (clearingBlock (d := d) (m := m) n₀ j u x).next
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) ≠
        Query.auxiliary a := by
  intro r k ω a _ hq
  exact absurd hq (clearing_next_ne_aux n₀ j u _ a)

/-! ## Measurability toolkit: coordinates, fibers, S6 functions -/

section MeasCoords
variable {d m : ℕ}

/-- Scratch `failed` flag is a measurable projection (chain checked by `rfl`). -/
theorem meas_failed : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.failed) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.failed)
      = (fun p => p.2.2.2.2.2.2.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch `done` flag. -/
theorem meas_done : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.done) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.done)
      = (fun p => p.2.2.2.2.2.2.2.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch `corePhase` flag. -/
theorem meas_corePhase : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.corePhase) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.corePhase)
      = (fun p => p.2.2.2.2.2.2.2.2.2.2.2.2) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch step counter. -/
theorem meas_step : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.step) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.step)
      = (fun p => p.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch ridge. -/
theorem meas_ridge : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.ridge) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.ridge)
      = (fun p => p.2.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch real matrix. -/
theorem meas_Mnum : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.Mnum) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.Mnum)
      = (fun p => p.2.2.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch inverse. -/
theorem meas_hatG : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.hatG) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.hatG)
      = (fun p => p.2.2.2.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch frozen inverse. -/
theorem meas_g0 : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.g0) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.g0)
      = (fun p => p.2.2.2.2.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch residuals. -/
theorem meas_resids : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.resids) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.2.resids)
      = (fun p => p.2.2.2.2.2.2.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch core indicator (joint in the site). -/
theorem meas_core_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.core) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.core)
      = (fun p => p.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch active indicator. -/
theorem meas_active_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.active) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.active)
      = (fun p => p.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch inspected indicator. -/
theorem meas_inspected_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.inspected) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.inspected)
      = (fun p => p.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Scratch remaining-core indicator. -/
theorem meas_coreLeft_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.coreLeft) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.coreLeft)
      = (fun p => p.2.2.2.1) ∘ (fun s => ClearScratch.code s.2) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (ClearScratch.measurable_code _ _) measurable_snd)

/-- Record `aborted` flag. -/
theorem meas_aborted : Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.aborted) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.1.aborted)
      = (fun p => p.2.2.2.2.2.2) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record stage. -/
theorem meas_stage : Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.stage) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.1.stage)
      = (fun p => p.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record endpoint-active indicator. -/
theorem meas_rec_active_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.endpoint.active) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.endpoint.active)
      = (fun p => p.2.1.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record pending indicator. -/
theorem meas_rec_pending_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.pending) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.pending)
      = (fun p => p.2.2.2.2.1.2.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record terminal indicator. -/
theorem meas_rec_terminal_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.terminal) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.terminal)
      = (fun p => p.2.2.2.2.1.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record components indicator (joint in the candidate set). -/
theorem meas_rec_components_ind :
    Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (fun B : Finset (Torus d m) => decide (B ∈ s.1.components))) := by
  have h : (fun s : RunRecord d m × ClearScratch d m =>
        (fun B : Finset (Torus d m) => decide (B ∈ s.1.components)))
      = (fun p => p.2.2.2.2.2.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record prefix lengths. -/
theorem meas_rec_prefix :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.prefixLength) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.1.prefixLength)
      = (fun p => p.2.2.2.1.2) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record installed values. -/
theorem meas_rec_installed :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.installed) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.1.installed)
      = (fun p => p.2.2.2.1.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record endpoint matrix. -/
theorem meas_rec_M :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.endpoint.M) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.1.endpoint.M)
      = (fun p => p.2.1.2.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record endpoint inverse. -/
theorem meas_rec_g :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.endpoint.g) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.1.endpoint.g)
      = (fun p => p.2.1.2.2.1) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record damping. -/
theorem meas_rec_r :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.r) := by
  have h : (fun s : RunRecord d m × ClearScratch d m => s.1.r)
      = (fun p => p.2.1.2.2.2) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

/-- Record latest-label codes (joint in the site). -/
theorem meas_rec_latest :
    Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (fun y => labelCode (s.1.latest y))) := by
  have h : (fun s : RunRecord d m × ClearScratch d m =>
        (fun y => labelCode (s.1.latest y)))
      = (fun p => p.2.2.2.2.1.2.2) ∘ (fun s => RunRecord.code s.1) := rfl
  rw [h]
  exact Measurable.comp (by fun_prop)
    (Measurable.comp (RunRecord.measurable_code _ _) measurable_fst)

end MeasCoords

section MeasFibers
variable {d m : ℕ}

/-- Functions into a countable space are measurable from singleton fibers. -/
theorem measurable_of_singleton_fibers {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] {f : α → β}
    (h : ∀ b, MeasurableSet (f ⁻¹' {b})) : Measurable f := by
  intro t ht
  have hunion : f ⁻¹' t = ⋃ b ∈ t, f ⁻¹' {b} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro ha; exact ⟨f a, ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact hb
  rw [hunion]
  exact MeasurableSet.biUnion (Set.to_countable t) fun b _ => h b

/-- Per-site scratch-core membership is measurable. -/
theorem measSet_core_mem (y : Torus d m) :
    MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} := by
  have hmeas : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode s.2.core y) :=
    (measurable_pi_apply y).comp meas_core_ind
  have : {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core}
      = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.core y) ⁻¹' {true} := by
    ext s
    simp [finsetCode]
  rw [this]
  exact hmeas (measurableSet_singleton true)

/-- Per-site scratch-active membership. -/
theorem measSet_active_mem (y : Torus d m) :
    MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.2.active} := by
  have hmeas : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode s.2.active y) :=
    (measurable_pi_apply y).comp meas_active_ind
  have : {s : RunRecord d m × ClearScratch d m | y ∈ s.2.active}
      = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.active y) ⁻¹' {true} := by
    ext s
    simp [finsetCode]
  rw [this]
  exact hmeas (measurableSet_singleton true)

/-- Per-site remaining-core membership. -/
theorem measSet_coreLeft_mem (y : Torus d m) :
    MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.2.coreLeft} := by
  have hmeas : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode s.2.coreLeft y) :=
    (measurable_pi_apply y).comp meas_coreLeft_ind
  have : {s : RunRecord d m × ClearScratch d m | y ∈ s.2.coreLeft}
      = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.coreLeft y) ⁻¹' {true} := by
    ext s
    simp [finsetCode]
  rw [this]
  exact hmeas (measurableSet_singleton true)

/-- Per-site scratch-inspected membership. -/
theorem measSet_inspected_mem (y : Torus d m) :
    MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected} := by
  have hmeas : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode s.2.inspected y) :=
    (measurable_pi_apply y).comp meas_inspected_ind
  have : {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected}
      = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.inspected y) ⁻¹' {true} := by
    ext s
    simp [finsetCode]
  rw [this]
  exact hmeas (measurableSet_singleton true)

/-- Record components indicator at record level (for `theCore`). -/
theorem meas_recC_components_ind :
    Measurable (fun rc : RunRecord d m =>
      (fun B : Finset (Torus d m) => decide (B ∈ rc.components))) := by
  have h : (fun rc : RunRecord d m =>
        (fun B : Finset (Torus d m) => decide (B ∈ rc.components)))
      = (fun p => p.2.2.2.2.2.1) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Per-set component membership of the record. -/
theorem measSet_comp_mem (B : Finset (Torus d m)) :
    MeasurableSet {s : RunRecord d m × ClearScratch d m | B ∈ s.1.components} := by
  have hmeas : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      decide (B ∈ s.1.components)) :=
    (measurable_pi_apply B).comp meas_rec_components_ind
  have : {s : RunRecord d m × ClearScratch d m | B ∈ s.1.components}
      = (fun s : RunRecord d m × ClearScratch d m => decide (B ∈ s.1.components)) ⁻¹' {true} := by
    ext s
    simp
  rw [this]
  exact hmeas (measurableSet_singleton true)

/-- The eligibility candidate set has measurable cardinality: per-site
membership in `theCore` is a finite Boolean combination of component
memberships (the anchor/card conditions are fixed). -/
theorem measSet_theCore_mem (j : ℕ) (u : ℝ) (x : Torus d m) (y : Torus d m) :
    MeasurableSet {rc : RunRecord d m | y ∈ theCore (d := d) (m := m) j u x rc} := by
  classical
  have hmemB : ∀ B : Finset (Torus d m),
      MeasurableSet {rc : RunRecord d m | B ∈ rc.components} := by
    intro B
    have heq : {rc : RunRecord d m | B ∈ rc.components}
        = (fun rc : RunRecord d m => decide (B ∈ rc.components)) ⁻¹' {true} := by
      ext rc
      simp
    rw [heq]
    have hmeas : Measurable (fun rc : RunRecord d m =>
        decide (B ∈ rc.components)) :=
      (measurable_pi_apply B).comp meas_recC_components_ind
    exact hmeas (measurableSet_singleton true)
  have hcard : Measurable (fun rc : RunRecord d m =>
      ((rc.components.filter
        (fun B => eligibleCand (d := d) (m := m) j u x B)).card : ℕ)) := by
    have hsum : (fun rc : RunRecord d m =>
          ((rc.components.filter
            (fun B => eligibleCand (d := d) (m := m) j u x B)).card : ℕ))
        = fun rc => ∑ B ∈ Finset.univ,
          (if B ∈ rc.components ∧ eligibleCand (d := d) (m := m) j u x B
            then 1 else 0) := by
      funext rc
      have heq : rc.components.filter
            (fun B => eligibleCand (d := d) (m := m) j u x B)
          = Finset.univ.filter
            (fun B => B ∈ rc.components ∧ eligibleCand (d := d) (m := m) j u x B) := by
        ext B
        simp [Finset.mem_filter]
      rw [heq, Finset.card_filter]
    rw [hsum]
    refine Finset.measurable_sum Finset.univ fun B _ => ?_
    have hset : MeasurableSet {rc : RunRecord d m |
        B ∈ rc.components ∧ eligibleCand (d := d) (m := m) j u x B} := by
      by_cases hB : eligibleCand (d := d) (m := m) j u x B
      · have h1 : {rc : RunRecord d m |
            B ∈ rc.components ∧ eligibleCand (d := d) (m := m) j u x B}
            = {rc : RunRecord d m | B ∈ rc.components} := by
          ext rc
          simp [hB]
        rw [h1]
        exact hmemB B
      · have h1 : {rc : RunRecord d m |
            B ∈ rc.components ∧ eligibleCand (d := d) (m := m) j u x B} = ∅ := by
          ext rc
          simp [hB]
        rw [h1]
        exact MeasurableSet.empty
    exact Measurable.ite hset measurable_const measurable_const
  have hmem : {rc : RunRecord d m | y ∈ theCore (d := d) (m := m) j u x rc}
      = {rc | ((rc.components.filter
          (fun B => eligibleCand (d := d) (m := m) j u x B)).card = 1 ∧
        ∃ B ∈ rc.components.filter
          (fun B => eligibleCand (d := d) (m := m) j u x B), y ∈ B)} := by
    ext rc
    simp only [Set.mem_setOf_eq]
    unfold theCore
    by_cases h1 : (rc.components.filter
        (fun B => eligibleCand (d := d) (m := m) j u x B)).card = 1
    · simp [h1, Finset.mem_biUnion]
    · simp [h1]
  rw [hmem, Set.setOf_and]
  refine MeasurableSet.inter (hcard (measurableSet_singleton 1)) ?_
  have hunion : {rc : RunRecord d m |
        ∃ B ∈ rc.components.filter
          (fun B => eligibleCand (d := d) (m := m) j u x B), y ∈ B}
      = ⋃ B ∈ Finset.univ.filter (fun B => y ∈ B),
        {rc : RunRecord d m | B ∈ rc.components.filter
          (fun B => eligibleCand (d := d) (m := m) j u x B)} := by
    ext rc
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨B, hBmem, hyB⟩
      exact ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ B, hyB⟩, hBmem⟩
    · rintro ⟨B, hBF, hSB⟩
      exact ⟨B, hSB, (Finset.mem_filter.mp hBF).2⟩
  rw [hunion]
  refine Finset.measurableSet_biUnion _ fun B _ => ?_
  by_cases hB : eligibleCand (d := d) (m := m) j u x B
  · have h1 : {rc : RunRecord d m | B ∈ rc.components.filter
        (fun B => eligibleCand (d := d) (m := m) j u x B)}
        = {rc : RunRecord d m | B ∈ rc.components} := by
      ext rc
      simp [Finset.mem_filter, hB]
    rw [h1]
    exact hmemB B
  · have h1 : {rc : RunRecord d m | B ∈ rc.components.filter
        (fun B => eligibleCand (d := d) (m := m) j u x B)} = ∅ := by
      ext rc
      simp [Finset.mem_filter, hB]
    rw [h1]
    exact MeasurableSet.empty

/-- Scratch fiber over fixed core/active sets. -/
def scratchFiber (B₀ A₀ : Finset (Torus d m)) :
    Set (RunRecord d m × ClearScratch d m) :=
  {s | s.2.core = B₀ ∧ s.2.active = A₀}

/-- Fibers are measurable (finite Boolean combinations of memberships). -/
theorem measSet_scratchFiber (B₀ A₀ : Finset (Torus d m)) :
    MeasurableSet (scratchFiber (d := d) (m := m) B₀ A₀) := by
  have hcore : {s : RunRecord d m × ClearScratch d m | s.2.core = B₀}
      = ⋂ y ∈ Finset.univ, {s | (y ∈ s.2.core) = (y ∈ B₀)} := by
    ext s
    simp [Finset.ext_iff]
  have hact : {s : RunRecord d m × ClearScratch d m | s.2.active = A₀}
      = ⋂ y ∈ Finset.univ, {s | (y ∈ s.2.active) = (y ∈ A₀)} := by
    ext s
    simp [Finset.ext_iff]
  have hmem : ∀ y : Torus d m, ∀ C₀ : Finset (Torus d m),
      MeasurableSet {s : RunRecord d m × ClearScratch d m |
        (y ∈ s.2.core) = (y ∈ C₀)} := by
    intro y C₀
    by_cases hy : y ∈ C₀
    · simpa [hy] using measSet_core_mem y
    · have : {s : RunRecord d m × ClearScratch d m | (y ∈ s.2.core) = (y ∈ C₀)}
          = {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core}ᶜ := by
        ext s; simp [hy]
      rw [this]
      exact (measSet_core_mem y).compl
  have hmemA : ∀ y : Torus d m, ∀ C₀ : Finset (Torus d m),
      MeasurableSet {s : RunRecord d m × ClearScratch d m |
        (y ∈ s.2.active) = (y ∈ C₀)} := by
    intro y C₀
    by_cases hy : y ∈ C₀
    · simpa [hy] using measSet_active_mem y
    · have : {s : RunRecord d m × ClearScratch d m | (y ∈ s.2.active) = (y ∈ C₀)}
          = {s : RunRecord d m × ClearScratch d m | y ∈ s.2.active}ᶜ := by
        ext s; simp [hy]
      rw [this]
      exact (measSet_active_mem y).compl
  unfold scratchFiber
  rw [Set.setOf_and, hcore, hact]
  refine MeasurableSet.inter ?_ ?_
  · exact Finset.measurableSet_biInter _ fun y _ => hmem y B₀
  · exact Finset.measurableSet_biInter _ fun y _ => hmemA y A₀

/-- Measurability from a countable measurable cover (fiber glue). -/
theorem Measurable.of_finite_fiber {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {f : α → β} {ι : Type*} [Countable ι]
    {fib : ι → Set α} (hcover : ∀ a, ∃ i, a ∈ fib i)
    (hmeas : ∀ i, MeasurableSet (fib i))
    (h : ∀ i, Measurable (fun a : ↥(fib i) => f a)) : Measurable f := by
  intro t ht
  have hunion : f ⁻¹' t
      = ⋃ i ∈ Set.univ, Subtype.val '' ((fun a : ↥(fib i) => f a) ⁻¹' t) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro ha
      obtain ⟨i, hi⟩ := hcover a
      exact ⟨i, Set.mem_univ i, ⟨a, hi⟩, ha, rfl⟩
    · rintro ⟨i, -, a', ha, heq⟩
      rw [← heq]
      exact ha
  rw [hunion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun i _ => ?_
  exact (MeasurableEmbedding.subtype_coe (hmeas i)).measurableSet_image.mpr ((h i) ht)

end MeasFibers

/-! ## S6 per-fiber toolkit: pure facts -/

section S6Pure
variable {d m : ℕ}

/-- The torus is nonempty (for maxWeight attainment). -/
theorem torus_nonempty : Nonempty (Torus d m) := ⟨fun _ => 0⟩

/-- `maxWeight` is always nonnegative. -/
theorem maxWeight_nonneg {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    0 ≤ AndersonAC.S6.maxWeight w := by
  unfold AndersonAC.S6.maxWeight
  have h : (0 : ℝ≥0) ≤ Finset.univ.sup (fun i => Real.toNNReal (w i)) :=
    zero_le
  exact_mod_cast h

/-- Finite suprema of nonnegative measurable functions are measurable
(same induction as `AgentS6` uses for streams). -/
theorem measurable_finset_sup_nnreal {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] {f : ι → α → ℝ≥0}
    (hf : ∀ i, Measurable (f i)) (s : Finset ι) :
    Measurable (fun a => (s.sup fun i => f i a : ℝ≥0)) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sup_empty] using
      (measurable_const : Measurable (fun _ : α => (⊥ : ℝ≥0)))
  | @insert a t ha ih =>
    simp only [Finset.sup_insert]
    exact (hf a).sup ih

/-- `maxWeight` of a jointly measurable family is measurable. -/
theorem measurable_maxWeight_of {α : Type*} [MeasurableSpace α]
    {w : α → Torus d m → ℝ} (hw : ∀ i, Measurable (fun a => w a i)) :
    Measurable (fun a => AndersonAC.S6.maxWeight (w a)) := by
  unfold AndersonAC.S6.maxWeight
  exact NNReal.continuous_coe.measurable.comp
    (measurable_finset_sup_nnreal
      (fun i => continuous_real_toNNReal.measurable.comp (hw i)) _)

/-- Least-maximizer correctness (pure): `some p` iff `p` attains the
global maximum and is least among attainers (`06-clearing.tex:684`). -/
theorem leastMaximizer_eq_some {ι : Type*} [Fintype ι] [DecidableEq ι]
    (order : ι ≃ Fin (Fintype.card ι)) (w : ι → ℝ) (p : ι) :
    AndersonAC.S6.leastMaximizer order w = some p ↔
      (w p = AndersonAC.S6.maxWeight w ∧
        ∀ q, w q = AndersonAC.S6.maxWeight w → order p ≤ order q) := by
  unfold AndersonAC.S6.leastMaximizer
  set maxW := AndersonAC.S6.maxWeight w with hmaxW
  set J : Finset (Fin (Fintype.card ι)) :=
    Finset.univ.filter (fun j => w (order.symm j) = maxW) with hJ
  have hmemJ : ∀ j : Fin (Fintype.card ι),
      j ∈ J ↔ w (order.symm j) = maxW := by
    intro j
    simp [hJ, Finset.mem_filter]
  have hsort_mem : ∀ j : Fin (Fintype.card ι),
      j ∈ J.sort (· ≤ ·) ↔ j ∈ J := fun j => Finset.mem_sort (· ≤ ·)
  constructor
  · intro h
    generalize hg : J.sort (· ≤ ·) = l
    cases l with
    | nil =>
      rw [hg] at h
      simp at h
    | cons j₀ t =>
      rw [hg] at h
      have hhead : (j₀ :: t).head? = some j₀ := rfl
      simp only [hhead, Option.map_some] at h
      have hp : order.symm j₀ = p := Option.some_inj.mp h
      have hj₀J : j₀ ∈ J := by
        have hmem : j₀ ∈ J.sort (· ≤ ·) := by
          rw [hg]
          exact List.mem_cons.mpr (Or.inl rfl)
        exact (hsort_mem j₀).mp hmem
      have hmax : w p = maxW := by
        have hq := (hmemJ j₀).mp hj₀J
        rw [← hp]
        exact hq
      refine ⟨hmax, fun q hq => ?_⟩
      have hqJ : order q ∈ J := by
        have hqq : w (order.symm (order q)) = maxW := by
          simp [Equiv.symm_apply_apply, hq]
        exact (hmemJ _).mpr hqq
      have hqs : order q ∈ J.sort (· ≤ ·) := (hsort_mem _).mpr hqJ
      rw [hg] at hqs
      have hpw := Finset.pairwise_sort J (· ≤ ·)
      rw [hg] at hpw
      have hle : j₀ ≤ order q := by
        rcases List.mem_cons.mp hqs with rfl | hxt
        · exact le_refl _
        · exact (List.pairwise_cons.mp hpw).1 _ hxt
      have hpo : order p = j₀ := by
        rw [← hp, Equiv.apply_symm_apply]
      rw [hpo]
      exact hle
  · intro h
    obtain ⟨hmax, hleast⟩ := h
    have hpJ : order p ∈ J := by
      rw [hmemJ]
      simp [Equiv.symm_apply_apply, hmax]
    generalize hg : J.sort (· ≤ ·) = l
    cases l with
    | nil =>
      exfalso
      exfalso
      have : order p ∈ J.sort (· ≤ ·) := (hsort_mem _).mpr hpJ
      rw [hg] at this
      exact List.not_mem_nil this
    | cons j₀ t =>
      have hhead : (j₀ :: t).head? = some j₀ := rfl
      have hj₀J : j₀ ∈ J := by
        have hmem : j₀ ∈ J.sort (· ≤ ·) := by
          rw [hg]
          exact List.mem_cons.mpr (Or.inl rfl)
        exact (hsort_mem j₀).mp hmem
      have hq : w (order.symm j₀) = maxW := (hmemJ j₀).mp hj₀J
      have hle1 : order p ≤ j₀ := by
        have hle := hleast _ hq
        simpa [Equiv.apply_symm_apply] using hle
      have hpw := Finset.pairwise_sort J (· ≤ ·)
      rw [hg] at hpw
      have hpJ' : order p ∈ J.sort (· ≤ ·) := (hsort_mem _).mpr hpJ
      rw [hg] at hpJ'
      have hle2 : j₀ ≤ order p := by
        rcases List.mem_cons.mp hpJ' with hcon | hxt
        · exact le_of_eq hcon.symm
        · exact (List.pairwise_cons.mp hpw).1 _ hxt
      have heq : j₀ = order p := le_antisymm hle2 hle1
      have hps : order.symm j₀ = p := by
        rw [heq, Equiv.symm_apply_apply]
      simp only [hhead, Option.map_some, hps]

end S6Pure

/-! ## S6 measurable toolkit (fixed fiber types, general domain) -/

section S6Tool
variable {d m : ℕ} {α : Type*} [MeasurableSpace α]
variable {A₀ B₀ : Finset (Torus d m)} (hsub : B₀ ⊆ A₀)

/-- Restricted real matrix is jointly measurable. -/
theorem tool_subM {Mf : α → Matrix (Torus d m) (Torus d m) ℝ}
    (hM : Measurable Mf) :
    Measurable (fun a => (Mf a).submatrix
      (fun i : {i // i ∈ A₀} => Subtype.val i)
      (fun i : {i // i ∈ A₀} => Subtype.val i)) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.submatrix_apply]
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hM)

/-- Damped matrix entries are measurable. -/
theorem tool_damped_eval
    {Mf : α → Matrix {i // i ∈ A₀} {i // i ∈ A₀} ℝ}
    {rf : α → {i // i ∈ A₀} → ℂ} (t : ℝ)
    (hM : Measurable Mf) (hr : Measurable rf) (a b : {i // i ∈ A₀}) :
    Measurable (fun s : α =>
      AndersonAC.S6.dampedMatrix (Mf s) t (rf s) a b) := by
  unfold AndersonAC.S6.dampedMatrix
  simp only [Matrix.sub_apply]
  refine Measurable.sub ?_ ?_
  · simp only [Matrix.map_apply]
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hM)))
  · -- diagonal part
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
      exact measurable_const.mul ((measurable_pi_apply _).comp hr)
    · simp only [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab, smul_zero]
      exact measurable_const

/-- Damped matrix is jointly measurable. -/
theorem tool_damped {Mf : α → Matrix {i // i ∈ A₀} {i // i ∈ A₀} ℝ}
    {rf : α → {i // i ∈ A₀} → ℂ} (t : ℝ)
    (hM : Measurable Mf) (hr : Measurable rf) :
    Measurable (fun s : α => AndersonAC.S6.dampedMatrix (Mf s) t (rf s)) := by
  refine Measurable.of_eval_matrix _ fun a b => ?_
  exact tool_damped_eval t hM hr a b

/-- Trial inverse entries are measurable (via the imported inverse). -/
theorem tool_trialInverse_eval (t : ℝ)
    {Mf : α → Matrix {i // i ∈ A₀} {i // i ∈ A₀} ℝ}
    {rf : α → {i // i ∈ A₀} → ℂ}
    (hM : Measurable Mf) (hr : Measurable rf)
    (a b : {i // i ∈ A₀}) :
    Measurable (fun s : α =>
      AndersonAC.S6.activeInverse (Mf s) t (rf s) a b) := by
  have hinv : Measurable (fun s : α =>
      (AndersonAC.S6.dampedMatrix (Mf s) t (rf s))⁻¹) :=
    AndersonAC.AgentS6.measurable_matrix_inv.comp (tool_damped t hM hr)
  unfold AndersonAC.S6.activeInverse
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hinv)

end S6Tool


section FiberEval
variable {d m : ℕ} {α : Type*} [MeasurableSpace α]
variable {A₀ B₀ : Finset (Torus d m)} (hsub : B₀ ⊆ A₀)

/-- Scattering is jointly measurable from measurable damping/inverse. -/
theorem tool_scattering (t : ℝ)
    {pf : α → {i // i ∈ A₀} → ℝ} {gf : α → Matrix {i // i ∈ A₀} {i // i ∈ A₀} ℂ}
    (hp : Measurable pf) (hg : Measurable gf) :
    Measurable (fun s => AndersonAC.S6.scatteringOfDamping t (pf s) (gf s)) := by
  have hA : Measurable (fun s => AndersonAC.S6.sqrtDamping (pf s)) := by
    refine Measurable.of_eval_matrix _ fun a b => ?_
    unfold AndersonAC.S6.sqrtDamping
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.diagonal_apply_eq]
      exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable.comp
        ((measurable_pi_apply _).comp hp)
    · simp only [Matrix.diagonal_apply_ne _ hab]
      exact measurable_const
  have hprod : Measurable (fun s =>
      AndersonAC.S6.sqrtDamping (pf s) * gf s *
        AndersonAC.S6.sqrtDamping (pf s)) :=
    AndersonAC.AgentS6.measurable_matrix_mul
      (AndersonAC.AgentS6.measurable_matrix_mul hA hg) hA
  have hprod_eval : ∀ i j : {i // i ∈ A₀}, Measurable (fun s =>
      (AndersonAC.S6.sqrtDamping (pf s) * gf s *
        AndersonAC.S6.sqrtDamping (pf s)) i j) := fun i j =>
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hprod)
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have hsc : (fun s =>
      AndersonAC.S6.scatteringOfDamping t (pf s) (gf s) i j)
      = fun s => (1 : Matrix {i // i ∈ A₀} {i // i ∈ A₀} ℂ) i j +
        (2 * Complex.I * (t : ℂ)) *
          ((AndersonAC.S6.sqrtDamping (pf s) * gf s *
            AndersonAC.S6.sqrtDamping (pf s)) i j) := by
    funext s
    unfold AndersonAC.S6.scatteringOfDamping
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hsc]
  by_cases hab : i = j
  · subst hab
    simp only [Matrix.one_apply_eq]
    exact measurable_const.add (measurable_const.mul (hprod_eval _ _))
  · simp only [Matrix.one_apply_ne hab, zero_add]
    exact measurable_const.mul (hprod_eval _ _)

end FiberEval

section XCross
variable {d m : ℕ} {α : Type*} [MeasurableSpace α]
variable {A₀ B₀ : Finset (Torus d m)}

/-- Scattering entries directly from entry-measurable inputs. -/
theorem tool_scattering_eval_direct (t : ℝ)
    {pf : α → {i // i ∈ A₀} → ℝ} {gf : α → Matrix {i // i ∈ A₀} {i // i ∈ A₀} ℂ}
    (hpf : ∀ j, Measurable (fun s => pf s j))
    (hgf : ∀ a b, Measurable (fun s => gf s a b))
    (i j : {i // i ∈ A₀}) :
    Measurable (fun s =>
      AndersonAC.S6.scatteringOfDamping t (pf s) (gf s) i j) := by
  have hA : ∀ a b : {i // i ∈ A₀}, Measurable (fun s =>
      AndersonAC.S6.sqrtDamping (pf s) a b) := by
    intro a b
    unfold AndersonAC.S6.sqrtDamping
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.diagonal_apply_eq]
      exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable.comp
        (hpf _)
    · simp only [Matrix.diagonal_apply_ne _ hab]
      exact measurable_const
  have hAjoint : Measurable (fun s => AndersonAC.S6.sqrtDamping (pf s)) := by
    refine Measurable.of_eval_matrix _ fun a b => ?_
    exact hA a b
  have hgf_joint : Measurable gf := by
    refine Measurable.of_eval_matrix _ fun a b => ?_
    exact hgf a b
  have hprod_joint : Measurable (fun s =>
      AndersonAC.S6.sqrtDamping (pf s) * gf s *
        AndersonAC.S6.sqrtDamping (pf s)) :=
    AndersonAC.AgentS6.measurable_matrix_mul
      (AndersonAC.AgentS6.measurable_matrix_mul hAjoint hgf_joint) hAjoint
  have hprod : ∀ a b : {i // i ∈ A₀}, Measurable (fun s =>
      (AndersonAC.S6.sqrtDamping (pf s) * gf s *
        AndersonAC.S6.sqrtDamping (pf s)) a b) := fun a b =>
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hprod_joint)
  have hsc : (fun s =>
      AndersonAC.S6.scatteringOfDamping t (pf s) (gf s) i j)
      = fun s => (1 : Matrix {i // i ∈ A₀} {i // i ∈ A₀} ℂ) i j +
        (2 * Complex.I * (t : ℂ)) *
          ((AndersonAC.S6.sqrtDamping (pf s) * gf s *
            AndersonAC.S6.sqrtDamping (pf s)) i j) := by
    funext s
    unfold AndersonAC.S6.scatteringOfDamping
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hsc]
  by_cases hab : i = j
  · subst hab
    simp only [Matrix.one_apply_eq]
    exact Measurable.add (measurable_const : Measurable (fun _ : α => (1 : ℂ)))
      (Measurable.mul (measurable_const : Measurable (fun _ : α => (2 * Complex.I * (t : ℂ))))
        (hprod _ _))
  · simp only [Matrix.one_apply_ne hab, zero_add]
    exact Measurable.mul (measurable_const : Measurable (fun _ : α => (2 * Complex.I * (t : ℂ))))
      (hprod _ _)

/-- Inlined cross entries are measurable. -/
theorem tool_xcross_eval (t : ℝ)
    {rf : α → Torus d m → ℂ} {Mf : α → Matrix (Torus d m) (Torus d m) ℝ}
    (hr : Measurable rf) (hM : Measurable Mf)
    (i : Torus d m) (b : {b // b ∈ B₀}) :
    Measurable (fun s =>
      xCross t (rf s) A₀
        ((Mf s).submatrix
          (fun i : {i // i ∈ A₀} => Subtype.val i)
          (fun i : {i // i ∈ A₀} => Subtype.val i)) B₀ i b) := by
  unfold xCross
  by_cases hi : i ∈ A₀
  · simp [hi]
    by_cases hiB : i ∈ B₀
    · simp [hiB]
    · simp [hiB]
      by_cases hb : b.val ∈ A₀
      · simp [hb]
        -- scattering of explicit restricted data
        have hMsub : Measurable (fun s =>
            (Mf s).submatrix
              (fun i : {i // i ∈ A₀} => Subtype.val i)
              (fun i : {i // i ∈ A₀} => Subtype.val i)) := by
          refine Measurable.of_eval_matrix _ fun a c => ?_
          simp only [Matrix.submatrix_apply]
          exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hM)
        have hrsub : Measurable (fun s : α =>
            (fun i : {i // i ∈ A₀} => rf s i.val)) := by
          apply Measurable.of_eval
          intro k
          exact (measurable_pi_apply _).comp hr
        have hginv : ∀ a c : {i // i ∈ A₀}, Measurable (fun s =>
            AndersonAC.S6.activeInverse
              ((Mf s).submatrix
                (fun i : {i // i ∈ A₀} => Subtype.val i)
                (fun i : {i // i ∈ A₀} => Subtype.val i)) t
              (fun i : {i // i ∈ A₀} => rf s i.val) a c) := by
          intro a c
          exact tool_trialInverse_eval t hMsub hrsub a c
        have hpf : ∀ k : {i // i ∈ A₀}, Measurable (fun s =>
            (rf s k.val).im) := by
          intro k
          exact Complex.continuous_im.measurable.comp
            ((measurable_pi_apply _).comp hr)
        have hscat : ∀ x y : {i // i ∈ A₀}, Measurable (fun s =>
            AndersonAC.S6.scatteringOfDamping t
              (fun i : {i // i ∈ A₀} => (rf s i.val).im)
              (AndersonAC.S6.activeInverse
                ((Mf s).submatrix
                  (fun i : {i // i ∈ A₀} => Subtype.val i)
                  (fun i : {i // i ∈ A₀} => Subtype.val i)) t
                (fun i : {i // i ∈ A₀} => rf s i.val)) x y) :=
          tool_scattering_eval_direct t hpf (fun a c => hginv a c)
        exact hscat ⟨i, hi⟩ ⟨b.val, hb⟩
      · simp [hb]
  · simp [hi]

end XCross

section FiberWeights
variable {d m : ℕ}
variable {A₀ B₀ : Finset (Torus d m)}

/-- Weights-eval on a (core, active) fiber via the fixed pipeline
(unfold first to expose the sets, then rewrite them). -/
theorem fiber_weights_eval (t : ℝ) (i : Torus d m) :
    Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      scratchWeights t (a.val.1.r) a.val.2 (a.val.2.ridge) i) := by
  have hMf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      a.val.2.Mnum) :=
    meas_Mnum.comp measurable_subtype_coe
  have hrf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      (fun i : Torus d m => a.val.1.r i)) := by
    apply Measurable.of_eval
    intro y
    exact (measurable_pi_apply _).comp
      (meas_rec_r.comp measurable_subtype_coe)
  have hridge : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      a.val.2.ridge) :=
    meas_ridge.comp measurable_subtype_coe
  have hnorm : (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
        scratchWeights t (a.val.1.r) a.val.2 (a.val.2.ridge) i)
      = (fun a => AndersonAC.S6.leverage
          (xCross t (a.val.1.r) A₀
            (restrictM A₀ (a.val.2.Mnum)) B₀)
          (a.val.2.ridge) i) := by
    funext a
    simp only [scratchWeights, xWeights]
    rw [a.property.1, a.property.2]
  rw [hnorm]
  have hcross_joint : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) := by
    refine Measurable.of_eval_matrix _ fun xb yb => ?_
    exact tool_xcross_eval t hrf hMf xb yb
  have hpair := hcross_joint.prodMk hridge
  have hlev : Measurable (fun p : Matrix (Torus d m) {b // b ∈ B₀} ℂ × ℝ =>
      AndersonAC.S6.leverage p.1 p.2 i) :=
    AndersonAC.AgentS6.measurable_leverage i
  have hcomp : Measurable ((fun p : Matrix (Torus d m) {b // b ∈ B₀} ℂ × ℝ =>
      AndersonAC.S6.leverage p.1 p.2 i) ∘
    (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      ((xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀), a.val.2.ridge))) :=
    hlev.comp hpair
  exact hcomp

/-- Weights-eval on a fiber at a fixed ridge (for `chooseRidge`'s
`maxWeight` test; same pipeline with constant `τ`). -/
theorem fiber_weights_fixed (t τ : ℝ) (i : Torus d m) :
    Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      AndersonAC.S6.leverage
        (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) τ i) := by
  have hMf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      a.val.2.Mnum) :=
    meas_Mnum.comp measurable_subtype_coe
  have hrf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      (fun i : Torus d m => a.val.1.r i)) := by
    apply Measurable.of_eval
    intro y
    exact (measurable_pi_apply _).comp
      (meas_rec_r.comp measurable_subtype_coe)
  have hcross_joint : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) := by
    refine Measurable.of_eval_matrix _ fun xb yb => ?_
    exact tool_xcross_eval t hrf hMf xb yb
  have hpair : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      ((xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀), τ)) :=
    hcross_joint.prodMk measurable_const
  have hlev : Measurable (fun p : Matrix (Torus d m) {b // b ∈ B₀} ℂ × ℝ =>
      AndersonAC.S6.leverage p.1 p.2 i) :=
    AndersonAC.AgentS6.measurable_leverage i
  have hcomp : Measurable ((fun p : Matrix (Torus d m) {b // b ∈ B₀} ℂ × ℝ =>
      AndersonAC.S6.leverage p.1 p.2 i) ∘
    (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      ((xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀), τ))) :=
    hlev.comp hpair
  exact hcomp

/-- Start ridge on a (core, active) fiber is measurable
(`chooseRidge` of the fixed-set cross matrix). -/
theorem fiber_ridge (t l : ℝ) (hl : 0 < l) :
    Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      AndersonAC.S6.chooseRidge
        (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀)
        l (l ^ (-2 : ℤ))) := by
  have hcross_joint : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) := by
    have hMf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
        a.val.2.Mnum) :=
      meas_Mnum.comp measurable_subtype_coe
    have hrf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
        (fun i : Torus d m => a.val.1.r i)) := by
      apply Measurable.of_eval
      intro y
      exact (measurable_pi_apply _).comp
        (meas_rec_r.comp measurable_subtype_coe)
    refine Measurable.of_eval_matrix _ fun xb yb => ?_
    exact tool_xcross_eval t hrf hMf xb yb
  -- chooseRidge C l τ = if maxWeight (leverage C τ) < 2*l then ridgeThreshold C l else τ
  have hmax : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
        (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀)
        (l ^ (-2 : ℤ)))) :=
    measurable_maxWeight_of (fun i => fiber_weights_fixed (A₀ := A₀) (B₀ := B₀) t (l ^ (-2 : ℤ)) i)
  have hthresh : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      AndersonAC.S6.ridgeThreshold
        (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) l) :=
    ((AndersonAC.S6.ridge_threshold_measurable (R := Torus d m)
      (B := {b // b ∈ B₀}) l hl).1).comp hcross_joint
  have hcond : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) |
      AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
        (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀)
        (l ^ (-2 : ℤ))) < 2 * l} :=
    measurableSet_lt hmax measurable_const
  refine Measurable.ite hcond hthresh measurable_const

end FiberWeights

section FiberS6Vals
variable {d m : ℕ}
variable {A₀ B₀ : Finset (Torus d m)}

/-- Fiber coordinate inclusion (subtype coe is measurable). -/
theorem fiber_coe_meas' :
    Measurable (Subtype.val : ↥(scratchFiber (d := d) (m := m) B₀ A₀) →
      RunRecord d m × ClearScratch d m) :=
  measurable_subtype_coe

/-- maxWeight on a fiber is measurable. -/
theorem fiber_maxWeight' (t : ℝ) :
    Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      AndersonAC.S6.maxWeight
        (scratchWeights t (a.val.1.r) a.val.2 (a.val.2.ridge))) :=
  measurable_maxWeight_of (fun i => fiber_weights_eval (A₀ := A₀) (B₀ := B₀) t i)

/-- Cross matrix joint measurability on a fiber. -/
theorem fiber_cross_joint' (t : ℝ) :
    Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      xCross t (a.val.1.r) A₀
        (restrictM A₀ (a.val.2.Mnum)) B₀) := by
  have hMf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      a.val.2.Mnum) :=
    meas_Mnum.comp measurable_subtype_coe
  have hrf : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      (fun i : Torus d m => a.val.1.r i)) := by
    apply Measurable.of_eval
    intro y
    exact (measurable_pi_apply _).comp (meas_rec_r.comp measurable_subtype_coe)
  refine Measurable.of_eval_matrix _ fun xb yb => ?_
  exact tool_xcross_eval t hrf hMf xb yb

/-- Projection-readiness on a fiber (`xReady`: bound `2 * leverageScale t`).
`rangeProjection` measurability comes from `ridge_threshold_measurable`
at level 1 (the projection itself is level-independent), so no
positivity hypothesis is needed. -/
theorem fiber_ready_set' (t : ℝ) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) |
      xReady t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀} := by
  have hset : {a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) |
        xReady t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀}
      = ⋂ i, {a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) |
        AndersonAC.S6.projectionWeight
          (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) i ≤
          2 * AndersonAC.S6.leverageScale t} := by
    ext a
    simp [xReady]
  rw [hset]
  refine MeasurableSet.iInter fun i => ?_
  have hrp : Measurable (fun C : Matrix (Torus d m) {b // b ∈ B₀} ℂ =>
      AndersonAC.S6.rangeProjection C) :=
    (AndersonAC.S6.ridge_threshold_measurable (R := Torus d m)
      (B := {b // b ∈ B₀}) 1 zero_lt_one).2
  have hpw : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
      AndersonAC.S6.projectionWeight
        (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) i) := by
    have heq : (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
          AndersonAC.S6.projectionWeight
            (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀) i)
        = (fun a : ↥(scratchFiber (d := d) (m := m) B₀ A₀) =>
          ((AndersonAC.S6.rangeProjection
            (xCross t (a.val.1.r) A₀ (restrictM A₀ (a.val.2.Mnum)) B₀)) i i).re) := by
      funext a
      rfl
    rw [heq]
    exact Complex.continuous_re.measurable.comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (hrp.comp (fiber_cross_joint' (A₀ := A₀) (B₀ := B₀) t))))
  exact measurableSet_le hpw measurable_const

end FiberS6Vals

section S6Meas
variable {d m : ℕ}

/-- Matrix entry evaluations from scratch coordinates. -/
theorem meas_Mnum_eval (i j : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.Mnum i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp meas_Mnum)

theorem meas_hatG_eval (i j : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.hatG i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp meas_hatG)

theorem meas_g0_eval (i j : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.g0 i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp meas_g0)

theorem meas_r_eval (i : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.r i) :=
  (measurable_pi_apply i).comp meas_rec_r

theorem meas_resids_eval (y : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.resids y) :=
  (measurable_pi_apply y).comp meas_resids

theorem meas_recM_eval (i j : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.endpoint.M i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp meas_rec_M)

theorem meas_recg_eval (i j : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.endpoint.g i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp meas_rec_g)

theorem meas_prefix_eval (y : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.prefixLength y) :=
  (measurable_pi_apply y).comp meas_rec_prefix

theorem meas_installed_eval (y : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => s.1.installed y) :=
  (measurable_pi_apply y).comp meas_rec_installed

/-- `Option.getD false` on answers is measurable (finite discrete). -/
theorem meas_getD_false :
    Measurable (fun o : Option Bool => o.getD false) := by
  refine measurable_of_singleton_fibers fun b => ?_
  cases b with
  | true =>
    have heq : (fun o : Option Bool => o.getD false) ⁻¹' {true} = {some true} := by
      ext o
      cases o with
      | none => simp
      | some c => cases c <;> simp
    rw [heq]
    exact measurableSet_singleton _
  | false =>
    have heq : (fun o : Option Bool => o.getD false) ⁻¹' {false} = {none, some false} := by
      ext o
      cases o with
      | none => simp
      | some c => cases c <;> simp
    rw [heq]
    exact (measurableSet_singleton _).union (measurableSet_singleton _)

/-- S6 budgets as a measurable set (full matrices, no subtypes). -/
theorem measSet_budgets (t : ℝ) :
    MeasurableSet {s : RunRecord d m × ClearScratch d m |
      AndersonAC.S6.BudgetsHold t s.2.g0 s.2.hatG} := by
  have hrow : ∀ i : Torus d m, Measurable (fun s : RunRecord d m × ClearScratch d m =>
      AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t (s.2.hatG - s.2.g0)) i) := by
    intro i
    unfold AndersonAC.S6.sqRow AndersonAC.S6.scaledInverse
    refine Finset.measurable_sum _ fun j _ => ?_
    have hsmul_meas : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        ((Real.sqrt t : ℂ) • (s.2.hatG - s.2.g0)) i j) := by
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
          ((Real.sqrt t : ℂ) • (s.2.hatG - s.2.g0)) i j)
          = fun s => (Real.sqrt t : ℂ) * (s.2.hatG i j - s.2.g0 i j) := by
        funext s
        simp [Matrix.smul_apply, smul_eq_mul]
      rw [heq]
      exact measurable_const.mul ((meas_hatG_eval i j).sub (meas_g0_eval i j))
    have hnorm : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        ‖((Real.sqrt t : ℂ) • (s.2.hatG - s.2.g0)) i j‖) :=
      continuous_norm.measurable.comp hsmul_meas
    have hsq : (fun s : RunRecord d m × ClearScratch d m =>
        ‖((Real.sqrt t : ℂ) • (s.2.hatG - s.2.g0)) i j‖ ^ 2)
        = fun s => ‖((Real.sqrt t : ℂ) • (s.2.hatG - s.2.g0)) i j‖ *
          ‖((Real.sqrt t : ℂ) • (s.2.hatG - s.2.g0)) i j‖ := by
      funext s
      rw [sq]
    rw [hsq]
    exact hnorm.mul hnorm
  unfold AndersonAC.S6.BudgetsHold
  simp only [Set.setOf_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · -- entry budget
    have : {s : RunRecord d m × ClearScratch d m |
          ∀ i j, ‖s.2.hatG i j - s.2.g0 i j‖ ≤ AndersonAC.S6.entryBudget t}
        = ⋂ i ∈ Finset.univ, ⋂ j ∈ Finset.univ,
          {s : RunRecord d m × ClearScratch d m |
            ‖s.2.hatG i j - s.2.g0 i j‖ ≤ AndersonAC.S6.entryBudget t} := by
      ext s
      simp
    rw [this]
    refine Finset.measurableSet_biInter _ fun i _ => ?_
    refine Finset.measurableSet_biInter _ fun j _ => ?_
    apply measurableSet_le _ measurable_const
    exact (continuous_norm.measurable.comp
      ((meas_hatG_eval i j).sub (meas_g0_eval i j)))
  · -- row budget
    have hset : {s : RunRecord d m × ClearScratch d m |
          ∀ i, AndersonAC.S6.sqRow
            (AndersonAC.S6.scaledInverse t (s.2.hatG - s.2.g0)) i ≤
            AndersonAC.S6.rowBudget t}
        = ⋂ i ∈ Finset.univ,
          {s : RunRecord d m × ClearScratch d m |
            AndersonAC.S6.sqRow
              (AndersonAC.S6.scaledInverse t (s.2.hatG - s.2.g0)) i ≤
              AndersonAC.S6.rowBudget t} := by
      ext s
      simp
    rw [hset]
    refine Finset.measurableSet_biInter _ fun i _ => ?_
    exact measurableSet_le (hrow i) measurable_const
  · -- frobenius budget
    have hfrob : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        AndersonAC.S6.hsSq (AndersonAC.S6.scaledInverse t (s.2.hatG - s.2.g0))) := by
      unfold AndersonAC.S6.hsSq
      refine Finset.measurable_sum _ fun i _ => ?_
      exact hrow i
    exact measurableSet_le hfrob measurable_const

end S6Meas

/-! ## Pattern measurability (`hcpatm`) via singleton fibers -/

section PatMeas
variable {d m : ℕ}

/-- Record-alone `aborted` projection. -/
theorem pat_meas_aborted :
    Measurable (fun rc : RunRecord d m => rc.aborted) := by
  have h : (fun rc : RunRecord d m => rc.aborted)
      = (fun p => p.2.2.2.2.2.2) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Record-alone active indicator. -/
theorem pat_meas_active_ind :
    Measurable (fun rc : RunRecord d m => finsetCode rc.endpoint.active) := by
  have h : (fun rc : RunRecord d m => finsetCode rc.endpoint.active)
      = (fun p => p.2.1.1) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Record-alone pending indicator. -/
theorem pat_meas_pending_ind :
    Measurable (fun rc : RunRecord d m => finsetCode rc.pending) := by
  have h : (fun rc : RunRecord d m => finsetCode rc.pending)
      = (fun p => p.2.2.2.2.1.2.1) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Record-alone terminal indicator. -/
theorem pat_meas_terminal_ind :
    Measurable (fun rc : RunRecord d m => finsetCode rc.terminal) := by
  have h : (fun rc : RunRecord d m => finsetCode rc.terminal)
      = (fun p => p.2.2.2.2.1.1) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Record-alone prefix lengths. -/
theorem pat_meas_prefix :
    Measurable (fun rc : RunRecord d m => rc.prefixLength) := by
  have h : (fun rc : RunRecord d m => rc.prefixLength)
      = (fun p => p.2.2.2.1.2) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Record-alone endpoint matrix. -/
theorem pat_meas_M :
    Measurable (fun rc : RunRecord d m => rc.endpoint.M) := by
  have h : (fun rc : RunRecord d m => rc.endpoint.M)
      = (fun p => p.2.1.2.1) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Record-alone endpoint inverse. -/
theorem pat_meas_g :
    Measurable (fun rc : RunRecord d m => rc.endpoint.g) := by
  have h : (fun rc : RunRecord d m => rc.endpoint.g)
      = (fun p => p.2.1.2.2.1) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

/-- Record-alone damping. -/
theorem pat_meas_r :
    Measurable (fun rc : RunRecord d m => rc.r) := by
  have h : (fun rc : RunRecord d m => rc.r)
      = (fun p => p.2.1.2.2.2) ∘ RunRecord.code := rfl
  rw [h]
  exact Measurable.comp (by fun_prop) (RunRecord.measurable_code _ _)

theorem patSet_active_mem (y : Torus d m) :
    MeasurableSet {rc : RunRecord d m | y ∈ rc.endpoint.active} := by
  have hmeas : Measurable (fun rc : RunRecord d m => finsetCode rc.endpoint.active y) :=
    (measurable_pi_apply y).comp pat_meas_active_ind
  have : {rc : RunRecord d m | y ∈ rc.endpoint.active}
      = (fun rc : RunRecord d m => finsetCode rc.endpoint.active y) ⁻¹' {true} := by
    ext rc
    simp [finsetCode]
  rw [this]
  exact hmeas (measurableSet_singleton true)

theorem patSet_pending_mem (y : Torus d m) :
    MeasurableSet {rc : RunRecord d m | y ∈ rc.pending} := by
  have hmeas : Measurable (fun rc : RunRecord d m => finsetCode rc.pending y) :=
    (measurable_pi_apply y).comp pat_meas_pending_ind
  have : {rc : RunRecord d m | y ∈ rc.pending}
      = (fun rc : RunRecord d m => finsetCode rc.pending y) ⁻¹' {true} := by
    ext rc
    simp [finsetCode]
  rw [this]
  exact hmeas (measurableSet_singleton true)

theorem patSet_terminal_mem (y : Torus d m) :
    MeasurableSet {rc : RunRecord d m | y ∈ rc.terminal} := by
  have hmeas : Measurable (fun rc : RunRecord d m => finsetCode rc.terminal y) :=
    (measurable_pi_apply y).comp pat_meas_terminal_ind
  have : {rc : RunRecord d m | y ∈ rc.terminal}
      = (fun rc : RunRecord d m => finsetCode rc.terminal y) ⁻¹' {true} := by
    ext rc
    simp [finsetCode]
  rw [this]
  exact hmeas (measurableSet_singleton true)

/-- Record `theCore` fibers are measurable. -/
theorem patSet_theCore_eq (j : ℕ) (u : ℝ) (x : Torus d m)
    (B₀ : Finset (Torus d m)) :
    MeasurableSet {rc : RunRecord d m |
      theCore (d := d) (m := m) j u x rc = B₀} := by
  classical
  have hfib : {rc : RunRecord d m |
        theCore (d := d) (m := m) j u x rc = B₀}
      = ⋂ y, (({rc : RunRecord d m | y ∈ theCore (d := d) (m := m) j u x rc} ∩
          {rc : RunRecord d m | y ∈ B₀}) ∪
        (({rc : RunRecord d m | y ∈ theCore (d := d) (m := m) j u x rc}ᶜ) ∩
          {rc : RunRecord d m | y ∈ B₀}ᶜ)) := by
    ext rc
    simp only [Set.mem_iInter, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h y
      by_cases hy : y ∈ theCore (d := d) (m := m) j u x rc
      · have hy' : y ∈ B₀ := by rw [← h]; exact hy
        exact Or.inl ⟨hy, hy'⟩
      · have hy' : y ∉ B₀ := by
          intro hc
          apply hy
          rw [h]
          exact hc
        exact Or.inr ⟨hy, hy'⟩
    · intro h
      ext y
      have hy := h y
      tauto
  rw [hfib]
  refine MeasurableSet.iInter fun y => ?_
  have hfix : MeasurableSet {rc : RunRecord d m | y ∈ B₀} := by
    by_cases hy : y ∈ B₀
    · simpa [hy] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set (RunRecord d m)))
    · have : {rc : RunRecord d m | y ∈ B₀} = ∅ := by
        ext rc
        simp [hy]
      rw [this]
      exact MeasurableSet.empty
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.inter (measSet_theCore_mem j u x y) hfix
  · exact MeasurableSet.inter (measSet_theCore_mem j u x y).compl hfix.compl

/-- Record active-set fibers are measurable. -/
theorem patSet_active_eq (A₀ : Finset (Torus d m)) :
    MeasurableSet {rc : RunRecord d m | rc.endpoint.active = A₀} := by
  classical
  have hfib : {rc : RunRecord d m | rc.endpoint.active = A₀}
      = ⋂ y, (({rc : RunRecord d m | y ∈ rc.endpoint.active} ∩
          {rc : RunRecord d m | y ∈ A₀}) ∪
        (({rc : RunRecord d m | y ∈ rc.endpoint.active}ᶜ) ∩
          {rc : RunRecord d m | y ∈ A₀}ᶜ)) := by
    ext rc
    simp only [Set.mem_iInter, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h y
      by_cases hy : y ∈ rc.endpoint.active
      · have hy' : y ∈ A₀ := by rw [← h]; exact hy
        exact Or.inl ⟨hy, hy'⟩
      · have hy' : y ∉ A₀ := by
          intro hc
          apply hy
          rw [h]
          exact hc
        exact Or.inr ⟨hy, hy'⟩
    · intro h
      ext y
      have hy := h y
      tauto
  rw [hfib]
  refine MeasurableSet.iInter fun y => ?_
  have hfix : MeasurableSet {rc : RunRecord d m | y ∈ A₀} := by
    by_cases hy : y ∈ A₀
    · simpa [hy] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set (RunRecord d m)))
    · have : {rc : RunRecord d m | y ∈ A₀} = ∅ := by
        ext rc
        simp [hy]
      rw [this]
      exact MeasurableSet.empty
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.inter (patSet_active_mem y) hfix
  · exact MeasurableSet.inter (patSet_active_mem y).compl hfix.compl
theorem patSet_aborted_eq (b : Bool) :
    MeasurableSet {rc : RunRecord d m | rc.aborted = b} := by
  have heq : {rc : RunRecord d m | rc.aborted = b}
      = (fun rc : RunRecord d m => rc.aborted) ⁻¹' {b} := rfl
  rw [heq]
  exact pat_meas_aborted (measurableSet_singleton b)

theorem patSet_prefix_eq (y : Torus d m) (n : ℕ) :
    MeasurableSet {rc : RunRecord d m | rc.prefixLength y = n} := by
  have hmeas : Measurable (fun rc : RunRecord d m => rc.prefixLength y) :=
    (measurable_pi_apply y).comp pat_meas_prefix
  exact hmeas (measurableSet_singleton n)

/-- Membership in the pattern sites is measurable (coupled active minus
terminal, gated by aborted/schedule/theCore). Proved via the decidable
indicator and `Measurable.ite`. -/
theorem patSet_sites_mem (n₀ j : ℕ) (u : ℝ) (x y : Torus d m) :
    MeasurableSet {rc : RunRecord d m |
      y ∈ (clearingPattern (d := d) (m := m) n₀ j u x rc).sites} := by
  by_cases hsched : clearingScheduled j m
  · have hemptySet : MeasurableSet {rc : RunRecord d m |
        theCore (d := d) (m := m) j u x rc = ∅} := by
      have : {rc : RunRecord d m |
            theCore (d := d) (m := m) j u x rc = ∅}
          = ⋂ y, {rc : RunRecord d m | y ∈ theCore (d := d) (m := m) j u x rc}ᶜ := by
        ext rc
        simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
        exact Finset.eq_empty_iff_forall_notMem
      rw [this]
      refine MeasurableSet.iInter fun y => ?_
      exact (measSet_theCore_mem j u x y).compl
    have habSet : MeasurableSet {rc : RunRecord d m | rc.aborted} := by
      have heq : {rc : RunRecord d m | rc.aborted}
          = (fun rc : RunRecord d m => rc.aborted) ⁻¹' {true} := by
        ext rc
        simp
      rw [heq]
      exact pat_meas_aborted (measurableSet_singleton true)
    have htriple : Measurable (fun rc : RunRecord d m =>
        decide (y ∈ rc.endpoint.active ∧ y ∉ rc.pending ∧ y ∉ rc.terminal)) := by
      refine measurable_of_singleton_fibers fun b => ?_
      cases b with
      | true =>
        have heq : (fun rc : RunRecord d m =>
              decide (y ∈ rc.endpoint.active ∧ y ∉ rc.pending ∧ y ∉ rc.terminal)) ⁻¹' {true}
            = {rc : RunRecord d m | y ∈ rc.endpoint.active} ∩
              (({rc : RunRecord d m | y ∈ rc.pending}ᶜ) ∩
                ({rc : RunRecord d m | y ∈ rc.terminal}ᶜ)) := by
          ext rc
          simp
        rw [heq]
        exact (patSet_active_mem y).inter
          ((patSet_pending_mem y).compl.inter (patSet_terminal_mem y).compl)
      | false =>
        have heq : (fun rc : RunRecord d m =>
              decide (y ∈ rc.endpoint.active ∧ y ∉ rc.pending ∧ y ∉ rc.terminal)) ⁻¹' {false}
            = ({rc : RunRecord d m | y ∈ rc.endpoint.active} ∩
              (({rc : RunRecord d m | y ∈ rc.pending}ᶜ) ∩
                ({rc : RunRecord d m | y ∈ rc.terminal}ᶜ)))ᶜ := by
          ext rc
          simp
        rw [heq]
        exact ((patSet_active_mem y).inter
          ((patSet_pending_mem y).compl.inter (patSet_terminal_mem y).compl)).compl
    have hinner : Measurable (fun rc : RunRecord d m =>
        if theCore (d := d) (m := m) j u x rc = ∅ then (false : Bool)
        else decide (y ∈ rc.endpoint.active ∧ y ∉ rc.pending ∧ y ∉ rc.terminal)) :=
      Measurable.ite hemptySet measurable_const htriple
    have hfull : Measurable (fun rc : RunRecord d m =>
        if rc.aborted then (false : Bool)
        else if theCore (d := d) (m := m) j u x rc = ∅ then (false : Bool)
        else decide (y ∈ rc.endpoint.active ∧ y ∉ rc.pending ∧ y ∉ rc.terminal)) :=
      Measurable.ite habSet measurable_const hinner
    have hmatch : (fun rc : RunRecord d m =>
          decide (y ∈ (clearingPattern (d := d) (m := m) n₀ j u x rc).sites))
        = (fun rc : RunRecord d m =>
          if rc.aborted then (false : Bool)
          else if theCore (d := d) (m := m) j u x rc = ∅ then (false : Bool)
          else decide (y ∈ rc.endpoint.active ∧ y ∉ rc.pending ∧ y ∉ rc.terminal)) := by
      funext rc
      by_cases hab : rc.aborted = true
      · unfold clearingPattern
        simp [hab]
      · by_cases hcore : theCore (d := d) (m := m) j u x rc = ∅
        · unfold clearingPattern
          simp [hab, hsched, hcore]
        · unfold clearingPattern
          simp [hab, hsched, hcore, coupledActive, Finset.mem_sdiff, and_assoc]
    have heq : {rc : RunRecord d m |
          y ∈ (clearingPattern (d := d) (m := m) n₀ j u x rc).sites}
        = (fun rc : RunRecord d m =>
            if rc.aborted then (false : Bool)
            else if theCore (d := d) (m := m) j u x rc = ∅ then (false : Bool)
            else decide (y ∈ rc.endpoint.active ∧ y ∉ rc.pending ∧ y ∉ rc.terminal)) ⁻¹' {true} := by
      rw [← hmatch]
      ext rc
      simp
    rw [heq]
    exact hfull (measurableSet_singleton true)
  · -- unscheduled: pattern sites always ∅
    have hempty : {rc : RunRecord d m |
        y ∈ (clearingPattern (d := d) (m := m) n₀ j u x rc).sites} = ∅ := by
      ext rc
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hy
      unfold clearingPattern at hy
      simp only at hy
      simp [hsched] at hy
    rw [hempty]
    exact MeasurableSet.empty

end PatMeas

/-- Fixed-ridge weights on a record fiber (for `enter`'s ridge;
record domain, `restrictM` form). -/
theorem recFiber_weights_fixed {d m : ℕ} (t τ : ℝ)
    (B₀ A₀ : Finset (Torus d m)) (i : Torus d m) :
    Measurable (fun rc : RunRecord d m =>
      AndersonAC.S6.leverage
        (xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
        τ i) := by
  have hMf : Measurable (fun rc : RunRecord d m =>
      (fun i j => (rc.endpoint.M i j).re)) := by
    apply Measurable.of_eval
    intro a
    apply Measurable.of_eval
    intro b
    exact Complex.continuous_re.measurable.comp
      ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp pat_meas_M))
  have hrf : Measurable (fun rc : RunRecord d m => (fun i : Torus d m => rc.r i)) := by
    apply Measurable.of_eval
    intro y
    exact (measurable_pi_apply _).comp pat_meas_r
  have hcross : Measurable (fun rc : RunRecord d m =>
      xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀) := by
    refine Measurable.of_eval_matrix _ fun xb yb => ?_
    exact tool_xcross_eval t hrf hMf xb yb
  have hpair : Measurable (fun rc : RunRecord d m =>
      ((xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀), τ)) :=
    hcross.prodMk measurable_const
  have hlev : Measurable (fun p : Matrix (Torus d m) {b // b ∈ B₀} ℂ × ℝ =>
      AndersonAC.S6.leverage p.1 p.2 i) :=
    AndersonAC.AgentS6.measurable_leverage i
  have hcomp : Measurable ((fun p : Matrix (Torus d m) {b // b ∈ B₀} ℂ × ℝ =>
      AndersonAC.S6.leverage p.1 p.2 i) ∘
    (fun rc : RunRecord d m =>
      ((xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀), τ))) :=
    hlev.comp hpair
  exact hcomp

/-- Start ridge on a record fiber (fixed eligible core and active set)
is measurable (for `enter`; `restrictM` form throughout, inferred
`tool_xcross_eval`, positivity split for `chooseRidge`). -/
theorem recFiber_ridge {d m : ℕ} (j : ℕ) (u : ℝ) (x : Torus d m)
    (B₀ A₀ : Finset (Torus d m)) :
    Measurable (fun rc : RunRecord d m =>
      AndersonAC.S6.chooseRidge
        (xCross (stageScale u j m) (rc.r) A₀
          (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
        (AndersonAC.S6.leverageScale (stageScale u j m))
        ((AndersonAC.S6.leverageScale (stageScale u j m)) ^ (-2 : ℤ))) := by
  classical
  set t := stageScale u j m with ht
  set l := AndersonAC.S6.leverageScale t with hl_def
  have hMf : Measurable (fun rc : RunRecord d m =>
      (fun i j => (rc.endpoint.M i j).re)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact Complex.continuous_re.measurable.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp pat_meas_M))
  have hrf : Measurable (fun rc : RunRecord d m => (fun i : Torus d m => rc.r i)) := by
    apply Measurable.of_eval
    intro y
    exact (measurable_pi_apply _).comp pat_meas_r
  have hcross : Measurable (fun rc : RunRecord d m =>
      xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀) := by
    refine Measurable.of_eval_matrix _ fun xb yb => ?_
    exact tool_xcross_eval t hrf hMf xb yb
  by_cases hl : 0 < l
  · have hmax : Measurable (fun rc : RunRecord d m =>
        AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
          (xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
          (l ^ (-2 : ℤ)))) :=
      measurable_maxWeight_of (fun i =>
        recFiber_weights_fixed (t := t) (τ := l ^ (-2 : ℤ)) B₀ A₀ i)
    have hthresh : Measurable (fun rc : RunRecord d m =>
        AndersonAC.S6.ridgeThreshold
          (xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀) l) :=
      ((AndersonAC.S6.ridge_threshold_measurable (R := Torus d m)
        (B := {b // b ∈ B₀}) l hl).1).comp hcross
    have hcond : MeasurableSet {rc : RunRecord d m |
        AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
          (xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
          (l ^ (-2 : ℤ))) < 2 * l} :=
      measurableSet_lt hmax measurable_const
    have heq : (fun rc : RunRecord d m =>
          AndersonAC.S6.chooseRidge
            (xCross t (rc.r) A₀
              (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
            l (l ^ (-2 : ℤ)))
        = (fun rc : RunRecord d m =>
          if AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
              (xCross t (rc.r) A₀
                (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
              (l ^ (-2 : ℤ))) < 2 * l then
            AndersonAC.S6.ridgeThreshold
              (xCross t (rc.r) A₀
                (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀) l
          else (l ^ (-2 : ℤ))) := by
      funext rc
      rfl
    rw [heq]
    exact Measurable.ite hcond hthresh measurable_const
  · push_neg at hl
    have hconst : (fun rc : RunRecord d m =>
          AndersonAC.S6.chooseRidge
            (xCross t (rc.r) A₀
              (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
            l (l ^ (-2 : ℤ)))
        = (fun _ : RunRecord d m => (l ^ (-2 : ℤ))) := by
      funext rc
      have hneg : ¬ AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
          (xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
          (l ^ (-2 : ℤ))) < 2 * l := by
        have hnn := maxWeight_nonneg (AndersonAC.S6.leverage
          (xCross t (rc.r) A₀ (restrictM A₀ (fun i j => (rc.endpoint.M i j).re)) B₀)
          (l ^ (-2 : ℤ)))
        linarith
      unfold AndersonAC.S6.chooseRidge
      rw [if_neg hneg]
    rw [hconst]
    exact measurable_const

/-! ## Block measurability (`hcmeas`): components -/

section BlockMeas
variable {d m : ℕ} {n₀ j : ℕ} {u : ℝ} {x : Torus d m}

/-- `firstFail` is a measurable projection. -/
theorem block_firstFail_meas :
    Measurable (clearingFirstFail (d := d) (m := m)) :=
  meas_failed

/-- `halted` is measurable (finite Boolean combination). -/
theorem block_halted_meas :
    Measurable (clearingHalted (d := d) (m := m)) := by
  refine measurable_of_singleton_fibers fun b => ?_
  cases b with
  | true =>
    have heq : (clearingHalted (d := d) (m := m)) ⁻¹' {true}
        = {s : RunRecord d m × ClearScratch d m | s.2.failed = true} ∪
          {s : RunRecord d m × ClearScratch d m | s.2.done = true} := by
      ext s
      simp [clearingHalted]
    rw [heq]
    exact (meas_failed (measurableSet_singleton true)).union
      (meas_done (measurableSet_singleton true))
  | false =>
    have heq : (clearingHalted (d := d) (m := m)) ⁻¹' {false}
        = ({s : RunRecord d m × ClearScratch d m | s.2.failed = true} ∪
          {s : RunRecord d m × ClearScratch d m | s.2.done = true})ᶜ := by
      ext s
      simp [clearingHalted]
    rw [heq]
    exact ((meas_failed (measurableSet_singleton true)).union
      (meas_done (measurableSet_singleton true))).compl

/-- `clearInitScratch` is measurable (`enter` of the block). Only the
ridge needs fiber glue (fixed core/active via `recFiber_ridge`); all
other coordinates are global. -/
theorem initScratch_meas {d m : ℕ} (j : ℕ) (u : ℝ) (x : Torus d m) :
    Measurable (clearInitScratch (d := d) (m := m) j u x) := by
  classical
  refine measurable_comap_iff.mpr ?_
  -- ridge coordinate via double-fiber glue
  have hridge : Measurable (fun rc : RunRecord d m =>
      (clearInitScratch (d := d) (m := m) j u x rc).ridge) := by
    apply Measurable.of_finite_fiber
      (fib := fun p : Finset (Torus d m) × Finset (Torus d m) =>
        {rc : RunRecord d m | theCore (d := d) (m := m) j u x rc = p.1} ∩
        {rc : RunRecord d m | rc.endpoint.active = p.2})
    · intro rc
      exact ⟨(theCore (d := d) (m := m) j u x rc, rc.endpoint.active),
        rfl, rfl⟩
    · intro p
      exact (patSet_theCore_eq j u x p.1).inter (patSet_active_eq p.2)
    · intro p
      -- on this fiber, the ridge equals the fixed-set form
      have hfib : (fun a : ↥({rc : RunRecord d m | theCore (d := d) (m := m) j u x rc = p.1} ∩
          {rc : RunRecord d m | rc.endpoint.active = p.2}) =>
          (clearInitScratch (d := d) (m := m) j u x a.val).ridge)
          = (fun a =>
            AndersonAC.S6.chooseRidge
              (xCross (stageScale u j m) (a.val.r) p.2
                (restrictM p.2 (fun i j => (a.val.endpoint.M i j).re)) p.1)
              (AndersonAC.S6.leverageScale (stageScale u j m))
              ((AndersonAC.S6.leverageScale (stageScale u j m)) ^ (-2 : ℤ))) := by
        funext a
        have hc : theCore (d := d) (m := m) j u x a.val = p.1 := a.property.1
        have ha : a.val.endpoint.active = p.2 := a.property.2
        simp only [clearInitScratch]
        rw [hc, ha]
      rw [hfib]
      exact (recFiber_ridge j u x p.1 p.2).comp measurable_subtype_coe
  -- remaining coordinates are global (indicators/consts/endpoint data)
  have hcore_ind : Measurable (fun rc : RunRecord d m =>
      finsetCode (theCore (d := d) (m := m) j u x rc)) := by
    apply Measurable.of_eval
    intro y
    refine measurable_of_singleton_fibers fun b => ?_
    cases b with
    | true =>
      have heq : (fun rc : RunRecord d m => finsetCode
            (theCore (d := d) (m := m) j u x rc) y) ⁻¹' {true}
          = {rc : RunRecord d m | y ∈ theCore (d := d) (m := m) j u x rc} := by
        ext rc
        simp [finsetCode]
      rw [heq]
      exact measSet_theCore_mem j u x y
    | false =>
      have heq : (fun rc : RunRecord d m => finsetCode
            (theCore (d := d) (m := m) j u x rc) y) ⁻¹' {false}
          = {rc : RunRecord d m | y ∈ theCore (d := d) (m := m) j u x rc}ᶜ := by
        ext rc
        simp [finsetCode]
      rw [heq]
      exact (measSet_theCore_mem j u x y).compl
  have hactive_ind : Measurable (fun rc : RunRecord d m =>
      finsetCode rc.endpoint.active) :=
    pat_meas_active_ind
  have hMnum : Measurable (fun rc : RunRecord d m =>
      (fun i j => (rc.endpoint.M i j).re)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact Complex.continuous_re.measurable.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp pat_meas_M))
  have hhatG : Measurable (fun rc : RunRecord d m => rc.endpoint.g) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp pat_meas_g)
  have hdone : Measurable (fun rc : RunRecord d m =>
      (clearInitScratch (d := d) (m := m) j u x rc).done) := by
    have htrue : MeasurableSet ((fun rc : RunRecord d m =>
        (clearInitScratch (d := d) (m := m) j u x rc).done) ⁻¹' {true}) := by
      have heq : ((fun rc : RunRecord d m =>
          (clearInitScratch (d := d) (m := m) j u x rc).done) ⁻¹' {true})
          = {rc : RunRecord d m | theCore (d := d) (m := m) j u x rc = ∅} ∪
            {rc : RunRecord d m | rc.aborted = true} ∪
            (if ¬clearingScheduled j m then Set.univ else ∅) := by
        ext rc
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_setOf_eq]
        unfold clearInitScratch
        simp only
        by_cases hab : rc.aborted = true
        · simp [hab]
        · simp only [hab, ↓reduceIte, Bool.or_eq_true, Bool.not_eq_true]
          by_cases hcore : theCore (d := d) (m := m) j u x rc = ∅
          · simp [hcore]
          · simp only [hcore, ↓reduceIte]
            by_cases hsch : clearingScheduled j m
            · simp [hsch]
            · simp [hsch]
      rw [heq]
      have hempty_core : MeasurableSet {rc : RunRecord d m |
          theCore (d := d) (m := m) j u x rc = ∅} := by
        have : {rc : RunRecord d m |
              theCore (d := d) (m := m) j u x rc = ∅}
            = ⋂ y, {rc : RunRecord d m |
              y ∈ theCore (d := d) (m := m) j u x rc}ᶜ := by
          ext rc
          simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
          exact Finset.eq_empty_iff_forall_notMem
        rw [this]
        exact MeasurableSet.iInter fun y => (measSet_theCore_mem j u x y).compl
      have habort : MeasurableSet {rc : RunRecord d m | rc.aborted = true} :=
        pat_meas_aborted (measurableSet_singleton true)
      by_cases hsch : clearingScheduled j m
      · have : (if ¬clearingScheduled j m then Set.univ else ∅) =
            (∅ : Set (RunRecord d m)) := by
          simp [hsch]
        rw [this]
        exact (hempty_core.union habort).union MeasurableSet.empty
      · have : (if ¬clearingScheduled j m then Set.univ else ∅) =
            (Set.univ : Set (RunRecord d m)) := by
          simp [hsch]
        rw [this]
        simpa using MeasurableSet.univ
    refine measurable_of_singleton_fibers fun b => ?_
    cases b with
    | true => exact htrue
    | false =>
      have heq : (fun rc : RunRecord d m =>
            (clearInitScratch (d := d) (m := m) j u x rc).done) ⁻¹' {false}
          = ((fun rc : RunRecord d m =>
            (clearInitScratch (d := d) (m := m) j u x rc).done) ⁻¹' {true})ᶜ := by
        ext rc
        simp
      rw [heq]
      exact htrue.compl
  have hinspected : Measurable (fun _ : RunRecord d m =>
      finsetCode (∅ : Finset (Torus d m))) :=
    measurable_const
  have hstep0 : Measurable (fun _ : RunRecord d m => (0 : ℕ)) :=
    measurable_const
  have hresids0 : Measurable (fun _ : RunRecord d m =>
      (fun _ : Torus d m => (0 : ℝ))) :=
    measurable_const
  have hfailed0 : Measurable (fun _ : RunRecord d m => false) :=
    measurable_const
  have hcorePhase0 : Measurable (fun _ : RunRecord d m => false) :=
    measurable_const
  -- assemble the code tuple
  refine Measurable.prodMk ?_ ?_
  · exact hcore_ind
  · refine Measurable.prodMk ?_ ?_
    · exact hactive_ind
    · refine Measurable.prodMk ?_ ?_
      · exact hinspected
      · refine Measurable.prodMk ?_ ?_
        · exact hcore_ind
        · refine Measurable.prodMk ?_ ?_
          · exact hstep0
          · refine Measurable.prodMk ?_ ?_
            · exact hridge
            · refine Measurable.prodMk ?_ ?_
              · exact hMnum
              · refine Measurable.prodMk ?_ ?_
                · exact hhatG
                · refine Measurable.prodMk ?_ ?_
                  · exact hhatG
                  · refine Measurable.prodMk ?_ ?_
                    · exact hresids0
                    · refine Measurable.prodMk ?_ ?_
                      · exact hfailed0
                      · refine Measurable.prodMk ?_ ?_
                        · exact hdone
                        · exact hcorePhase0

end BlockMeas

/-- `enter` is measurable. -/
theorem block_enter_meas {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Measurable (clearingBlock (d := d) (m := m) n₀ j u x).enter := by
  have h : (clearingBlock (d := d) (m := m) n₀ j u x).enter =
      fun rec => (rec, clearInitScratch (d := d) (m := m) j u x rec) := rfl
  rw [h]
  exact measurable_id.prodMk (initScratch_meas j u x)

/-- FAIL exit is measurable (into `RunRecord` via its code). -/
theorem failExit_meas {d m : ℕ} (j : ℕ) (x : Torus d m) :
    Measurable (fun s : RunRecord d m × ClearScratch d m =>
      clearingFailExit (d := d) (m := m) j x s.1 s.2) := by
  classical
  refine measurable_comap_iff.mpr ?_
  -- pending indicator gains core ∪ inspected; latest relabels there
  have hpend_ind : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode (s.1.pending ∪ s.2.core ∪ s.2.inspected)) := by
    apply Measurable.of_eval
    intro y
    have hmemP : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending} := by
      have : {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending}
          = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.pending y) ⁻¹' {true} := by
        ext s
        simp [finsetCode]
      rw [this]
      exact ((measurable_pi_apply y).comp meas_rec_pending_ind)
        (measurableSet_singleton true)
    have hmemI : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected} := by
      have : {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected}
          = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.2.inspected y) ⁻¹' {true} := by
        ext s
        simp [finsetCode]
      rw [this]
      exact ((measurable_pi_apply y).comp meas_inspected_ind)
        (measurableSet_singleton true)
    refine measurable_of_singleton_fibers fun b => ?_
    cases b with
    | true =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.1.pending ∪ s.2.core ∪ s.2.inspected) y) ⁻¹' {true}
          = {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected} := by
        ext s
        by_cases hP : y ∈ s.1.pending <;> by_cases hC : y ∈ s.2.core <;>
          by_cases hI : y ∈ s.2.inspected <;> simp_all [finsetCode]
      rw [heq]
      exact (hmemP.union (measSet_core_mem y)).union hmemI
    | false =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.1.pending ∪ s.2.core ∪ s.2.inspected) y) ⁻¹' {false}
          = (({s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected}))ᶜ := by
        ext s
        by_cases hP : y ∈ s.1.pending <;> by_cases hC : y ∈ s.2.core <;>
          by_cases hI : y ∈ s.2.inspected <;> simp_all [finsetCode]
      rw [heq]
      exact ((hmemP.union (measSet_core_mem y)).union hmemI).compl
  -- relabelled latest codes
  have hlatest : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (fun y => labelCode ((clearingFailExit (d := d) (m := m) j x s.1 s.2).latest y))) := by
    apply Measurable.of_eval
    intro y
    have hset : MeasurableSet {s : RunRecord d m × ClearScratch d m |
        y ∈ s.2.core ∪ s.2.inspected} := by
      have heq : {s : RunRecord d m × ClearScratch d m |
          y ∈ s.2.core ∪ s.2.inspected}
          = {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected} := by
        ext s
        simp [Finset.mem_union]
      rw [heq]
      exact (measSet_core_mem y).union (measSet_inspected_mem y)
    have hconst : Measurable (fun _ : RunRecord d m × ClearScratch d m =>
        labelCode (⟨j, BirthType.clearing, x⟩ : BirthLabel (Torus d m))) :=
      measurable_const
    have hprev : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        labelCode (s.1.latest y)) :=
      (measurable_pi_apply y).comp meas_rec_latest
    have heq : (fun s : RunRecord d m × ClearScratch d m =>
          labelCode ((clearingFailExit (d := d) (m := m) j x s.1 s.2).latest y))
        = (fun s : RunRecord d m × ClearScratch d m =>
          if y ∈ s.2.core ∪ s.2.inspected then
            labelCode (⟨j, BirthType.clearing, x⟩ : BirthLabel (Torus d m))
          else labelCode (s.1.latest y)) := by
      funext s
      by_cases h : y ∈ s.2.core ∨ y ∈ s.2.inspected <;> simp [h, clearingFailExit]
    rw [heq]
    exact Measurable.ite hset hconst hprev
  -- unchanged record coordinates (projections of `hcode`; `failExit`
  -- keeps every other field, so leaves match by definition).
  -- Tuple parts stay whole (no expansion); only the changed status
  -- fields (pending/latest) split out.
  have hcode : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      RunRecord.code s.1) :=
    (RunRecord.measurable_code _ _).comp measurable_fst
  -- assemble by splitting the code tuple (leaves match by definition)
  refine Measurable.prodMk ?_ ?_
  · exact meas_stage
  · refine Measurable.prodMk ?_ ?_
    · exact (measurable_fst.comp (measurable_snd.comp hcode))
    · refine Measurable.prodMk ?_ ?_
      · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcode)))
      · refine Measurable.prodMk ?_ ?_
        · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
            (measurable_snd.comp hcode))))
        · refine Measurable.prodMk ?_ ?_
          · refine Measurable.prodMk ?_ ?_
            · exact meas_rec_terminal_ind
            · refine Measurable.prodMk ?_ ?_
              · exact hpend_ind
              · exact hlatest
          · refine Measurable.prodMk ?_ ?_
            · exact meas_rec_components_ind
            · exact meas_aborted

/-- DONE exit is measurable. -/
theorem doneExit_meas {d m : ℕ} :
    Measurable (fun s : RunRecord d m × ClearScratch d m =>
      clearingDoneExit (d := d) (m := m) s.1 s.2) := by
  classical
  refine measurable_comap_iff.mpr ?_
  have hcode : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      RunRecord.code s.1) :=
    (RunRecord.measurable_code _ _).comp measurable_fst
  -- changed endpoint active: scratch active minus core
  have hactive_ind : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode (s.2.active \ s.2.core)) := by
    apply Measurable.of_eval
    intro y
    refine measurable_of_singleton_fibers fun b => ?_
    cases b with
    | true =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.2.active \ s.2.core) y) ⁻¹' {true}
          = {s : RunRecord d m × ClearScratch d m | y ∈ s.2.active} ∩
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core}ᶜ := by
        ext s
        simp [finsetCode]
      rw [heq]
      exact (measSet_active_mem y).inter (measSet_core_mem y).compl
    | false =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.2.active \ s.2.core) y) ⁻¹' {false}
          = (({s : RunRecord d m × ClearScratch d m | y ∈ s.2.active} ∩
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core}ᶜ))ᶜ := by
        ext s
        simp [finsetCode]
      rw [heq]
      exact ((measSet_active_mem y).inter (measSet_core_mem y).compl).compl
  -- changed endpoint matrix/inverse from scratch
  have hM : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (s.2.Mnum.map Complex.ofReal : Matrix (Torus d m) (Torus d m) ℂ)) := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    -- per-entry via ofReal of Mnum eval
    have hmeas : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        Complex.ofReal (s.2.Mnum i j)) :=
      Complex.continuous_ofReal.measurable.comp (meas_Mnum_eval i j)
    simpa [Matrix.map_apply] using hmeas
  have hg : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (fun i k => if i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core then s.2.hatG i k
        else 0)) := by
    refine Measurable.of_eval_matrix _ fun i k => ?_
    have hset : MeasurableSet {s : RunRecord d m × ClearScratch d m |
        i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core} := by
      have hmem : ∀ y : Torus d m, MeasurableSet
          {s : RunRecord d m × ClearScratch d m | y ∈ s.2.active \ s.2.core} := by
        intro y
        have : {s : RunRecord d m × ClearScratch d m | y ∈ s.2.active \ s.2.core}
            = {s : RunRecord d m × ClearScratch d m | y ∈ s.2.active} ∩
              {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core}ᶜ := by
          ext s
          simp [Finset.mem_sdiff]
        rw [this]
        exact (measSet_active_mem y).inter (measSet_core_mem y).compl
      have : {s : RunRecord d m × ClearScratch d m |
          i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core}
          = {s : RunRecord d m × ClearScratch d m | i ∈ s.2.active \ s.2.core} ∩
            {s : RunRecord d m × ClearScratch d m | k ∈ s.2.active \ s.2.core} := rfl
      rw [this]
      exact (hmem i).inter (hmem k)
    have hpos : Measurable (fun s : RunRecord d m × ClearScratch d m => s.2.hatG i k) :=
      meas_hatG_eval i k
    have hzero : Measurable (fun _ : RunRecord d m × ClearScratch d m => (0 : ℂ)) :=
      measurable_const
    have heq : (fun s : RunRecord d m × ClearScratch d m =>
          (if i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core then s.2.hatG i k
            else 0))
        = (fun s : RunRecord d m × ClearScratch d m =>
          if i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core then s.2.hatG i k
            else 0) := rfl
    rw [heq]
    -- ite on a measurable set (as a function of `s`)
    have hite : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        if i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core then s.2.hatG i k
          else (0 : ℂ)) := by
      classical
      rw [show (fun s : RunRecord d m × ClearScratch d m =>
          if i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core then s.2.hatG i k
            else (0 : ℂ))
          = Set.piecewise {s : RunRecord d m × ClearScratch d m |
            i ∈ s.2.active \ s.2.core ∧ k ∈ s.2.active \ s.2.core}
            (fun s : RunRecord d m × ClearScratch d m => s.2.hatG i k)
            (fun _ : RunRecord d m × ClearScratch d m => (0 : ℂ)) from rfl]
      exact Measurable.piecewise hset hpos hzero
    exact hite
  -- changed terminal (union) and pending (diff)
  have hterm_ind : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode (s.1.terminal ∪ s.2.core ∪ s.2.inspected)) := by
    apply Measurable.of_eval
    intro y
    refine measurable_of_singleton_fibers fun b => ?_
    cases b with
    | true =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.1.terminal ∪ s.2.core ∪ s.2.inspected) y) ⁻¹' {true}
          = ({s : RunRecord d m × ClearScratch d m | y ∈ s.1.terminal} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected}) := by
        ext s
        by_cases hT : y ∈ s.1.terminal <;> by_cases hC : y ∈ s.2.core <;>
          by_cases hI : y ∈ s.2.inspected <;> simp_all [finsetCode]
      rw [heq]
      have hT : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.1.terminal} := by
        have : {s : RunRecord d m × ClearScratch d m | y ∈ s.1.terminal}
            = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.terminal y) ⁻¹' {true} := by
          ext s
          simp [finsetCode]
        rw [this]
        exact ((measurable_pi_apply y).comp meas_rec_terminal_ind)
          (measurableSet_singleton true)
      have hI : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected} :=
        measSet_inspected_mem y
      exact (hT.union (measSet_core_mem y)).union hI
    | false =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.1.terminal ∪ s.2.core ∪ s.2.inspected) y) ⁻¹' {false}
          = (({s : RunRecord d m × ClearScratch d m | y ∈ s.1.terminal} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected}))ᶜ := by
        ext s
        by_cases hT : y ∈ s.1.terminal <;> by_cases hC : y ∈ s.2.core <;>
          by_cases hI : y ∈ s.2.inspected <;> simp_all [finsetCode]
      rw [heq]
      have hT : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.1.terminal} := by
        have : {s : RunRecord d m × ClearScratch d m | y ∈ s.1.terminal}
            = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.terminal y) ⁻¹' {true} := by
          ext s
          simp [finsetCode]
        rw [this]
        exact ((measurable_pi_apply y).comp meas_rec_terminal_ind)
          (measurableSet_singleton true)
      have hI : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected} :=
        measSet_inspected_mem y
      exact ((hT.union (measSet_core_mem y)).union hI).compl
  -- changed pending (diff) and installed (completion)
  have hpend_diff : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      finsetCode (s.1.pending \ (s.2.core ∪ s.2.inspected))) := by
    apply Measurable.of_eval
    intro y
    refine measurable_of_singleton_fibers fun b => ?_
    cases b with
    | true =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.1.pending \ (s.2.core ∪ s.2.inspected)) y) ⁻¹' {true}
          = {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending} ∩
            ({s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
              {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected})ᶜ := by
        ext s
        simp [finsetCode]
      rw [heq]
      have hmemP : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending} := by
        have : {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending}
            = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.pending y) ⁻¹' {true} := by
          ext s
          simp [finsetCode]
        rw [this]
        exact ((measurable_pi_apply y).comp meas_rec_pending_ind)
          (measurableSet_singleton true)
      exact hmemP.inter
        ((measSet_core_mem y).union (measSet_inspected_mem y)).compl
    | false =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
            finsetCode (s.1.pending \ (s.2.core ∪ s.2.inspected)) y) ⁻¹' {false}
          = ({s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending} ∩
            ({s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
              {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected})ᶜ)ᶜ := by
        ext s
        simp [finsetCode]
      rw [heq]
      have hmemP : MeasurableSet {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending} := by
        have : {s : RunRecord d m × ClearScratch d m | y ∈ s.1.pending}
            = (fun s : RunRecord d m × ClearScratch d m => finsetCode s.1.pending y) ⁻¹' {true} := by
          ext s
          simp [finsetCode]
        rw [this]
        exact ((measurable_pi_apply y).comp meas_rec_pending_ind)
          (measurableSet_singleton true)
      exact ((hmemP.inter
        ((measSet_core_mem y).union (measSet_inspected_mem y)).compl)).compl
  have hinstalled : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (fun y => if y ∈ s.2.core ∪ s.2.inspected then s.1.installed y + s.2.resids y
        else s.1.installed y)) := by
    apply Measurable.of_eval
    intro y
    have hset : MeasurableSet {s : RunRecord d m × ClearScratch d m |
        y ∈ s.2.core ∪ s.2.inspected} := by
      have heq : {s : RunRecord d m × ClearScratch d m |
          y ∈ s.2.core ∪ s.2.inspected}
          = {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core} ∪
            {s : RunRecord d m × ClearScratch d m | y ∈ s.2.inspected} := by
        ext s
        simp [Finset.mem_union]
      rw [heq]
      exact (measSet_core_mem y).union (measSet_inspected_mem y)
    have hplus : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        s.1.installed y + s.2.resids y) :=
      ((measurable_pi_apply y).comp meas_rec_installed).add
        ((measurable_pi_apply y).comp meas_resids)
    have hkeep : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        s.1.installed y) :=
      (measurable_pi_apply y).comp meas_rec_installed
    have heq : (fun s : RunRecord d m × ClearScratch d m =>
          (if y ∈ s.2.core ∪ s.2.inspected then s.1.installed y + s.2.resids y
            else s.1.installed y))
        = (fun s : RunRecord d m × ClearScratch d m =>
          if y ∈ s.2.core ∪ s.2.inspected then s.1.installed y + s.2.resids y
            else s.1.installed y) := rfl
    rw [heq]
    -- ite on a measurable set with measurable branches (as a function of s)
    have hite : Measurable (fun s : RunRecord d m × ClearScratch d m =>
        if y ∈ s.2.core ∪ s.2.inspected then s.1.installed y + s.2.resids y
          else s.1.installed y) := by
      classical
      have hpiece : (fun s : RunRecord d m × ClearScratch d m =>
          if y ∈ s.2.core ∪ s.2.inspected then s.1.installed y + s.2.resids y
            else s.1.installed y)
          = Set.piecewise {s : RunRecord d m × ClearScratch d m |
            y ∈ s.2.core ∪ s.2.inspected}
            (fun s : RunRecord d m × ClearScratch d m =>
              s.1.installed y + s.2.resids y)
            (fun s : RunRecord d m × ClearScratch d m => s.1.installed y) := rfl
      rw [hpiece]
      exact Measurable.piecewise hset hplus hkeep
    exact hite
  -- assemble (mirroring `RunRecord.code`; changed: endpoint, terminal,
  -- pending, installed; rest from `hcode`)
  have hcode : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      RunRecord.code s.1) :=
    (RunRecord.measurable_code _ _).comp measurable_fst
  refine Measurable.prodMk ?_ ?_
  · exact measurable_fst.comp hcode
  · refine Measurable.prodMk ?_ ?_
    · refine Measurable.prodMk ?_ ?_
      · exact hactive_ind
      · refine Measurable.prodMk ?_ ?_
        · exact hM
        · refine Measurable.prodMk ?_ ?_
          · exact hg
          · exact meas_rec_r
    · refine Measurable.prodMk ?_ ?_
      · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcode)))
      · refine Measurable.prodMk ?_ ?_
        · refine Measurable.prodMk ?_ ?_
          · exact hinstalled
          · exact meas_rec_prefix
        · refine Measurable.prodMk ?_ ?_
          · refine Measurable.prodMk ?_ ?_
            · exact hterm_ind
            · refine Measurable.prodMk ?_ ?_
              · exact hpend_diff
              · exact meas_rec_latest
          · refine Measurable.prodMk ?_ ?_
            · exact meas_rec_components_ind
            · exact meas_aborted

/-- `exit` is measurable. -/
theorem block_exit_meas {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Measurable (clearingBlock (d := d) (m := m) n₀ j u x).exit := by
  classical
  have hexit : (clearingBlock (d := d) (m := m) n₀ j u x).exit =
      fun s : RunRecord d m × ClearScratch d m =>
        if s.1.aborted then s.1
        else if !decide (clearingScheduled j m) then s.1
        else if s.2.core = ∅ then s.1
        else if s.2.failed then clearingFailExit (d := d) (m := m) j x s.1 s.2
        else if s.2.done then clearingDoneExit (d := d) (m := m) s.1 s.2
        else s.1 := rfl
  rw [hexit]
  have haborted : MeasurableSet {s : RunRecord d m × ClearScratch d m | s.1.aborted = true} := by
    have : {s : RunRecord d m × ClearScratch d m | s.1.aborted = true}
        = (fun s : RunRecord d m × ClearScratch d m => s.1.aborted) ⁻¹' {true} := rfl
    rw [this]
    exact meas_aborted (measurableSet_singleton true)
  have hsched : MeasurableSet {s : RunRecord d m × ClearScratch d m |
      (!decide (clearingScheduled j m)) = true} := by
    by_cases hb : ((!decide (clearingScheduled j m)) = true)
    · have : {s : RunRecord d m × ClearScratch d m |
          (!decide (clearingScheduled j m)) = true} = Set.univ := by
        ext s
        simp [hb]
      rw [this]
      exact MeasurableSet.univ
    · have : {s : RunRecord d m × ClearScratch d m |
          (!decide (clearingScheduled j m)) = true} = ∅ := by
        ext s
        simp [hb]
      rw [this]
      exact MeasurableSet.empty
  have hcore_empty : MeasurableSet {s : RunRecord d m × ClearScratch d m | s.2.core = ∅} := by
    have : {s : RunRecord d m × ClearScratch d m | s.2.core = ∅}
        = ⋂ y, {s : RunRecord d m × ClearScratch d m | y ∈ s.2.core}ᶜ := by
      ext s
      simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
      exact Finset.eq_empty_iff_forall_notMem
    rw [this]
    exact MeasurableSet.iInter fun y => (measSet_core_mem y).compl
  have hfailed : MeasurableSet {s : RunRecord d m × ClearScratch d m | s.2.failed = true} :=
    meas_failed (measurableSet_singleton true)
  have hdone : MeasurableSet {s : RunRecord d m × ClearScratch d m | s.2.done = true} :=
    meas_done (measurableSet_singleton true)
  have hid : Measurable (fun s : RunRecord d m × ClearScratch d m => s.1) :=
    measurable_fst
  refine Measurable.ite haborted hid ?_
  refine Measurable.ite hsched hid ?_
  refine Measurable.ite hcore_empty hid ?_
  refine Measurable.ite hfailed ?_ ?_
  · exact failExit_meas j x
  · refine Measurable.ite hdone ?_ hid
    exact doneExit_meas

/-! ## Per-fiber action sets (shared by `next`/`update` measurability) -/

section ActSet
variable {d m : ℕ} {n₀ j : ℕ} {u : ℝ} {x : Torus d m}
variable (p : Finset (Torus d m) × Finset (Torus d m))

/-- Flag/coordinate conditions restricted to fiber `p`, via the subtype coe. -/
theorem fibSet_failed :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.failed = true} := by
  have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) => a.val.2.failed) :=
    meas_failed.comp measurable_subtype_coe
  have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.failed = true}
      = (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) => a.val.2.failed) ⁻¹' {true} :=
    rfl
  rw [this]
  exact hfn (measurableSet_singleton true)

/-- `done` flag on fiber. -/
theorem fibSet_done :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.done = true} := by
  have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) => a.val.2.done) :=
    meas_done.comp measurable_subtype_coe
  have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.done = true}
      = (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) => a.val.2.done) ⁻¹' {true} :=
    rfl
  rw [this]
  exact hfn (measurableSet_singleton true)

/-- `corePhase` flag on fiber. -/
theorem fibSet_corePhase :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.corePhase = true} := by
  have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) => a.val.2.corePhase) :=
    meas_corePhase.comp measurable_subtype_coe
  have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.corePhase = true}
      = (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) => a.val.2.corePhase) ⁻¹' {true} :=
    rfl
  rw [this]
  exact hfn (measurableSet_singleton true)

/-- Budgets on fiber (global set restricted via coe). -/
theorem fibSet_budgets :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      AndersonAC.S6.BudgetsHold (stageScale u j m) a.val.2.g0 a.val.2.hatG} := by
  have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      AndersonAC.S6.BudgetsHold (stageScale u j m) a.val.2.g0 a.val.2.hatG}
      = (Subtype.val : ↥(scratchFiber (d := d) (m := m) p.1 p.2) →
        RunRecord d m × ClearScratch d m) ⁻¹'
        {s : RunRecord d m × ClearScratch d m |
          AndersonAC.S6.BudgetsHold (stageScale u j m) s.2.g0 s.2.hatG} := rfl
  rw [this]
  exact measurable_subtype_coe (measSet_budgets _)

/-- Heat-limit step bound on fiber. -/
theorem fibSet_limit :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.step < AndersonAC.S6.heatLimit (stageScale u j m)} := by
  have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) => a.val.2.step) :=
    meas_step.comp measurable_subtype_coe
  exact measurableSet_lt hfn measurable_const

/-- Cap condition on fiber (via `fiber_maxWeight'`). -/
theorem fibSet_cap :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      AndersonAC.S6.maxWeight
        (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge)) ≤
        4 * AndersonAC.S6.leverageScale (stageScale u j m)} :=
  measurableSet_le
    (fiber_maxWeight' (A₀ := p.2) (B₀ := p.1) (stageScale u j m))
    measurable_const

/-- Cap-failure condition on fiber (strict, for the fail branch). -/
theorem fibSet_capFail :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      4 * AndersonAC.S6.leverageScale (stageScale u j m) <
        AndersonAC.S6.maxWeight
          (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge))} :=
  measurableSet_lt measurable_const
    (fiber_maxWeight' (A₀ := p.2) (B₀ := p.1) (stageScale u j m))

/-- Readiness on fiber (via `fiber_ready_set'`). -/
theorem fibSet_ready :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      xReady (stageScale u j m) (a.val.1.r) p.2
        (restrictM p.2 (a.val.2.Mnum)) p.1} :=
  fiber_ready_set' (A₀ := p.2) (B₀ := p.1) (stageScale u j m)

/-- Candidate pivot equals `some p₀` on fiber (via `leastMaximizer_eq_some`
and fiber weights). -/
theorem fibSet_candSome (p₀ : Torus d m) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) = some p₀} := by
  classical
  have hwt : ∀ i : Torus d m, Measurable
      (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
        scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge) i) :=
    fun i => fiber_weights_eval (A₀ := p.2) (B₀ := p.1) (stageScale u j m) i
  have hmaxW : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
      AndersonAC.S6.maxWeight
        (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge))) :=
    fiber_maxWeight' (A₀ := p.2) (B₀ := p.1) (stageScale u j m)
  have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) = some p₀}
      = {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge) p₀ =
            AndersonAC.S6.maxWeight
              (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge))} ∩
        ⋂ q, {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge) q =
            AndersonAC.S6.maxWeight
              (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge)) →
            (siteRank d m p₀).val ≤ (siteRank d m q).val} := by
    ext a
    simp [candPivot, leastMaximizer_eq_some]
  rw [heq]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun q => ?_)
  · exact measurableSet_eq_fun (hwt p₀) hmaxW
  · by_cases hord : (siteRank d m p₀).val ≤ (siteRank d m q).val
    · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge) q =
            AndersonAC.S6.maxWeight
              (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge)) →
            (siteRank d m p₀).val ≤ (siteRank d m q).val} = Set.univ := by
        ext a
        simp [hord]
      rw [this]
      exact MeasurableSet.univ
    · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge) q =
            AndersonAC.S6.maxWeight
              (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge)) →
            (siteRank d m p₀).val ≤ (siteRank d m q).val}
          = {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
            scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge) q =
              AndersonAC.S6.maxWeight
                (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge))}ᶜ := by
        ext a
        simp [hord]
      rw [this]
      exact (measurableSet_eq_fun (hwt q) hmaxW).compl

/-- Guard for pivot `p₀` on fiber (coupled/terminal via record
indicators restricted by coe; radius with fixed `B₀`). -/
theorem fibSet_guard (p₀ : Torus d m) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      guardHolds (d := d) (m := m) j p.1 (coupledActive a.val.1) a.val.1.terminal p₀} := by
  classical
  have hrad : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      ∃ y ∈ p.1, physicalDistance d m p₀ y ≤ inspectionRadius j / 2} := by
    by_cases h : ∃ y ∈ p.1, physicalDistance d m p₀ y ≤ inspectionRadius j / 2
    · simpa [h] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set ↥(scratchFiber (d := d) (m := m) p.1 p.2)))
    · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          ∃ y ∈ p.1, physicalDistance d m p₀ y ≤ inspectionRadius j / 2} = ∅ := by
        ext a
        simp [h]
      rw [this]
      exact MeasurableSet.empty
  have hact : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      p₀ ∈ a.val.1.endpoint.active} := by
    have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
        finsetCode a.val.1.endpoint.active p₀) :=
      (measurable_pi_apply p₀).comp
        (meas_rec_active_ind.comp measurable_subtype_coe)
    have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        p₀ ∈ a.val.1.endpoint.active}
        = (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
          finsetCode a.val.1.endpoint.active p₀) ⁻¹' {true} := by
      ext a
      simp [finsetCode]
    rw [this]
    exact hfn (measurableSet_singleton true)
  have hpend : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      p₀ ∈ a.val.1.pending} := by
    have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
        finsetCode a.val.1.pending p₀) :=
      (measurable_pi_apply p₀).comp
        (meas_rec_pending_ind.comp measurable_subtype_coe)
    have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        p₀ ∈ a.val.1.pending}
        = (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
          finsetCode a.val.1.pending p₀) ⁻¹' {true} := by
      ext a
      simp [finsetCode]
    rw [this]
    exact hfn (measurableSet_singleton true)
  have hterm : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      p₀ ∈ a.val.1.terminal} := by
    have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
        finsetCode a.val.1.terminal p₀) :=
      (measurable_pi_apply p₀).comp
        (meas_rec_terminal_ind.comp measurable_subtype_coe)
    have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        p₀ ∈ a.val.1.terminal}
        = (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
          finsetCode a.val.1.terminal p₀) ⁻¹' {true} := by
      ext a
      simp [finsetCode]
    rw [this]
    exact hfn (measurableSet_singleton true)
  have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      guardHolds (d := d) (m := m) j p.1 (coupledActive a.val.1) a.val.1.terminal p₀}
      = ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p₀ ∈ a.val.1.endpoint.active} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p₀ ∈ a.val.1.pending}ᶜ) ∩
        ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p₀ ∈ a.val.1.terminal}ᶜ ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          ∃ y ∈ p.1, physicalDistance d m p₀ y ≤ inspectionRadius j / 2}) := by
    ext a
    simp [guardHolds, coupledActive, Finset.mem_sdiff]
  rw [heq]
  exact (hact.inter hpend.compl).inter (hterm.compl.inter hrad)

/-- Pivot outside scratch core on fiber (constant, core `= p.1` there). -/
theorem fibSet_coreOut (p₀ : Torus d m) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p₀ ∉ a.val.2.core} := by
  by_cases h : p₀ ∈ p.1
  · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p₀ ∉ a.val.2.core} = ∅ := by
      ext a
      have hc : a.val.2.core = p.1 := a.property.1
      simp [hc, h]
    rw [this]
    exact MeasurableSet.empty
  · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p₀ ∉ a.val.2.core} = Set.univ := by
      ext a
      have hc : a.val.2.core = p.1 := a.property.1
      simp [hc, h]
    rw [this]
    exact MeasurableSet.univ

/-- Core-subset-active on fiber (constant). -/
theorem fibSet_subset :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p.1 ⊆ p.2} := by
  by_cases h : p.1 ⊆ p.2
  · simpa [h] using
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set ↥(scratchFiber (d := d) (m := m) p.1 p.2)))
  · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p.1 ⊆ p.2} = ∅ := by
      ext a
      simp [h]
    rw [this]
    exact MeasurableSet.empty

/-- CoreLeft membership on fiber (varying, via coordinates). -/
theorem fibSet_coreLeftMem (y : Torus d m) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | y ∈ a.val.2.coreLeft} := by
  have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
      finsetCode a.val.2.coreLeft y) :=
    (measurable_pi_apply y).comp
      (meas_coreLeft_ind.comp measurable_subtype_coe)
  have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | y ∈ a.val.2.coreLeft}
      = (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
        finsetCode a.val.2.coreLeft y) ⁻¹' {true} := by
    ext a
    simp [finsetCode]
  rw [this]
  exact hfn (measurableSet_singleton true)

/-- Prefix-length level on fiber (varying record coordinate). -/
theorem fibSet_prefixEq (y : Torus d m) (h : ℕ) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.1.prefixLength y = h} := by
  have hfn : Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) =>
      a.val.1.prefixLength y) :=
    (measurable_pi_apply y).comp
      (meas_rec_prefix.comp measurable_subtype_coe)
  exact hfn (measurableSet_singleton h)

/-- Core emptiness on fiber is constant (core `= p.1` there). -/
theorem fibSet_coreEmpty :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.core = ∅} := by
  by_cases h : p.1 = ∅
  · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.core = ∅} = Set.univ := by
      ext a
      have hc : a.val.2.core = p.1 := a.property.1
      simp [hc, h]
    rw [this]
    exact MeasurableSet.univ
  · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.core = ∅} = ∅ := by
      ext a
      have hc : a.val.2.core = p.1 := a.property.1
      simp [hc, h]
    rw [this]
    exact MeasurableSet.empty

/-- Heat action with pivot `p₀` on fiber (all `actionOf` heat conditions). -/
theorem fibSet_heat (p₀ : Torus d m) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      ∃ hg : guardHolds (d := d) (m := m) j a.val.2.core
        (coupledActive a.val.1) a.val.1.terminal p₀,
        actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
          ClearingAction.heat p₀ hg} := by
  classical
  -- condition sets (all measurable on this fiber)
  have hbool : ∀ (f : ↥(scratchFiber (d := d) (m := m) p.1 p.2) → Bool),
      Measurable f → ∀ b : Bool, MeasurableSet {a | f a = b} := by
    intro f hf b
    have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | f a = b} = f ⁻¹' {b} := rfl
    rw [this]
    exact hf (measurableSet_singleton b)
  have h1 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.failed = false} :=
    hbool _ (meas_failed.comp measurable_subtype_coe) false
  have h2 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.done = false} :=
    hbool _ (meas_done.comp measurable_subtype_coe) false
  have h4 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.corePhase = false} :=
    hbool _ (meas_corePhase.comp measurable_subtype_coe) false
  have h3c : MeasurableSet ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.core = ∅}ᶜ) :=
    (fibSet_coreEmpty (p := p)).compl
  have h5eq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.core ⊆ a.val.2.active} =
      {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p.1 ⊆ p.2} := by
    ext a
    rcases a with ⟨s, hs⟩
    simp only [Set.mem_setOf_eq]
    have hc : s.2.core = p.1 := hs.1
    have ha : s.2.active = p.2 := hs.2
    simp only [hc, ha]
  have h5 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.core ⊆ a.val.2.active} := by
    rw [h5eq]
    exact fibSet_subset (p := p)
  have h6 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      AndersonAC.S6.BudgetsHold (stageScale u j m) a.val.2.g0 a.val.2.hatG} :=
    fibSet_budgets (p := p)
  have h7 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.step < AndersonAC.S6.heatLimit (stageScale u j m)} :=
    fibSet_limit (p := p)
  have h8 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      AndersonAC.S6.maxWeight
        (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge)) ≤
        4 * AndersonAC.S6.leverageScale (stageScale u j m)} :=
    fibSet_cap (p := p)
  have h9eq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      ¬ xReady (stageScale u j m) (a.val.1.r) a.val.2.active
        (restrictM a.val.2.active a.val.2.Mnum) a.val.2.core} =
      ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        xReady (stageScale u j m) (a.val.1.r) p.2
          (restrictM p.2 (a.val.2.Mnum)) p.1}ᶜ) := by
    ext a
    rcases a with ⟨⟨rec, sc⟩, hs⟩
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    -- destructure the scratch state so `core`/`active` become variables for `subst`
    rcases sc with ⟨core, step, active, inspected, ridge, Mnum, hatG, g0, resids,
      failed, done, corePhase, coreLeft⟩
    obtain ⟨hc, ha⟩ := hs
    -- `hc : core = p.1`, `ha : active = p.2` with variables on the left; substitute
    subst hc
    subst ha
    exact Iff.rfl
    -- NOTE: after `subst`, both sides are `¬ xReady ... p.2 ... p.1`. The `subst`
    -- handles the dependent `restrictM`/`xCross` types (variable motive), unlike
    -- `rw` on projections.
  have h9 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      ¬ xReady (stageScale u j m) (a.val.1.r) a.val.2.active
        (restrictM a.val.2.active a.val.2.Mnum) a.val.2.core} := by
    rw [h9eq]
    exact (fibSet_ready (p := p)).compl
  have h10 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) = some p₀} :=
    fibSet_candSome (p := p) p₀
  have h11eq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      guardHolds (d := d) (m := m) j a.val.2.core
        (coupledActive a.val.1) a.val.1.terminal p₀} =
      {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      guardHolds (d := d) (m := m) j p.1 (coupledActive a.val.1) a.val.1.terminal p₀} := by
    ext a
    rcases a with ⟨s, hs⟩
    simp only [Set.mem_setOf_eq]
    have hc : s.2.core = p.1 := hs.1
    simp only [hc]
  have h11 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      guardHolds (d := d) (m := m) j a.val.2.core
        (coupledActive a.val.1) a.val.1.terminal p₀} := by
    rw [h11eq]
    exact fibSet_guard (p := p) p₀
  have h12 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      p₀ ∉ a.val.2.core} :=
    fibSet_coreOut (p := p) p₀
  -- the heat set is the intersection of the twelve conditions
  -- (all varying, matching `actionOf` directly; no fiber rewriting in `heq`)
  have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        ∃ hg : guardHolds (d := d) (m := m) j a.val.2.core
          (coupledActive a.val.1) a.val.1.terminal p₀,
          actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.heat p₀ hg}
      = {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.failed = false} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.done = false} ∩
        ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.core = ∅}ᶜ) ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.corePhase = false} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          a.val.2.core ⊆ a.val.2.active} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          AndersonAC.S6.BudgetsHold (stageScale u j m) a.val.2.g0 a.val.2.hatG} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          a.val.2.step < AndersonAC.S6.heatLimit (stageScale u j m)} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          AndersonAC.S6.maxWeight
            (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge)) ≤
            4 * AndersonAC.S6.leverageScale (stageScale u j m)} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          ¬ xReady (stageScale u j m) (a.val.1.r) a.val.2.active
            (restrictM a.val.2.active a.val.2.Mnum) a.val.2.core} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) = some p₀} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          guardHolds (d := d) (m := m) j a.val.2.core
            (coupledActive a.val.1) a.val.1.terminal p₀} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | p₀ ∉ a.val.2.core} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨hg, hact⟩
      -- each `if` of `actionOf` must have taken the heat branch (varying, no fiber)
      have hf : a.val.2.failed = false := by
        cases hff : a.val.2.failed with
        | true =>
          have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
              ClearingAction.fail (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) none := by
            unfold actionOf
            simp [hff]
          rw [this] at hact
          nomatch hact
        | false => rfl
      have hd : a.val.2.done = false := by
        cases hdd : a.val.2.done with
        | true =>
          have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
              ClearingAction.finish (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) := by
            unfold actionOf
            simp [hf, hdd]
          rw [this] at hact
          nomatch hact
        | false => rfl
      have hne : a.val.2.core ≠ ∅ := by
        intro hcon
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.finish (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2) := by
          unfold actionOf
          simp [hf, hd, hcon]
        rw [this] at hact
        nomatch hact
      have hph : a.val.2.corePhase = false := by
        cases hpp : a.val.2.corePhase with
        | true =>
          have hcon : (∃ y, actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
              ClearingAction.coreQuery (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) y hpp) ∨
              actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
              ClearingAction.finish (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) := by
            have hlist : (a.val.2.coreLeft.toList.mergeSort
                (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
                = none ∨ ∃ y, (a.val.2.coreLeft.toList.mergeSort
                (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? = some y := by
              cases h : (a.val.2.coreLeft.toList.mergeSort
                (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? with
              | none => exact Or.inl rfl
              | some y => exact Or.inr ⟨y, rfl⟩
            rcases hlist with hnone | ⟨y, hy⟩
            · refine Or.inr ?_
              simp only [actionOf, hf, hd, hne, hpp, hnone,
                if_true, if_false, if_pos, if_neg, dite_true, dite_false,
                reduceCtorEq]
            · refine Or.inl ⟨y, ?_⟩
              simp only [actionOf, hf, hd, hne, hpp, hy,
                if_true, if_false, if_pos, if_neg, dite_true, dite_false,
                reduceCtorEq]
          rcases hcon with ⟨y, hcon⟩ | hcon
          · rw [hcon] at hact
            nomatch hact
          · rw [hcon] at hact
            nomatch hact
        | false => rfl
      have hsub : a.val.2.core ⊆ a.val.2.active := by
        by_contra hcon
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.fail (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2) none := by
          unfold actionOf
          dsimp only
          simp [hf, hd, hne, hph, hcon]
        rw [this] at hact
        nomatch hact
      have hbud : AndersonAC.S6.BudgetsHold (stageScale u j m) a.val.2.g0 a.val.2.hatG := by
        by_contra hcon
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.fail (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2)
              (guardedCand j a.val.1 a.val.2
                (candPivot a.val.1.r a.val.2 (stageScale u j m) a.val.2.ridge)) := by
          unfold actionOf
          dsimp only
          simp [hf, hd, hne, hph, hsub, hcon]
        rw [this] at hact
        nomatch hact
      have hlim : a.val.2.step < AndersonAC.S6.heatLimit (stageScale u j m) := by
        by_contra hcon
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.fail (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2) none := by
          unfold actionOf
          dsimp only
          simp [hf, hd, hne, hph, hsub, hbud, hcon]
        rw [this] at hact
        nomatch hact
      have hcap : AndersonAC.S6.maxWeight
          (scratchWeights (stageScale u j m) (a.val.1.r) a.val.2 (a.val.2.ridge)) ≤
          4 * AndersonAC.S6.leverageScale (stageScale u j m) := by
        by_contra hcon
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.fail (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2)
              (guardedCand j a.val.1 a.val.2
                (candPivot a.val.1.r a.val.2 (stageScale u j m) a.val.2.ridge)) := by
          unfold actionOf
          dsimp only
          simp [hf, hd, hne, hph, hsub, hbud, hlim, hcon]
        rw [this] at hact
        nomatch hact
      have hnr : ¬ xReady (stageScale u j m) (a.val.1.r) a.val.2.active
          (restrictM a.val.2.active a.val.2.Mnum) a.val.2.core := by
        intro hready
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.coreReady (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2) := by
          unfold actionOf
          dsimp only
          simp [hf, hd, hne, hph, hsub, hbud, hlim, hcap, hready]
        rw [this] at hact
        nomatch hact
      have hcand : candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) = some p₀ := by
        have hmatch : (match candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) with
            | some pp =>
              (if hg' : guardHolds (d := d) (m := m) j a.val.2.core
                  (coupledActive a.val.1) a.val.1.terminal pp then
                (if pp ∈ a.val.2.core then
                  ClearingAction.fail (d := d) (m := m) (j := j)
                    (rc := a.val.1) (sc := a.val.2) (some pp)
                else ClearingAction.heat (d := d) (m := m) (j := j)
                  (rc := a.val.1) (sc := a.val.2) pp hg')
              else ClearingAction.fail (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) none)
            | none =>
              ClearingAction.coreReady (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2))
            = ClearingAction.heat (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) p₀ hg := by
          have hunfold : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
              (match candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) with
              | some pp =>
                (if hg' : guardHolds (d := d) (m := m) j a.val.2.core
                    (coupledActive a.val.1) a.val.1.terminal pp then
                  (if pp ∈ a.val.2.core then
                    ClearingAction.fail (d := d) (m := m) (j := j)
                      (rc := a.val.1) (sc := a.val.2) (some pp)
                  else ClearingAction.heat (d := d) (m := m) (j := j)
                    (rc := a.val.1) (sc := a.val.2) pp hg')
                else ClearingAction.fail (d := d) (m := m) (j := j)
                  (rc := a.val.1) (sc := a.val.2) none)
              | none =>
                ClearingAction.coreReady (d := d) (m := m) (j := j)
                  (rc := a.val.1) (sc := a.val.2)) := by
            unfold actionOf
            dsimp only
            simp [hf, hd, hne, hph, hsub, hbud, hlim, hcap, hnr]
          rw [hunfold] at hact
          exact hact
        cases hcc : candPivot (a.val.1.r) a.val.2 (stageScale u j m) (a.val.2.ridge) with
        | none =>
          rw [hcc] at hmatch
          nomatch hmatch
        | some pp =>
          rw [hcc] at hmatch
          by_cases hgpp : guardHolds (d := d) (m := m) j a.val.2.core
              (coupledActive a.val.1) a.val.1.terminal pp
          · by_cases hmem : pp ∈ a.val.2.core
            · simp [hgpp, hmem] at hmatch
            · simp [hgpp, hmem] at hmatch
              have hpp : pp = p₀ := by
                cases hmatch
                rfl
              -- goal here is `some pp = some p₀` (since `cases hcc` substituted
              -- the scrutinee); rewrite the goal, not `hcc`
              rw [hpp]
          · simp [hgpp] at hmatch
      have hguard : guardHolds (d := d) (m := m) j a.val.2.core
          (coupledActive a.val.1) a.val.1.terminal p₀ :=
        hg
      have hout : p₀ ∉ a.val.2.core := by
        intro hmem
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.fail (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2) (some p₀) := by
          unfold actionOf
          dsimp only
          simp [hf, hd, hne, hph, hsub, hbud, hlim, hcap, hnr, hcand, hg, hmem]
        rw [this] at hact
        nomatch hact
      -- package for the `ᶜ` form of the core-emptiness condition
      have hneC : a ∈ ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          a.val.2.core = ∅}ᶜ) := by
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        exact hne
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hd⟩, hneC⟩, hph⟩, hsub⟩, hbud⟩, hlim⟩, hcap⟩, hnr⟩, hcand⟩, hguard⟩, hout⟩
    · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hd⟩, hneC⟩, hph⟩, hsub⟩, hbud⟩, hlim⟩, hcap⟩, hnr⟩, hcand⟩, hguard⟩, hout⟩
      have hne : a.val.2.core ≠ ∅ := hneC
      refine ⟨hguard, ?_⟩
      unfold actionOf
      dsimp only
      simp [hf, hd, hne, hph, hsub, hbud, hlim, hcap, hnr, hcand, hguard, hout]
  rw [heq]
  exact ((((((((((h1.inter h2).inter h3c).inter h4).inter h5).inter h6).inter h7).inter h8).inter h9).inter h10).inter h11).inter h12

/-- CoreLeft value on fiber (finite Boolean combination of memberships). -/
theorem fibSet_coreLeftEq (C : Finset (Torus d m)) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.coreLeft = C} := by
  classical
  have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.coreLeft = C}
      = ⋂ y ∈ Finset.univ, {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        ((y ∈ a.val.2.coreLeft) ↔ (y ∈ C))} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ, true_and]
    constructor
    · intro h y _
      rw [h]
    · intro h
      exact Finset.ext fun y => h y trivial
  rw [heq]
  refine Finset.measurableSet_biInter _ fun y _ => ?_
  by_cases hy : y ∈ C
  · simpa [hy] using fibSet_coreLeftMem (p := p) y
  · have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        ((y ∈ a.val.2.coreLeft) ↔ (y ∈ C))}
        = {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          y ∈ a.val.2.coreLeft}ᶜ := by
      ext a
      simp [hy]
    rw [this]
    exact (fibSet_coreLeftMem (p := p) y).compl

/-- Core-query action with site `y` on fiber (flags + exact head computation).
`head? = some y` is captured exactly via the `coreLeft = C` fibers
(finite union over the decidable head predicate), avoiding any
rank-tie subtlety. -/
theorem fibSet_coreQuery (y : Torus d m) :
    MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      ∃ hy : a.val.2.corePhase = true,
        actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
          ClearingAction.coreQuery y hy} := by
  classical
  have hbool : ∀ (f : ↥(scratchFiber (d := d) (m := m) p.1 p.2) → Bool),
      Measurable f → ∀ b : Bool, MeasurableSet {a | f a = b} := by
    intro f hf b
    have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | f a = b} = f ⁻¹' {b} := rfl
    rw [this]
    exact hf (measurableSet_singleton b)
  have h1 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.failed = false} :=
    hbool _ (meas_failed.comp measurable_subtype_coe) false
  have h2 : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.done = false} :=
    hbool _ (meas_done.comp measurable_subtype_coe) false
  have h4T : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.corePhase = true} :=
    hbool _ (meas_corePhase.comp measurable_subtype_coe) true
  have h3c : MeasurableSet ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      a.val.2.core = ∅}ᶜ) :=
    (fibSet_coreEmpty (p := p)).compl
  have hhead : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
      (a.val.2.coreLeft.toList.mergeSort
        (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
        = some y} := by
    have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        (a.val.2.coreLeft.toList.mergeSort
          (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
          = some y}
        = ⋃ C ∈ Finset.univ.filter (fun C => decide
            ((C.toList.mergeSort
              (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
              = some y)),
          {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.coreLeft = C} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨a.val.2.coreLeft, by simpa using h, rfl⟩
      · rintro ⟨C, hCdec, hCeq⟩
        have hC : (C.toList.mergeSort
            (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
            = some y := of_decide_eq_true hCdec
        rw [hCeq, hC]
    rw [heq]
    refine Finset.measurableSet_biUnion _ fun C _ => ?_
    exact fibSet_coreLeftEq (p := p) C
  have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        ∃ hy : a.val.2.corePhase = true,
          actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.coreQuery y hy}
      = {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.failed = false} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.done = false} ∩
        ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.core = ∅}ᶜ) ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) | a.val.2.corePhase = true} ∩
        {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          (a.val.2.coreLeft.toList.mergeSort
            (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
            = some y} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨hy, hact⟩
      have hf : a.val.2.failed = false := by
        cases hff : a.val.2.failed with
        | true =>
          have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
              ClearingAction.fail (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) none := by
            unfold actionOf
            simp [hff]
          rw [this] at hact
          nomatch hact
        | false => rfl
      have hd : a.val.2.done = false := by
        cases hdd : a.val.2.done with
        | true =>
          have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
              ClearingAction.finish (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) := by
            unfold actionOf
            simp [hf, hdd]
          rw [this] at hact
          nomatch hact
        | false => rfl
      have hne : a.val.2.core ≠ ∅ := by
        intro hcon
        have : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            ClearingAction.finish (d := d) (m := m) (j := j)
              (rc := a.val.1) (sc := a.val.2) := by
          unfold actionOf
          simp [hf, hd, hcon]
        rw [this] at hact
        nomatch hact
      have hneC : a ∈ ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          a.val.2.core = ∅}ᶜ) := by
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        exact hne
      have hhead' : (a.val.2.coreLeft.toList.mergeSort
          (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
          = some y := by
        have hunfold : actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
            (match (a.val.2.coreLeft.toList.mergeSort
              (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? with
            | some y' => ClearingAction.coreQuery (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2) y' hy
            | none => ClearingAction.finish (d := d) (m := m) (j := j)
                (rc := a.val.1) (sc := a.val.2)) := by
          unfold actionOf
          dsimp only
          simp [hf, hd, hne, hy]
        rw [hunfold] at hact
        clear hunfold
        have hne' : (a.val.2.coreLeft.toList.mergeSort
            (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head?
            ≠ none := by
          intro hnone
          have h2 := hact
          rw [hnone] at h2
          dsimp only at h2
          nomatch h2
        obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists.mp hne'
        rw [←hy'] at hact
        dsimp only at hact
        cases hact
        exact hy'.symm
      exact ⟨⟨⟨⟨hf, hd⟩, hneC⟩, hy⟩, hhead'⟩
    · rintro ⟨⟨⟨⟨hf, hd⟩, hneC⟩, hyT⟩, hhead⟩
      have hne : a.val.2.core ≠ ∅ := hneC
      refine ⟨hyT, ?_⟩
      unfold actionOf
      dsimp only
      rw [hhead]
      simp [hf, hd, hne, hyT]
  rw [heq]
  exact (((h1.inter h2).inter h3c).inter h4T).inter hhead

end ActSet

/-! ## Update measurability: joint state/answer functions on a fiber.

On a fixed `(core, active)` fiber, every coordinate of `clearingUpdate`
is an explicit measurable function of `(state, answer)`: heat residuals
via `S2.binarySuffix_measurable` (fixed height) glued over prefix
heights, Schur data via rational matrix arithmetic plus the imported
inverse, ridges via `chooseRidge` exactly as in `fiber_ridge`, and the
post-step stop conditions by replicating `measSet_budgets` /
`fiber_maxWeight'` / `fiber_ready_set'` with the successor data.
Varying `core`/`active` occurrences are eliminated once per function
by congruence with the fixed-fiber form (destructured state, hence a
safe first-order rewrite). -/

section UpdateMeas
variable {d m : ℕ} {n₀ j : ℕ} {u : ℝ}
variable (p : Finset (Torus d m) × Finset (Torus d m))

/-- Sign values are measurable (countable domain). -/
theorem meas_signValue : Measurable AndersonAC.S2.signValue :=
  measurable_of_countable _

/-- Residual from an answer at fixed height, joint in state/answer. -/
theorem meas_resid_fixed (lam : ℝ) (y : Torus d m) (H : ℕ) :
    Measurable (fun q : (RunRecord d m × ClearScratch d m) × Answer (Torus d m) =>
      residOfAnswer (d := d) (m := m) lam y H q.2) := by
  classical
  have hdig : Measurable (fun q : (RunRecord d m × ClearScratch d m) × Answer (Torus d m) =>
      fun k : ℕ => ((q.2.1 (Sum.inl (y, k))).getD false)) := by
    apply Measurable.of_eval
    intro k
    exact (measurable_of_countable (fun o : Option Bool => o.getD false)).comp
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))
  have heq : (fun q : (RunRecord d m × ClearScratch d m) × Answer (Torus d m) =>
      residOfAnswer (d := d) (m := m) lam y H q.2)
      = fun q => AndersonAC.S2.binarySuffix lam H
        (fun k => ((q.2.1 (Sum.inl (y, k))).getD false)) := rfl
  rw [heq]
  exact (AndersonAC.S2.binarySuffix_measurable lam H).comp hdig

/-- Heat residual with varying prefix height, on a `(core, active)` fiber. -/
theorem meas_heatXi (p₀ : Torus d m) (lam : ℝ) :
    Measurable (fun a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      residOfAnswer (d := d) (m := m) lam p₀ (a.1.val.1.prefixLength p₀) a.2) := by
  classical
  apply Measurable.of_finite_fiber
    (fib := fun H : ℕ => {a : ↥(scratchFiber p.1 p.2) × Answer (Torus d m) |
      a.1.val.1.prefixLength p₀ = H})
  · intro a
    exact ⟨a.1.val.1.prefixLength p₀, rfl⟩
  · intro H
    have : {a : ↥(scratchFiber p.1 p.2) × Answer (Torus d m) |
        a.1.val.1.prefixLength p₀ = H}
        = (fun a : ↥(scratchFiber p.1 p.2) × Answer (Torus d m) => (a.1 : ↥(scratchFiber p.1 p.2))) ⁻¹'
          {a : ↥(scratchFiber p.1 p.2) | a.val.1.prefixLength p₀ = H} := rfl
    rw [this]
    exact measurable_fst (fibSet_prefixEq (p := p) p₀ H)
  · intro H
    have hfix : Measurable (fun a : ↥(scratchFiber p.1 p.2) × Answer (Torus d m) =>
        residOfAnswer (d := d) (m := m) lam p₀ H a.2) :=
      (meas_resid_fixed lam p₀ H).comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
    have heq : (fun a : ↥({a : ↥(scratchFiber p.1 p.2) × Answer (Torus d m) |
          a.1.val.1.prefixLength p₀ = H}) =>
          residOfAnswer (d := d) (m := m) lam p₀ (a.val.1.val.1.prefixLength p₀) a.val.2)
        = fun a => residOfAnswer (d := d) (m := m) lam p₀ H a.val.2 := by
      funext a
      have ha : a.val.1.val.1.prefixLength p₀ = H := a.property
      rw [ha]
    rw [heq]
    exact hfix.comp measurable_subtype_coe

/-- Schur-update entries with heat data (fixed pivot). -/
theorem meas_Mfull_eval (x₀ : Torus d m) (lam : ℝ) (i j : Torus d m) :
    Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
        (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2) i j) := by
  classical
  have hM : ∀ i j : Torus d m, Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      q.1.val.2.Mnum i j) := fun i j =>
    (meas_Mnum_eval i j).comp (fiber_coe_meas'.comp measurable_fst)
  have hXi : Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2) :=
    meas_heatXi (p := p) x₀ lam
  by_cases h : i = x₀ ∨ j = x₀
  · by_cases hij : i = j
    · have : (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
          schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2) i j)
          = fun _ => (1 : ℝ) := by
        funext q
        simp only [schurStepM, if_pos h, if_pos hij]
      rw [this]
      exact measurable_const
    · have : (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
          schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2) i j)
          = fun _ => (0 : ℝ) := by
        funext q
        simp only [schurStepM, if_pos h, if_neg hij]
      rw [this]
      exact measurable_const
  · have : (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
          schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2) i j)
        = (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
          q.1.val.2.Mnum i j - q.1.val.2.Mnum i x₀ * q.1.val.2.Mnum x₀ j
            * ((q.1.val.2.Mnum x₀ x₀ +
              residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2)⁻¹)) := by
      funext q
      simp only [schurStepM, if_neg h, div_eq_mul_inv]
    rw [this]
    exact ((hM i j).sub (((hM i x₀).mul (hM x₀ j)).mul (measurable_inv.comp ((hM x₀ x₀).add hXi))))

/-- Full-matrix successor is jointly measurable. -/
theorem meas_MfullF (x₀ : Torus d m) (lam : ℝ) :
    Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
        (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2)) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  exact meas_Mfull_eval (p := p) x₀ lam i j

/-- Restricted successor matrix is jointly measurable (fixed active set). -/
theorem meas_MsubF (x₀ : Torus d m) (lam : ℝ) :
    Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      restrictM (p.2.erase x₀)
        (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
          (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) := by
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [restrictM, Matrix.submatrix_apply]
  exact meas_Mfull_eval (p := p) x₀ lam a.val b.val

/-- Successor damping data as a measurable function. -/
theorem meas_rfF :
    Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      (fun i : Torus d m => q.1.val.1.r i)) := by
  apply Measurable.of_eval
  intro y
  exact ((measurable_pi_apply _).comp meas_rec_r).comp
    (fiber_coe_meas'.comp measurable_fst)

/-- Refreshed inverse entries with heat data (fixed active set). -/
theorem meas_hatGF_eval (x₀ : Torus d m) (lam t : ℝ) (i j : Torus d m) :
    Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      (if h : i ∈ p.2.erase x₀ ∧ j ∈ p.2.erase x₀ then
        AndersonAC.S6.activeInverse
          (restrictM (p.2.erase x₀)
            (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
              (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) t
          (fun i : {i // i ∈ p.2.erase x₀} => q.1.val.1.r i.val) ⟨i, h.1⟩ ⟨j, h.2⟩
      else q.1.val.2.hatG i j)) := by
  classical
  by_cases hmem : i ∈ p.2.erase x₀ ∧ j ∈ p.2.erase x₀
  · have hMsub : Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
        restrictM (p.2.erase x₀)
          (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) :=
      meas_MsubF (p := p) x₀ lam
    have hrf : Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
        (fun i : {i // i ∈ p.2.erase x₀} => q.1.val.1.r i.val)) := by
      apply Measurable.of_eval
      intro k
      exact ((measurable_pi_apply _).comp meas_rec_r).comp
        (fiber_coe_meas'.comp measurable_fst)
    have : (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
        (if h : i ∈ p.2.erase x₀ ∧ j ∈ p.2.erase x₀ then
          AndersonAC.S6.activeInverse
            (restrictM (p.2.erase x₀)
              (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
                (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) t
            (fun i : {i // i ∈ p.2.erase x₀} => q.1.val.1.r i.val) ⟨i, h.1⟩ ⟨j, h.2⟩
        else q.1.val.2.hatG i j))
        = fun q => AndersonAC.S6.activeInverse
          (restrictM (p.2.erase x₀)
            (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
              (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) t
          (fun i : {i // i ∈ p.2.erase x₀} => q.1.val.1.r i.val)
          ⟨i, hmem.1⟩ ⟨j, hmem.2⟩ := by
      funext q
      rw [dif_pos hmem]
    rw [this]
    exact tool_trialInverse_eval t hMsub hrf _ _
  · have : (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
        (if h : i ∈ p.2.erase x₀ ∧ j ∈ p.2.erase x₀ then
          AndersonAC.S6.activeInverse
            (restrictM (p.2.erase x₀)
              (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
                (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) t
          (fun i : {i // i ∈ p.2.erase x₀} => q.1.val.1.r i.val) ⟨i, h.1⟩ ⟨j, h.2⟩
        else q.1.val.2.hatG i j))
        = fun q => q.1.val.2.hatG i j := by
      funext q
      rw [dif_neg hmem]
    rw [this]
    exact (meas_hatG_eval i j).comp (fiber_coe_meas'.comp measurable_fst)

/-- Successor cross matrix with heat data (fixed sets, opaque for reuse). -/
theorem meas_sc1cross_joint (x₀ : Torus d m) (lam t : ℝ) :
    Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      xCross t (fun i => q.1.val.1.r i) (p.2.erase x₀)
        (restrictM (p.2.erase x₀)
          (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) p.1) := by
  have hMf : Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
        (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2)) :=
    meas_MfullF (p := p) x₀ lam
  have hrf : Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      (fun i : Torus d m => q.1.val.1.r i)) :=
    meas_rfF (p := p)
  refine Measurable.of_eval_matrix _ fun xb yb => ?_
  exact tool_xcross_eval t hrf hMf xb yb

/-- Successor weights at fixed ridge with heat data. -/
theorem meas_sc1weights_fixed_eval (x₀ : Torus d m) (lam t τ : ℝ) (i : Torus d m) :
    Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      AndersonAC.S6.leverage
        (xCross t (fun i => q.1.val.1.r i) (p.2.erase x₀)
          (restrictM (p.2.erase x₀)
            (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
              (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) p.1) τ i) := by
  have hcross_joint : Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      xCross t (fun i => q.1.val.1.r i) (p.2.erase x₀)
        (restrictM (p.2.erase x₀)
          (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) p.1) :=
    meas_sc1cross_joint (p := p) x₀ lam t
  have hpair : Measurable (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      ((xCross t (fun i => q.1.val.1.r i) (p.2.erase x₀)
        (restrictM (p.2.erase x₀)
          (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) p.1), τ)) :=
    hcross_joint.prodMk measurable_const
  have hlev : Measurable (fun q' : Matrix (Torus d m) {b // b ∈ p.1} ℂ × ℝ =>
      AndersonAC.S6.leverage q'.1 q'.2 i) :=
    AndersonAC.AgentS6.measurable_leverage i
  have hcomp : Measurable ((fun q' : Matrix (Torus d m) {b // b ∈ p.1} ℂ × ℝ =>
      AndersonAC.S6.leverage q'.1 q'.2 i) ∘
    (fun q : ↥(scratchFiber (d := d) (m := m) p.1 p.2) × Answer (Torus d m) =>
      ((xCross t (fun i => q.1.val.1.r i) (p.2.erase x₀)
        (restrictM (p.2.erase x₀)
          (schurStepM (d := d) (m := m) q.1.val.2.Mnum x₀
            (residOfAnswer (d := d) (m := m) lam x₀ (q.1.val.1.prefixLength x₀) q.2))) p.1), τ))) :=
    hlev.comp hpair
  exact hcomp

/-- `chooseRidge` is the identity when the lowering threshold is non-positive
(small-terms helper, so successor-ridge proofs avoid unfolding the huge
successor cross matrix inline). -/
theorem chooseRidge_eq_self_of_not_pos {R B : Type*} [Fintype R] [Fintype B]
    (C : Matrix R B ℂ) (l τ : ℝ) (hl : ¬ 0 < l) :
    AndersonAC.S6.chooseRidge C l τ = τ := by
  simp only [AndersonAC.S6.chooseRidge]
  have hfalse : ¬ AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C
      τ) < 2 * l := by
    intro hcon
    have hnn := maxWeight_nonneg (AndersonAC.S6.leverage C τ)
    have hle : l ≤ 0 := le_of_not_gt hl
    linarith
  rw [if_neg hfalse]

/- Successor ridge/maxWeight: see `upd_meas_reridge` / `upd_meas_post` below
(state maps glued over the `(core, active)` key). -/

end UpdateMeas

/-- `next` is measurable (double-fiber glue; on each fiber it is an
ite-chain on measurable conditions with constant queries). -/
theorem block_next_meas {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Measurable (clearingBlock (d := d) (m := m) n₀ j u x).next := by
  classical
  have hnext_eq : (clearingBlock (d := d) (m := m) n₀ j u x).next =
      clearingNext (d := d) (m := m) n₀ j u := rfl
  rw [hnext_eq]
  apply Measurable.of_finite_fiber
    (fib := fun p : Finset (Torus d m) × Finset (Torus d m) => scratchFiber p.1 p.2)
  · intro s
    exact ⟨(s.2.core, s.2.active), rfl, rfl⟩
  · intro p
    exact measSet_scratchFiber p.1 p.2
  · intro p
    -- per-fiber `next` via singleton fibers on `Query` (countable);
    -- order/aux queries never occur, so those fibers are empty.
    have hord : ∀ o : ℕ, MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        clearingNext (d := d) (m := m) n₀ j u a.val = Query.nextOrder o} := by
      intro o
      have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          clearingNext (d := d) (m := m) n₀ j u a.val = Query.nextOrder o} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hcon
        exact absurd hcon (clearing_next_ne_order n₀ j u _ o)
      rw [this]
      exact MeasurableSet.empty
    have haux : ∀ a_ : ℕ, MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        clearingNext (d := d) (m := m) n₀ j u a.val = Query.auxiliary a_} := by
      intro a_
      have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          clearingNext (d := d) (m := m) n₀ j u a.val = Query.auxiliary a_} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hcon
        exact absurd hcon (clearing_next_ne_aux n₀ j u _ a_)
      rw [this]
      exact MeasurableSet.empty
    have hdig : ∀ i k, MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        clearingNext (d := d) (m := m) n₀ j u a.val = Query.trueDigit i k} := by
      intro i k
      have : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
          clearingNext (d := d) (m := m) n₀ j u a.val = Query.trueDigit i k} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hcon
        exact absurd hcon (clearing_next_ne_digit n₀ j u _ i k)
      rw [this]
      exact MeasurableSet.empty
    -- trueSuffix fibers: heat pivot (at its prefix height) or core query (at height 0).
    have hts : ∀ y h, MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        clearingNext (d := d) (m := m) n₀ j u a.val = Query.trueSuffix y h} := by
      intro y h
      have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
            clearingNext (d := d) (m := m) n₀ j u a.val = Query.trueSuffix y h}
          = ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
              ∃ hg : guardHolds (d := d) (m := m) j a.val.2.core
                (coupledActive a.val.1) a.val.1.terminal y,
                actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
                  ClearingAction.heat y hg}
              ∩ {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
                a.val.1.prefixLength y = h})
            ∪ ({a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
              ∃ hy : a.val.2.corePhase = true,
                actionOf (d := d) (m := m) j u a.val.1 a.val.2 =
                  ClearingAction.coreQuery y hy}
              ∩ {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
                h = 0}) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union]
        constructor
        · intro hcon
          cases hact : actionOf (d := d) (m := m) j u a.val.1 a.val.2 with
          | fail po => simp [clearingNext, hact] at hcon
          | coreReady => simp [clearingNext, hact] at hcon
          | heat p hg =>
            simp only [clearingNext, hact] at hcon
            have hpy : p = y := by injection hcon
            have hph : a.val.1.prefixLength p = h := by injection hcon
            rw [←hpy]
            exact Or.inl ⟨⟨hg, rfl⟩, hph⟩
          | coreQuery z hz =>
            simp only [clearingNext, hact] at hcon
            have hzy : z = y := by injection hcon
            have hz0 : (0 : ℕ) = h := by injection hcon
            rw [←hzy]
            exact Or.inr ⟨⟨hz, rfl⟩, hz0.symm⟩
          | finish => simp [clearingNext, hact] at hcon
        · rintro (⟨⟨hg, hact⟩, hph⟩ | ⟨⟨hy, hact2⟩, hh0⟩)
          · have hq : clearingNext (d := d) (m := m) n₀ j u a.val =
                Query.trueSuffix y (a.val.1.prefixLength y) := by
              simp [clearingNext, hact]
            rw [hq, hph]
          · have hq : clearingNext (d := d) (m := m) n₀ j u a.val =
                Query.trueSuffix y 0 := by
              simp [clearingNext, hact2]
            rw [hq, hh0]
      rw [heq]
      refine MeasurableSet.union ?_ ?_
      · exact (fibSet_heat (p := p) y).inter (fibSet_prefixEq (p := p) y h)
      · refine (fibSet_coreQuery (p := p) y).inter ?_
        by_cases hh0 : h = 0
        · simpa [hh0] using MeasurableSet.univ
        · simpa [hh0] using MeasurableSet.empty
    -- decision fiber: complement of the countable trueSuffix union.
    have hdec : MeasurableSet {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
        clearingNext (d := d) (m := m) n₀ j u a.val = Query.decision} := by
      have heq : {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
            clearingNext (d := d) (m := m) n₀ j u a.val = Query.decision}
          = (⋃ y, ⋃ h, {a : ↥(scratchFiber (d := d) (m := m) p.1 p.2) |
            clearingNext (d := d) (m := m) n₀ j u a.val = Query.trueSuffix y h})ᶜ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion]
        constructor
        · intro hcon H
          obtain ⟨y, h, hyh⟩ := H
          rw [hcon] at hyh
          nomatch hyh
        · intro hcon
          cases hact : actionOf (d := d) (m := m) j u a.val.1 a.val.2 with
          | fail po => simp [clearingNext, hact]
          | coreReady => simp [clearingNext, hact]
          | heat p hg =>
            have hq : clearingNext (d := d) (m := m) n₀ j u a.val =
                Query.trueSuffix p (a.val.1.prefixLength p) := by
              simp [clearingNext, hact]
            exact (hcon ⟨p, _, hq⟩).elim
          | coreQuery z hz =>
            have hq : clearingNext (d := d) (m := m) n₀ j u a.val =
                Query.trueSuffix z 0 := by
              simp [clearingNext, hact]
            exact (hcon ⟨z, 0, hq⟩).elim
          | finish => simp [clearingNext, hact]
      rw [heq]
      refine MeasurableSet.compl ?_
      refine MeasurableSet.iUnion fun y => ?_
      refine MeasurableSet.iUnion fun h => ?_
      exact hts y h
    -- glue over countable `Query` via singleton fibers.
    haveI : Countable (Query (Torus d m)) := by
      classical
      refine Function.Injective.countable (f := fun q : Query (Torus d m) =>
        (match q with
        | .trueDigit i k => Sum.inl (i, k)
        | .auxiliary k => Sum.inr (Sum.inl k)
        | .trueSuffix i h => Sum.inr (Sum.inr (Sum.inl (i, h)))
        | .nextOrder o => Sum.inr (Sum.inr (Sum.inr (Sum.inl o)))
        | .decision => Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))) :
        (Torus d m × ℕ) ⊕ ℕ ⊕ (Torus d m × ℕ) ⊕ ℕ ⊕ Unit)) ?_
      intro a b h
      cases a <;> cases b <;> simp_all
    refine measurable_of_singleton_fibers fun q => ?_
    cases q with
    | trueDigit i k => exact hdig i k
    | auxiliary a_ => exact haux a_
    | trueSuffix y h => exact hts y h
    | nextOrder o => exact hord o
    | decision => exact hdec

/-! ## Update measurability (`clearingBlock_measurable`, `update` field)

The update is written as `updByKind (updKindU s) (s, ans)`: a countable
action key (`ClearKind`, measurable in the state) selects one of six
branch maps, each measurable on the whole state/answer space. Every
dependence on the scratch `core`/`active` sets as index types is
isolated in a state map `St → St` (`updRefresh`, `updReridge`,
`updPost`) or in `updKindBA`, and glued over the countable
`(core, active)` key (`upd_meas_coreActive`), so no subtype of the
state space is ever elaborated. -/

section UpdGlue
variable {d m : ℕ}

/-- Measurability through a countable key with measurable fibers. -/
theorem upd_measurable_of_key {α β K : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable K] {f : α → β} (key : α → K) (g : K → α → β)
    (hkey : ∀ k, MeasurableSet {a | key a = k}) (hg : ∀ k, Measurable (g k))
    (hfg : ∀ a, f a = g (key a) a) : Measurable f := by
  intro t ht
  have heq : f ⁻¹' t = ⋃ k, ({a | key a = k} ∩ g k ⁻¹' t) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨key a, rfl, by rw [← hfg]; exact h⟩
    · rintro ⟨k, rfl, h⟩
      rw [hfg]
      exact h
  rw [heq]
  exact MeasurableSet.iUnion fun k => (hkey k).inter (hg k ht)

/-- Set version of `upd_measurable_of_key`. -/
theorem upd_measurableSet_of_key {α K : Type*} [MeasurableSpace α] [Countable K]
    {P : α → Prop} (key : α → K) (Q : K → α → Prop)
    (hkey : ∀ k, MeasurableSet {a | key a = k}) (hQ : ∀ k, MeasurableSet {a | Q k a})
    (hPQ : ∀ a, P a ↔ Q (key a) a) : MeasurableSet {a | P a} := by
  have heq : {a | P a} = ⋃ k, ({a | key a = k} ∩ {a | Q k a}) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨key a, rfl, (hPQ a).1 h⟩
    · rintro ⟨k, rfl, h⟩
      exact (hPQ a).2 h
  rw [heq]
  exact MeasurableSet.iUnion fun k => (hkey k).inter (hQ k)

/-- Any function of two finset coordinates with measurable indicators is
measurable (the indicator space is finite). -/
theorem upd_meas_finset2 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f g : α → Finset (Torus d m)} (hf : Measurable fun a => finsetCode (f a))
    (hg : Measurable fun a => finsetCode (g a))
    (G : Finset (Torus d m) → Finset (Torus d m) → β) :
    Measurable (fun a => G (f a) (g a)) := by
  have hdec : ∀ s : Finset (Torus d m),
      Finset.univ.filter (fun y => finsetCode s y = true) = s := by
    intro s
    ext y
    simp [finsetCode]
  have h1 : Measurable (fun c : (Torus d m → Bool) × (Torus d m → Bool) =>
      G (Finset.univ.filter (fun y => c.1 y = true))
        (Finset.univ.filter (fun y => c.2 y = true))) :=
    measurable_of_countable _
  have heq : (fun a => G (f a) (g a)) =
      (fun c : (Torus d m → Bool) × (Torus d m → Bool) =>
        G (Finset.univ.filter (fun y => c.1 y = true))
          (Finset.univ.filter (fun y => c.2 y = true))) ∘
      (fun a => (finsetCode (f a), finsetCode (g a))) := by
    funext a
    simp only [Function.comp, hdec]
  rw [heq]
  exact h1.comp (hf.prodMk hg)

/-- Set version of `upd_meas_finset2`. -/
theorem upd_measSet_finset2 {α : Type*} [MeasurableSpace α]
    {f g : α → Finset (Torus d m)} (hf : Measurable fun a => finsetCode (f a))
    (hg : Measurable fun a => finsetCode (g a))
    (P : Finset (Torus d m) → Finset (Torus d m) → Prop) :
    MeasurableSet {a | P (f a) (g a)} := by
  have h := upd_meas_finset2 hf hg (fun B A => decide (P B A))
  have heq : {a | P (f a) (g a)} = (fun a => decide (P (f a) (g a))) ⁻¹' {true} := by
    ext a
    simp
  rw [heq]
  exact h (measurableSet_singleton true)

/-- Glue over the `(core, active)` key: measurable if measurable for each
fixed pair of sets. -/
theorem upd_meas_coreActive {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {c a : α → Finset (Torus d m)} (hc : Measurable fun x => finsetCode (c x))
    (ha : Measurable fun x => finsetCode (a x))
    (F : Finset (Torus d m) → Finset (Torus d m) → α → β)
    (hF : ∀ B A, Measurable (F B A)) :
    Measurable (fun x => F (c x) (a x) x) :=
  upd_measurable_of_key (fun x => (c x, a x)) (fun k => F k.1 k.2)
    (fun k => upd_measSet_finset2 hc ha (fun B A => (B, A) = k))
    (fun k => hF k.1 k.2) (fun _ => rfl)

/-- Set version of `upd_meas_coreActive`. -/
theorem upd_measSet_coreActive {α : Type*} [MeasurableSpace α]
    {c a : α → Finset (Torus d m)} (hc : Measurable fun x => finsetCode (c x))
    (ha : Measurable fun x => finsetCode (a x))
    (P : Finset (Torus d m) → Finset (Torus d m) → α → Prop)
    (hP : ∀ B A, MeasurableSet {x | P B A x}) :
    MeasurableSet {x | P (c x) (a x) x} :=
  upd_measurableSet_of_key (fun x => (c x, a x)) (fun k => P k.1 k.2)
    (fun k => upd_measSet_finset2 hc ha (fun B A => (B, A) = k))
    (fun k => hP k.1 k.2) (fun _ => Iff.rfl)

/-- Membership in a finset coordinate with measurable indicator. -/
theorem upd_measSet_mem {α : Type*} [MeasurableSpace α]
    {f : α → Finset (Torus d m)} (hf : Measurable fun a => finsetCode (f a))
    (y : Torus d m) : MeasurableSet {a | y ∈ f a} :=
  upd_measSet_finset2 hf hf (fun B _ => y ∈ B)

/-- A scratch state built from measurable coordinates is measurable. -/
theorem upd_meas_scratch_mk {α : Type*} [MeasurableSpace α]
    {core active inspected coreLeft : α → Finset (Torus d m)} {step : α → ℕ}
    {ridge : α → ℝ} {Mnum : α → Matrix (Torus d m) (Torus d m) ℝ}
    {hatG g0 : α → Matrix (Torus d m) (Torus d m) ℂ} {resids : α → Torus d m → ℝ}
    {failed done corePhase : α → Bool}
    (hcore : Measurable fun a => finsetCode (core a)) (hstep : Measurable step)
    (hactive : Measurable fun a => finsetCode (active a))
    (hinsp : Measurable fun a => finsetCode (inspected a)) (hridge : Measurable ridge)
    (hM : Measurable Mnum) (hG : Measurable hatG) (hg0 : Measurable g0)
    (hres : Measurable resids) (hf : Measurable failed) (hd : Measurable done)
    (hc : Measurable corePhase) (hleft : Measurable fun a => finsetCode (coreLeft a)) :
    Measurable (fun a => (⟨core a, step a, active a, inspected a, ridge a, Mnum a,
      hatG a, g0 a, resids a, failed a, done a, corePhase a, coreLeft a⟩ :
        ClearScratch d m)) := by
  refine measurable_comap_iff.mpr ?_
  exact hcore.prodMk (hactive.prodMk (hinsp.prodMk (hleft.prodMk (hstep.prodMk
    (hridge.prodMk (hM.prodMk (hG.prodMk (hg0.prodMk (hres.prodMk
      (hf.prodMk (hd.prodMk hc)))))))))))

end UpdGlue

/-! ### Fixed-set S6 quantities on any measurable space -/

section UpdS6
variable {d m : ℕ} {α : Type*} [MeasurableSpace α]

/-- Inlined cross matrix at fixed sets. -/
theorem upd_meas_cross (t : ℝ) (B A : Finset (Torus d m))
    {r : α → Torus d m → ℂ} {M : α → Matrix (Torus d m) (Torus d m) ℝ}
    (hr : Measurable r) (hM : Measurable M) :
    Measurable (fun x => xCross t (r x) A (restrictM A (M x)) B) := by
  refine Measurable.of_eval_matrix _ fun i b => ?_
  exact tool_xcross_eval (A₀ := A) (B₀ := B) t hr hM i b

/-- Leverage scores jointly in the matrix and the ridge. -/
theorem upd_meas_lev {Bt : Type*} [Fintype Bt] [DecidableEq Bt]
    {C : α → Matrix (Torus d m) Bt ℂ} {τ : α → ℝ}
    (hC : Measurable C) (hτ : Measurable τ) (i : Torus d m) :
    Measurable (fun x => AndersonAC.S6.leverage (C x) (τ x) i) := by
  have h1 : Measurable (fun p : Matrix (Torus d m) Bt ℂ × ℝ => AndersonAC.S6.leverage p.1 p.2 i) :=
    AndersonAC.AgentS6.measurable_leverage (R := Torus d m) (B := Bt) i
  have h2 : Measurable (fun x => (C x, τ x)) := hC.prodMk hτ
  have h3 := h1.comp h2
  exact h3

/-- Maximal leverage jointly in the matrix and the ridge. -/
theorem upd_meas_maxLev {Bt : Type*} [Fintype Bt] [DecidableEq Bt]
    {C : α → Matrix (Torus d m) Bt ℂ} {τ : α → ℝ}
    (hC : Measurable C) (hτ : Measurable τ) :
    Measurable (fun x => AndersonAC.S6.maxWeight (AndersonAC.S6.leverage (C x) (τ x))) :=
  measurable_maxWeight_of (fun i => upd_meas_lev hC hτ i)

/-- `chooseRidge` jointly in the matrix and the (varying) ridge `τ`; the
lowering test is at `τ` itself. -/
theorem upd_meas_chooseRidge {Bt : Type*} [Fintype Bt] [DecidableEq Bt]
    {C : α → Matrix (Torus d m) Bt ℂ} {τ : α → ℝ}
    (hC : Measurable C) (hτ : Measurable τ) (l : ℝ) :
    Measurable (fun x => AndersonAC.S6.chooseRidge (C x) l (τ x)) := by
  by_cases hl : 0 < l
  · unfold AndersonAC.S6.chooseRidge
    have hth0 : Measurable (fun C : Matrix (Torus d m) Bt ℂ => AndersonAC.S6.ridgeThreshold C l) :=
      (AndersonAC.S6.ridge_threshold_measurable (R := Torus d m) (B := Bt) l hl).1
    have hth := hth0.comp hC
    have hmax : Measurable (fun x =>
        AndersonAC.S6.maxWeight (AndersonAC.S6.leverage (C x) (τ x))) := upd_meas_maxLev hC hτ
    have hset : MeasurableSet {x | AndersonAC.S6.maxWeight
        (AndersonAC.S6.leverage (C x) (τ x)) < 2 * l} := measurableSet_lt hmax measurable_const
    exact Measurable.ite hset hth hτ
  · have heq : (fun x => AndersonAC.S6.chooseRidge (C x) l (τ x)) = τ := by
      funext x
      unfold AndersonAC.S6.chooseRidge
      have hnn := maxWeight_nonneg (AndersonAC.S6.leverage (C x) (τ x))
      have hfalse : ¬ AndersonAC.S6.maxWeight (AndersonAC.S6.leverage (C x) (τ x)) < 2 * l := by
        intro hcon
        have hle : l ≤ 0 := le_of_not_gt hl
        linarith
      rw [if_neg hfalse]
    rw [heq]
    exact hτ

/-- Projection readiness at fixed sets. -/
theorem upd_measSet_ready {Bt : Type*} [Fintype Bt] [DecidableEq Bt]
    {C : α → Matrix (Torus d m) Bt ℂ} (hC : Measurable C) (c : ℝ) :
    MeasurableSet {x | ∀ i, AndersonAC.S6.projectionWeight (C x) i ≤ c} := by
  have hset : {x | ∀ i, AndersonAC.S6.projectionWeight (C x) i ≤ c}
      = ⋂ i, {x | AndersonAC.S6.projectionWeight (C x) i ≤ c} := by
    ext x
    simp
  rw [hset]
  refine MeasurableSet.iInter fun i => ?_
  have hrp : Measurable (fun C : Matrix (Torus d m) Bt ℂ =>
      AndersonAC.S6.rangeProjection C) :=
    (AndersonAC.S6.ridge_threshold_measurable (R := Torus d m) (B := Bt) 1 zero_lt_one).2
  have hpw : Measurable (fun x => AndersonAC.S6.projectionWeight (C x) i) :=
    Complex.continuous_re.measurable.comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp (hrp.comp hC)))
  exact measurableSet_le hpw measurable_const

/-- Least maximizer equal to `some p₀`. -/
theorem upd_measSet_leastMax {w : α → Torus d m → ℝ}
    (hw : ∀ i, Measurable fun x => w x i) (p₀ : Torus d m) :
    MeasurableSet {x | AndersonAC.S6.leastMaximizer (siteRank d m) (w x) = some p₀} := by
  have hmax : Measurable fun x => AndersonAC.S6.maxWeight (w x) :=
    measurable_maxWeight_of hw
  have heq : {x | AndersonAC.S6.leastMaximizer (siteRank d m) (w x) = some p₀}
      = {x | w x p₀ = AndersonAC.S6.maxWeight (w x)} ∩
        ⋂ q, {x | w x q = AndersonAC.S6.maxWeight (w x) →
          siteRank d m p₀ ≤ siteRank d m q} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, leastMaximizer_eq_some]
  rw [heq]
  refine (measurableSet_eq_fun (hw p₀) hmax).inter (MeasurableSet.iInter fun q => ?_)
  by_cases hord : siteRank d m p₀ ≤ siteRank d m q
  · have h1 : {x | w x q = AndersonAC.S6.maxWeight (w x) →
        siteRank d m p₀ ≤ siteRank d m q} = Set.univ := by
      ext x
      simp [hord]
    rw [h1]
    exact MeasurableSet.univ
  · have h1 : {x | w x q = AndersonAC.S6.maxWeight (w x) →
        siteRank d m p₀ ≤ siteRank d m q} = {x | w x q = AndersonAC.S6.maxWeight (w x)}ᶜ := by
      ext x
      simp [hord]
    rw [h1]
    exact (measurableSet_eq_fun (hw q) hmax).compl

/-- Least maximizer equal to `none`. -/
theorem upd_measSet_leastMax_none {w : α → Torus d m → ℝ}
    (hw : ∀ i, Measurable fun x => w x i) :
    MeasurableSet {x | AndersonAC.S6.leastMaximizer (siteRank d m) (w x) = none} := by
  have heq : {x | AndersonAC.S6.leastMaximizer (siteRank d m) (w x) = none}
      = (⋃ p₀, {x | AndersonAC.S6.leastMaximizer (siteRank d m) (w x) = some p₀})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro h p₀ h'
      rw [h] at h'
      cases h'
    · intro h
      cases hx : AndersonAC.S6.leastMaximizer (siteRank d m) (w x) with
      | none => rfl
      | some p => exact absurd hx (h p)
  rw [heq]
  exact (MeasurableSet.iUnion fun p₀ => upd_measSet_leastMax hw p₀).compl

end UpdS6

/-! ### State coordinates and the pivot guard -/

section UpdState
variable {d m : ℕ}

/-- Residual from an answer at a fixed height (absolute digit positions). -/
theorem upd_meas_resid (lam : ℝ) (y : Torus d m) (H : ℕ) :
    Measurable (fun ans : Answer (Torus d m) => residOfAnswer (d := d) (m := m) lam y H ans) := by
  have hdig : Measurable (fun ans : Answer (Torus d m) =>
      fun k : ℕ => ((ans.1 (Sum.inl (y, k))).getD false)) := by
    refine Measurable.of_eval fun k => ?_
    exact meas_getD_false.comp ((measurable_pi_apply _).comp measurable_fst)
  exact (AndersonAC.S2.binarySuffix_measurable lam H).comp hdig

/-- Heat residual at the record's prefix height, joint in state/answer. -/
theorem upd_meas_heatXi (lam : ℝ) (p : Torus d m) :
    Measurable (fun q : (RunRecord d m × ClearScratch d m) × Answer (Torus d m) =>
      residOfAnswer (d := d) (m := m) lam p (q.1.1.prefixLength p) q.2) :=
  upd_measurable_of_key (fun q : (RunRecord d m × ClearScratch d m) × Answer (Torus d m) =>
      q.1.1.prefixLength p)
    (fun H q => residOfAnswer (d := d) (m := m) lam p H q.2)
    (fun H => ((meas_prefix_eval p).comp measurable_fst) (measurableSet_singleton H))
    (fun H => (upd_meas_resid lam p H).comp measurable_snd) (fun _ => rfl)

/-- Pivot guard at a fixed core. -/
theorem upd_measSet_guard (j : ℕ) (B : Finset (Torus d m)) (p : Torus d m) :
    MeasurableSet {s : RunRecord d m × ClearScratch d m |
      guardHolds (d := d) (m := m) j B (coupledActive s.1) s.1.terminal p} := by
  have heq : {s : RunRecord d m × ClearScratch d m |
      guardHolds (d := d) (m := m) j B (coupledActive s.1) s.1.terminal p}
      = ({s : RunRecord d m × ClearScratch d m | p ∈ s.1.endpoint.active} ∩
        {s : RunRecord d m × ClearScratch d m | p ∈ s.1.pending}ᶜ) ∩
        ({s : RunRecord d m × ClearScratch d m | p ∈ s.1.terminal}ᶜ ∩
          {_s : RunRecord d m × ClearScratch d m |
            ∃ y ∈ B, physicalDistance d m p y ≤ inspectionRadius j / 2}) := by
    ext s
    simp [guardHolds, coupledActive, Finset.mem_sdiff, and_assoc]
  rw [heq]
  exact ((upd_measSet_mem meas_rec_active_ind p).inter
    (upd_measSet_mem meas_rec_pending_ind p).compl).inter
    ((upd_measSet_mem meas_rec_terminal_ind p).compl.inter (MeasurableSet.const _))

end UpdState

/-! ### Action key -/

/-- Proof-free action kind (plus `halt` for latched states). -/
inductive ClearKind (d m : ℕ) where
  | halt : ClearKind d m
  | fail : Option (Torus d m) → ClearKind d m
  | coreReady : ClearKind d m
  | heat : Torus d m → ClearKind d m
  | coreQuery : Torus d m → ClearKind d m
  | finish : ClearKind d m

instance (d m : ℕ) : MeasurableSpace (ClearKind d m) := ⊤

instance (d m : ℕ) : MeasurableSingletonClass (ClearKind d m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance (d m : ℕ) : Countable (ClearKind d m) := by
  refine Function.Injective.countable (f := fun k : ClearKind d m =>
    (match k with
    | .halt => Sum.inr (Sum.inr (Sum.inr true))
    | .fail po => Sum.inl (some po)
    | .coreReady => Sum.inl none
    | .heat p => Sum.inr (Sum.inl p)
    | .coreQuery y => Sum.inr (Sum.inr (Sum.inl y))
    | .finish => Sum.inr (Sum.inr (Sum.inr false)) :
      Option (Option (Torus d m)) ⊕ Torus d m ⊕ Torus d m ⊕ Bool)) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Forget the evidence of an action. -/
def clearKindOf {d m j : ℕ} {rc : RunRecord d m} {sc : ClearScratch d m} :
    ClearingAction d m j rc sc → ClearKind d m
  | .fail po => .fail po
  | .coreReady => .coreReady
  | .heat p _ => .heat p
  | .coreQuery y _ => .coreQuery y
  | .finish => .finish

section UpdKind
variable {d m : ℕ}

/-- Guarded failure candidate at a fixed core (`guardedCand`). -/
def updGuarded (j : ℕ) (B : Finset (Torus d m)) (rec : RunRecord d m)
    (o : Option (Torus d m)) : Option (Torus d m) :=
  o.bind fun p => if guardHolds (d := d) (m := m) j B (coupledActive rec) rec.terminal p
    then some p else none

/-- Heat-candidate branch of `actionOf` at a fixed core. -/
def updCandKind (j : ℕ) (B : Finset (Torus d m)) (rec : RunRecord d m)
    (o : Option (Torus d m)) : ClearKind d m :=
  match o with
  | some p =>
    if guardHolds (d := d) (m := m) j B (coupledActive rec) rec.terminal p then
      (if p ∈ B then .fail (some p) else .heat p)
    else .fail none
  | none => .coreReady

/-- `actionOf` with the core/active sets as explicit parameters. -/
def updKindBA (j : ℕ) (u : ℝ) (B A : Finset (Torus d m)) (rec : RunRecord d m)
    (sc : ClearScratch d m) : ClearKind d m :=
  if sc.failed then .fail none
  else if sc.done then .finish
  else if B = ∅ then .finish
  else if sc.corePhase then
    match (sc.coreLeft.toList.mergeSort
        (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? with
    | some y => .coreQuery y
    | none => .finish
  else
    if B ⊆ A then
      if AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc.hatG then
        if sc.step < AndersonAC.S6.heatLimit (stageScale u j m) then
          if AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
              (xCross (stageScale u j m) rec.r A (restrictM A sc.Mnum) B) sc.ridge) ≤
              4 * AndersonAC.S6.leverageScale (stageScale u j m) then
            if xReady (stageScale u j m) rec.r A (restrictM A sc.Mnum) B then .coreReady
            else updCandKind j B rec (AndersonAC.S6.leastMaximizer (siteRank d m)
              (AndersonAC.S6.leverage
                (xCross (stageScale u j m) rec.r A (restrictM A sc.Mnum) B) sc.ridge))
          else .fail (updGuarded j B rec (AndersonAC.S6.leastMaximizer (siteRank d m)
              (AndersonAC.S6.leverage
                (xCross (stageScale u j m) rec.r A (restrictM A sc.Mnum) B) sc.ridge)))
        else .fail none
      else .fail (updGuarded j B rec (AndersonAC.S6.leastMaximizer (siteRank d m)
              (AndersonAC.S6.leverage
                (xCross (stageScale u j m) rec.r A (restrictM A sc.Mnum) B) sc.ridge)))
    else .fail none

theorem clearKindOf_actionOf (j : ℕ) (u : ℝ) (rec : RunRecord d m) (sc : ClearScratch d m) :
    clearKindOf (actionOf (d := d) (m := m) j u rec sc) =
      updKindBA j u sc.core sc.active rec sc := by
  unfold actionOf updKindBA
  by_cases h1 : sc.failed = true
  · simp only [h1, ↓reduceIte]
    rfl
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : sc.done = true
  · simp only [h2, ↓reduceIte]
    rfl
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  by_cases h3 : sc.core = ∅
  · simp only [h3, ↓reduceIte]
    rfl
  simp only [h3, ↓reduceIte]
  by_cases h4 : sc.corePhase = true
  · simp only [h4, ↓reduceIte, ↓reduceDIte]
    generalize (sc.coreLeft.toList.mergeSort
      (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? = o
    cases o <;> rfl
  simp only [h4, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  by_cases h5 : sc.core ⊆ sc.active
  swap
  · simp only [h5, ↓reduceIte]
    rfl
  simp only [h5, ↓reduceIte]
  by_cases h6 : AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc.hatG
  swap
  · simp only [h6, ↓reduceIte]
    rfl
  simp only [h6, ↓reduceIte]
  by_cases h7 : sc.step < AndersonAC.S6.heatLimit (stageScale u j m)
  swap
  · simp only [h7, ↓reduceIte]
    rfl
  simp only [h7, ↓reduceIte]
  have hw : scratchWeights (stageScale u j m) rec.r sc sc.ridge =
      AndersonAC.S6.leverage (xCross (stageScale u j m) rec.r sc.active
        (restrictM sc.active sc.Mnum) sc.core) sc.ridge := rfl
  have hcp : candPivot rec.r sc (stageScale u j m) sc.ridge =
      AndersonAC.S6.leastMaximizer (siteRank d m) (AndersonAC.S6.leverage
        (xCross (stageScale u j m) rec.r sc.active (restrictM sc.active sc.Mnum) sc.core)
        sc.ridge) := rfl
  rw [hw, hcp]
  by_cases h8 : AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
      (xCross (stageScale u j m) rec.r sc.active (restrictM sc.active sc.Mnum) sc.core)
      sc.ridge) ≤ 4 * AndersonAC.S6.leverageScale (stageScale u j m)
  swap
  · simp only [h8, ↓reduceIte]
    rfl
  simp only [h8, ↓reduceIte]
  by_cases h9 : xReady (stageScale u j m) rec.r sc.active (restrictM sc.active sc.Mnum) sc.core
  · simp only [h9, ↓reduceIte]
    rfl
  simp only [h9, ↓reduceIte]
  unfold updCandKind
  generalize AndersonAC.S6.leastMaximizer (siteRank d m) (AndersonAC.S6.leverage
      (xCross (stageScale u j m) rec.r sc.active (restrictM sc.active sc.Mnum) sc.core)
      sc.ridge) = o
  cases o with
  | none => rfl
  | some p =>
    by_cases hg : guardHolds (d := d) (m := m) j sc.core (coupledActive rec) rec.terminal p
    · by_cases hp : p ∈ sc.core
      · simp only [hg, hp, ↓reduceIte, ↓reduceDIte]
        rfl
      · simp only [hg, hp, ↓reduceIte, ↓reduceDIte]
        rfl
    · simp only [hg, ↓reduceIte, ↓reduceDIte]
      rfl

/-- Kind of the next update (`halt` on latched states). -/
def updKindU (j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m) : ClearKind d m :=
  if s.2.failed = true ∨ s.2.done = true then .halt
  else clearKindOf (actionOf (d := d) (m := m) j u s.1 s.2)

theorem upd_meas_kindBA (j : ℕ) (u : ℝ) (B A : Finset (Torus d m)) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => updKindBA j u B A s.1 s.2) := by
  have hcross : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      xCross (stageScale u j m) s.1.r A (restrictM A s.2.Mnum) B) :=
    upd_meas_cross _ B A meas_rec_r meas_Mnum
  have hw : ∀ i, Measurable (fun s : RunRecord d m × ClearScratch d m =>
      AndersonAC.S6.leverage (xCross (stageScale u j m) s.1.r A (restrictM A s.2.Mnum) B)
        s.2.ridge i) := fun i => upd_meas_lev hcross meas_ridge i
  have hkeyO : ∀ o : Option (Torus d m), MeasurableSet {s : RunRecord d m × ClearScratch d m |
      AndersonAC.S6.leastMaximizer (siteRank d m) (AndersonAC.S6.leverage
        (xCross (stageScale u j m) s.1.r A (restrictM A s.2.Mnum) B) s.2.ridge) = o} := by
    intro o
    cases o with
    | none => exact upd_measSet_leastMax_none hw
    | some p₀ => exact upd_measSet_leastMax hw p₀
  have hcand : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      updCandKind j B s.1 (AndersonAC.S6.leastMaximizer (siteRank d m)
        (AndersonAC.S6.leverage
          (xCross (stageScale u j m) s.1.r A (restrictM A s.2.Mnum) B) s.2.ridge))) := by
    refine upd_measurable_of_key _ (fun o s => updCandKind j B s.1 o) hkeyO ?_ (fun _ => rfl)
    intro o
    cases o with
    | none => exact measurable_const
    | some p =>
      exact Measurable.ite (upd_measSet_guard j B p) measurable_const measurable_const
  have hguard : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (ClearKind.fail (updGuarded j B s.1 (AndersonAC.S6.leastMaximizer (siteRank d m)
        (AndersonAC.S6.leverage
          (xCross (stageScale u j m) s.1.r A (restrictM A s.2.Mnum) B) s.2.ridge))) :
        ClearKind d m)) := by
    refine upd_measurable_of_key _ (fun o s => (ClearKind.fail (updGuarded j B s.1 o) :
      ClearKind d m)) hkeyO ?_ (fun _ => rfl)
    intro o
    cases o with
    | none =>
      exact (measurable_const : Measurable fun _ : RunRecord d m × ClearScratch d m =>
        (ClearKind.fail none : ClearKind d m))
    | some p =>
      have heq : (fun s : RunRecord d m × ClearScratch d m =>
          (ClearKind.fail (updGuarded j B s.1 (some p)) : ClearKind d m))
          = fun s => if guardHolds (d := d) (m := m) j B (coupledActive s.1) s.1.terminal p
            then ClearKind.fail (some p) else ClearKind.fail none := by
        funext s
        simp only [updGuarded, Option.bind_some]
        split_ifs <;> rfl
      rw [heq]
      exact Measurable.ite (upd_measSet_guard j B p) measurable_const measurable_const
  have hhead : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      (match (s.2.coreLeft.toList.mergeSort
          (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? with
        | some y => ClearKind.coreQuery y
        | none => ClearKind.finish : ClearKind d m)) :=
    upd_meas_finset2 meas_coreLeft_ind meas_coreLeft_ind (fun C _ =>
      (match (C.toList.mergeSort
          (fun a b => decide ((siteRank d m a).val ≤ (siteRank d m b).val))).head? with
        | some y => ClearKind.coreQuery y
        | none => ClearKind.finish : ClearKind d m))
  unfold updKindBA
  refine Measurable.ite (meas_failed (measurableSet_singleton true)) measurable_const ?_
  refine Measurable.ite (meas_done (measurableSet_singleton true)) measurable_const ?_
  refine Measurable.ite (MeasurableSet.const _) measurable_const ?_
  refine Measurable.ite (meas_corePhase (measurableSet_singleton true)) hhead ?_
  refine Measurable.ite (MeasurableSet.const _) ?_ measurable_const
  refine Measurable.ite (measSet_budgets _) ?_ hguard
  refine Measurable.ite (measurableSet_lt meas_step measurable_const) ?_ measurable_const
  refine Measurable.ite (measurableSet_le (upd_meas_maxLev hcross meas_ridge)
    measurable_const) ?_ hguard
  exact Measurable.ite (upd_measSet_ready hcross _) measurable_const hcand

theorem upd_meas_kindU (j : ℕ) (u : ℝ) :
    Measurable (fun s : RunRecord d m × ClearScratch d m => updKindU j u s) := by
  have heq : (fun s : RunRecord d m × ClearScratch d m => updKindU j u s)
      = fun s => (fun (B A : Finset (Torus d m)) (s : RunRecord d m × ClearScratch d m) =>
          if s.2.failed = true ∨ s.2.done = true then ClearKind.halt
          else (updKindBA j u B A s.1 s.2 : ClearKind d m)) s.2.core s.2.active s := by
    funext s
    simp only [updKindU, clearKindOf_actionOf]
  rw [heq]
  exact upd_meas_coreActive (β := ClearKind d m)
    (c := fun s : RunRecord d m × ClearScratch d m => s.2.core)
    (a := fun s : RunRecord d m × ClearScratch d m => s.2.active)
    meas_core_ind meas_active_ind
    (fun (B A : Finset (Torus d m)) (s : RunRecord d m × ClearScratch d m) =>
      if s.2.failed = true ∨ s.2.done = true then ClearKind.halt
      else (updKindBA j u B A s.1 s.2 : ClearKind d m))
    (fun B A => Measurable.ite ((meas_failed (measurableSet_singleton true)).union
      (meas_done (measurableSet_singleton true))) measurable_const (upd_meas_kindBA j u B A))

end UpdKind


/-! ### Branch maps -/

section UpdMaps
variable {d m : ℕ}

/-- Schur step with measurable matrix and shift. -/
theorem upd_meas_schur {α : Type*} [MeasurableSpace α] (x₀ : Torus d m)
    {M : α → Matrix (Torus d m) (Torus d m) ℝ} {ξ : α → ℝ}
    (hM : Measurable M) (hξ : Measurable ξ) :
    Measurable (fun a => schurStepM (d := d) (m := m) (M a) x₀ (ξ a)) := by
  have hMe : ∀ i k : Torus d m, Measurable (fun a => M a i k) := fun i k =>
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hM)
  refine Measurable.of_eval_matrix _ fun i k => ?_
  by_cases h : i = x₀ ∨ k = x₀
  · by_cases hik : i = k
    · have heq : (fun a => schurStepM (d := d) (m := m) (M a) x₀ (ξ a) i k)
          = fun _ => (1 : ℝ) := by
        funext a
        simp only [schurStepM]
        rw [if_pos h, if_pos hik]
      rw [heq]
      exact measurable_const
    · have heq : (fun a => schurStepM (d := d) (m := m) (M a) x₀ (ξ a) i k)
          = fun _ => (0 : ℝ) := by
        funext a
        simp only [schurStepM]
        rw [if_pos h, if_neg hik]
      rw [heq]
      exact measurable_const
  · have heq : (fun a => schurStepM (d := d) (m := m) (M a) x₀ (ξ a) i k)
        = fun a => M a i k - M a i x₀ * M a x₀ k * (M a x₀ x₀ + ξ a)⁻¹ := by
      funext a
      simp only [schurStepM]
      rw [if_neg h, div_eq_mul_inv]
    rw [heq]
    exact (hMe i k).sub (((hMe i x₀).mul (hMe x₀ k)).mul
      (measurable_inv.comp ((hMe x₀ x₀).add hξ)))

/-- Point update of a measurable family. -/
theorem upd_meas_update {α : Type*} [MeasurableSpace α] (x₀ : Torus d m)
    {f : α → Torus d m → ℝ} {v : α → ℝ} (hf : Measurable f) (hv : Measurable v) :
    Measurable (fun a => Function.update (f a) x₀ (v a)) := by
  refine Measurable.of_eval fun y => ?_
  have heq : (fun a => Function.update (f a) x₀ (v a) y)
      = fun a => if y = x₀ then v a else f a y := by
    funext a
    simp only [Function.update_apply]
  rw [heq]
  exact Measurable.ite (MeasurableSet.const _) hv ((measurable_pi_apply y).comp hf)

/-- Refresh `hatG` from the active inverse on the current active set
(the `hatG` clause of `elimStep`). -/
def updRefreshG (t : ℝ) (s : RunRecord d m × ClearScratch d m) :
    Matrix (Torus d m) (Torus d m) ℂ := fun i k =>
  if h : i ∈ s.2.active ∧ k ∈ s.2.active then
    AndersonAC.S6.activeInverse (restrictM s.2.active s.2.Mnum) t
      (fun i : {i // i ∈ s.2.active} => s.1.r i.val) ⟨i, h.1⟩ ⟨k, h.2⟩
  else s.2.hatG i k

/-- Refresh `hatG` (state map). -/
def updRefresh (t : ℝ) (s : RunRecord d m × ClearScratch d m) :
    RunRecord d m × ClearScratch d m :=
  (s.1, { s.2 with hatG := updRefreshG t s })

theorem upd_meas_refresh (t : ℝ) : Measurable (updRefresh (d := d) (m := m) t) := by
  have hG : Measurable (fun s : RunRecord d m × ClearScratch d m => updRefreshG t s) := by
    refine Measurable.of_eval_matrix _ fun i k => ?_
    unfold updRefreshG
    refine upd_meas_coreActive (β := ℂ)
      (c := fun s : RunRecord d m × ClearScratch d m => s.2.core)
      (a := fun s : RunRecord d m × ClearScratch d m => s.2.active)
      meas_core_ind meas_active_ind
      (fun (_ A : Finset (Torus d m)) (s : RunRecord d m × ClearScratch d m) =>
        if h : i ∈ A ∧ k ∈ A then
          AndersonAC.S6.activeInverse (restrictM A s.2.Mnum) t
            (fun i : {i // i ∈ A} => s.1.r i.val) ⟨i, h.1⟩ ⟨k, h.2⟩
        else s.2.hatG i k) fun _ A => ?_
    by_cases hik : i ∈ A ∧ k ∈ A
    · have heq : (fun s : RunRecord d m × ClearScratch d m =>
          if h : i ∈ A ∧ k ∈ A then
            AndersonAC.S6.activeInverse (restrictM A s.2.Mnum) t
              (fun i : {i // i ∈ A} => s.1.r i.val) ⟨i, h.1⟩ ⟨k, h.2⟩
          else s.2.hatG i k)
          = fun s => AndersonAC.S6.activeInverse (restrictM A s.2.Mnum) t
              (fun i : {i // i ∈ A} => s.1.r i.val) ⟨i, hik.1⟩ ⟨k, hik.2⟩ :=
        funext fun s => dif_pos hik
      rw [heq]
      have hMs : Measurable (fun s : RunRecord d m × ClearScratch d m =>
          restrictM A s.2.Mnum) := tool_subM (A₀ := A) meas_Mnum
      have hrs : Measurable (fun s : RunRecord d m × ClearScratch d m =>
          (fun i : {i // i ∈ A} => s.1.r i.val)) :=
        Measurable.of_eval fun i => meas_r_eval i.val
      exact tool_trialInverse_eval t hMs hrs _ _
    · have heq : (fun s : RunRecord d m × ClearScratch d m =>
          if h : i ∈ A ∧ k ∈ A then
            AndersonAC.S6.activeInverse (restrictM A s.2.Mnum) t
              (fun i : {i // i ∈ A} => s.1.r i.val) ⟨i, h.1⟩ ⟨k, h.2⟩
          else s.2.hatG i k)
          = fun s => s.2.hatG i k :=
        funext fun s => dif_neg hik
      rw [heq]
      exact meas_hatG_eval i k
  unfold updRefresh
  exact measurable_fst.prodMk (upd_meas_scratch_mk meas_core_ind meas_step meas_active_ind
    meas_inspected_ind meas_ridge meas_Mnum hG meas_g0 meas_resids meas_failed meas_done
    meas_corePhase meas_coreLeft_ind)

/-- Re-choose the ridge of the current state (`chooseRidge` at the current ridge). -/
def updRidge (t l : ℝ) (s : RunRecord d m × ClearScratch d m) : ℝ :=
  AndersonAC.S6.chooseRidge
    (xCross t s.1.r s.2.active (restrictM s.2.active s.2.Mnum) s.2.core) l s.2.ridge

/-- Re-choose the ridge (state map). -/
def updReridge (t l : ℝ) (s : RunRecord d m × ClearScratch d m) :
    RunRecord d m × ClearScratch d m :=
  (s.1, { s.2 with ridge := updRidge t l s })

theorem upd_meas_reridge (t l : ℝ) : Measurable (updReridge (d := d) (m := m) t l) := by
  have hR : Measurable (fun s : RunRecord d m × ClearScratch d m => updRidge t l s) :=
    upd_meas_coreActive (β := ℝ)
      (c := fun s : RunRecord d m × ClearScratch d m => s.2.core)
      (a := fun s : RunRecord d m × ClearScratch d m => s.2.active)
      meas_core_ind meas_active_ind
      (fun (B A : Finset (Torus d m)) (s : RunRecord d m × ClearScratch d m) =>
        AndersonAC.S6.chooseRidge (xCross t s.1.r A (restrictM A s.2.Mnum) B) l s.2.ridge)
      (fun B A => upd_meas_chooseRidge (upd_meas_cross t B A meas_rec_r meas_Mnum) meas_ridge l)
  unfold updReridge
  exact measurable_fst.prodMk (upd_meas_scratch_mk meas_core_ind meas_step meas_active_ind
    meas_inspected_ind hR meas_Mnum meas_hatG meas_g0 meas_resids meas_failed meas_done
    meas_corePhase meas_coreLeft_ind)

/-- Post-heat stop checks (budgets, heat limit, cap, readiness) on the successor. -/
def updPost (t l : ℝ) (s : RunRecord d m × ClearScratch d m) :
    RunRecord d m × ClearScratch d m :=
  if ¬ AndersonAC.S6.BudgetsHold t s.2.g0 s.2.hatG then (s.1, { s.2 with failed := true })
  else if s.2.step ≥ AndersonAC.S6.heatLimit t then (s.1, { s.2 with failed := true })
  else if 4 * l < AndersonAC.S6.maxWeight (scratchWeights (d := d) (m := m) t s.1.r s.2 s.2.ridge)
    then (s.1, { s.2 with failed := true })
  else if xReady t s.1.r s.2.active (restrictM s.2.active s.2.Mnum) s.2.core then
    (s.1, { s.2 with corePhase := true })
  else s

theorem upd_meas_post (t l : ℝ) : Measurable (updPost (d := d) (m := m) t l) := by
  have hfail : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      ((s.1, { s.2 with failed := true }) : RunRecord d m × ClearScratch d m)) :=
    measurable_fst.prodMk (upd_meas_scratch_mk meas_core_ind meas_step meas_active_ind
      meas_inspected_ind meas_ridge meas_Mnum meas_hatG meas_g0 meas_resids measurable_const
      meas_done meas_corePhase meas_coreLeft_ind)
  have hready : Measurable (fun s : RunRecord d m × ClearScratch d m =>
      ((s.1, { s.2 with corePhase := true }) : RunRecord d m × ClearScratch d m)) :=
    measurable_fst.prodMk (upd_meas_scratch_mk meas_core_ind meas_step meas_active_ind
      meas_inspected_ind meas_ridge meas_Mnum meas_hatG meas_g0 meas_resids meas_failed
      meas_done measurable_const meas_coreLeft_ind)
  have c1 : MeasurableSet {s : RunRecord d m × ClearScratch d m |
      ¬ AndersonAC.S6.BudgetsHold t s.2.g0 s.2.hatG} := (measSet_budgets t).compl
  have c2 : MeasurableSet {s : RunRecord d m × ClearScratch d m |
      s.2.step ≥ AndersonAC.S6.heatLimit t} := measurableSet_le measurable_const meas_step
  have c3 : MeasurableSet {s : RunRecord d m × ClearScratch d m |
      4 * l < AndersonAC.S6.maxWeight (scratchWeights (d := d) (m := m) t s.1.r s.2 s.2.ridge)} :=
    upd_measSet_coreActive
      (c := fun s : RunRecord d m × ClearScratch d m => s.2.core)
      (a := fun s : RunRecord d m × ClearScratch d m => s.2.active)
      meas_core_ind meas_active_ind
      (fun (B A : Finset (Torus d m)) (s : RunRecord d m × ClearScratch d m) =>
        4 * l < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage
          (xCross t s.1.r A (restrictM A s.2.Mnum) B) s.2.ridge))
      (fun B A => measurableSet_lt measurable_const
        (upd_meas_maxLev (upd_meas_cross t B A meas_rec_r meas_Mnum) meas_ridge))
  have c4 : MeasurableSet {s : RunRecord d m × ClearScratch d m |
      xReady t s.1.r s.2.active (restrictM s.2.active s.2.Mnum) s.2.core} :=
    upd_measSet_coreActive
      (c := fun s : RunRecord d m × ClearScratch d m => s.2.core)
      (a := fun s : RunRecord d m × ClearScratch d m => s.2.active)
      meas_core_ind meas_active_ind
      (fun (B A : Finset (Torus d m)) (s : RunRecord d m × ClearScratch d m) =>
        xReady t s.1.r A (restrictM A s.2.Mnum) B)
      (fun B A => upd_measSet_ready (upd_meas_cross t B A meas_rec_r meas_Mnum) _)
  unfold updPost
  exact Measurable.ite c1 hfail (Measurable.ite c2 hfail (Measurable.ite c3 hfail
    (Measurable.ite c4 hready measurable_id)))

/-- Heat step before the hatG refresh: Schur update with the revealed residual. -/
def updHeat0 (lam : ℝ) (p : Torus d m)
    (q : (RunRecord d m × ClearScratch d m) × Answer (Torus d m)) :
    RunRecord d m × ClearScratch d m :=
  (q.1.1, { q.1.2 with
    Mnum := schurStepM q.1.2.Mnum p (residOfAnswer lam p (q.1.1.prefixLength p) q.2),
    active := q.1.2.active.erase p,
    resids := Function.update q.1.2.resids p (residOfAnswer lam p (q.1.1.prefixLength p) q.2),
    inspected := insert p q.1.2.inspected,
    step := q.1.2.step + 1 })

/-- Core step before the hatG refresh. -/
def updCore0 (lam : ℝ) (y : Torus d m)
    (q : (RunRecord d m × ClearScratch d m) × Answer (Torus d m)) :
    RunRecord d m × ClearScratch d m :=
  (q.1.1, { q.1.2 with
    Mnum := schurStepM q.1.2.Mnum y (residOfAnswer lam y 0 q.2 - q.1.1.installed y),
    active := q.1.2.active.erase y,
    resids := Function.update q.1.2.resids y (residOfAnswer lam y 0 q.2 - q.1.1.installed y),
    coreLeft := q.1.2.coreLeft.erase y,
    done := decide (q.1.2.coreLeft.erase y = ∅) })

section Lift
variable (d m) in
/-- Projection of the state from a state/answer pair. -/
abbrev UpdQ := (RunRecord d m × ClearScratch d m) × Answer (Torus d m)
end Lift

theorem upd_q_core : Measurable (fun q : UpdQ d m => finsetCode q.1.2.core) :=
  meas_core_ind.comp measurable_fst
theorem upd_q_active : Measurable (fun q : UpdQ d m => finsetCode q.1.2.active) :=
  meas_active_ind.comp measurable_fst
theorem upd_q_inspected : Measurable (fun q : UpdQ d m => finsetCode q.1.2.inspected) :=
  meas_inspected_ind.comp measurable_fst
theorem upd_q_coreLeft : Measurable (fun q : UpdQ d m => finsetCode q.1.2.coreLeft) :=
  meas_coreLeft_ind.comp measurable_fst
theorem upd_q_step : Measurable (fun q : UpdQ d m => q.1.2.step) := meas_step.comp measurable_fst
theorem upd_q_ridge : Measurable (fun q : UpdQ d m => q.1.2.ridge) := meas_ridge.comp measurable_fst
theorem upd_q_Mnum : Measurable (fun q : UpdQ d m => q.1.2.Mnum) := meas_Mnum.comp measurable_fst
theorem upd_q_hatG : Measurable (fun q : UpdQ d m => q.1.2.hatG) := meas_hatG.comp measurable_fst
theorem upd_q_g0 : Measurable (fun q : UpdQ d m => q.1.2.g0) := meas_g0.comp measurable_fst
theorem upd_q_resids : Measurable (fun q : UpdQ d m => q.1.2.resids) :=
  meas_resids.comp measurable_fst
theorem upd_q_failed : Measurable (fun q : UpdQ d m => q.1.2.failed) :=
  meas_failed.comp measurable_fst
theorem upd_q_done : Measurable (fun q : UpdQ d m => q.1.2.done) := meas_done.comp measurable_fst
theorem upd_q_corePhase : Measurable (fun q : UpdQ d m => q.1.2.corePhase) :=
  meas_corePhase.comp measurable_fst
theorem upd_q_rec : Measurable (fun q : UpdQ d m => q.1.1) := measurable_fst.comp measurable_fst

theorem upd_meas_heat0 (lam : ℝ) (p : Torus d m) :
    Measurable (updHeat0 (d := d) (m := m) lam p) := by
  have hξ := upd_meas_heatXi (d := d) (m := m) lam p
  have hM : Measurable (fun q : UpdQ d m =>
      schurStepM q.1.2.Mnum p (residOfAnswer lam p (q.1.1.prefixLength p) q.2)) :=
    upd_meas_schur p upd_q_Mnum hξ
  have hres : Measurable (fun q : UpdQ d m =>
      Function.update q.1.2.resids p (residOfAnswer lam p (q.1.1.prefixLength p) q.2)) :=
    upd_meas_update p upd_q_resids hξ
  have hact : Measurable (fun q : UpdQ d m => finsetCode (q.1.2.active.erase p)) :=
    upd_meas_finset2 upd_q_active upd_q_active (fun A _ => finsetCode (A.erase p))
  have hinsp : Measurable (fun q : UpdQ d m => finsetCode (insert p q.1.2.inspected)) :=
    upd_meas_finset2 upd_q_inspected upd_q_inspected (fun A _ => finsetCode (insert p A))
  have hstep : Measurable (fun q : UpdQ d m => q.1.2.step + 1) :=
    (measurable_of_countable (fun n : ℕ => n + 1)).comp upd_q_step
  unfold updHeat0
  exact upd_q_rec.prodMk (upd_meas_scratch_mk upd_q_core hstep hact hinsp upd_q_ridge hM
    upd_q_hatG upd_q_g0 hres upd_q_failed upd_q_done upd_q_corePhase upd_q_coreLeft)

theorem upd_meas_core0 (lam : ℝ) (y : Torus d m) :
    Measurable (updCore0 (d := d) (m := m) lam y) := by
  have hξ : Measurable (fun q : UpdQ d m =>
      residOfAnswer lam y 0 q.2 - q.1.1.installed y) :=
    ((upd_meas_resid lam y 0).comp measurable_snd).sub
      ((meas_installed_eval y).comp measurable_fst)
  have hM : Measurable (fun q : UpdQ d m =>
      schurStepM q.1.2.Mnum y (residOfAnswer lam y 0 q.2 - q.1.1.installed y)) :=
    upd_meas_schur y upd_q_Mnum hξ
  have hres : Measurable (fun q : UpdQ d m =>
      Function.update q.1.2.resids y (residOfAnswer lam y 0 q.2 - q.1.1.installed y)) :=
    upd_meas_update y upd_q_resids hξ
  have hact : Measurable (fun q : UpdQ d m => finsetCode (q.1.2.active.erase y)) :=
    upd_meas_finset2 upd_q_active upd_q_active (fun A _ => finsetCode (A.erase y))
  have hleft : Measurable (fun q : UpdQ d m => finsetCode (q.1.2.coreLeft.erase y)) :=
    upd_meas_finset2 upd_q_coreLeft upd_q_coreLeft (fun A _ => finsetCode (A.erase y))
  have hdone : Measurable (fun q : UpdQ d m => decide (q.1.2.coreLeft.erase y = ∅)) :=
    upd_meas_finset2 upd_q_coreLeft upd_q_coreLeft (fun A _ => decide (A.erase y = ∅))
  unfold updCore0
  exact upd_q_rec.prodMk (upd_meas_scratch_mk upd_q_core upd_q_step hact upd_q_inspected
    upd_q_ridge hM upd_q_hatG upd_q_g0 hres upd_q_failed hdone upd_q_corePhase hleft)

/-- The update, branch by action kind. -/
def updByKind (n₀ j : ℕ) (u : ℝ) : ClearKind d m → UpdQ d m → RunRecord d m × ClearScratch d m
  | .halt, q => q.1
  | .fail po, q => (q.1.1, { q.1.2 with failed := true, inspected := po.elim q.1.2.inspected (fun p => insert p q.1.2.inspected) })
  | .coreReady, q => (q.1.1, { q.1.2 with corePhase := true })
  | .heat p, q => updPost (stageScale u j m) (AndersonAC.S6.leverageScale (stageScale u j m))
      (updReridge (stageScale u j m) (AndersonAC.S6.leverageScale (stageScale u j m))
        (updRefresh (stageScale u j m) (updHeat0 (clearingLam n₀ u) p q)))
  | .coreQuery y, q => updRefresh (stageScale u j m) (updCore0 (clearingLam n₀ u) y q)
  | .finish, q => (q.1.1, { q.1.2 with done := true })

theorem upd_meas_byKind (n₀ j : ℕ) (u : ℝ) (k : ClearKind d m) :
    Measurable (updByKind (d := d) (m := m) n₀ j u k) := by
  have hT : Measurable (fun _ : UpdQ d m => true) := measurable_const
  cases k with
  | halt => exact measurable_fst
  | fail po =>
    have hinsp : Measurable (fun q : UpdQ d m =>
        finsetCode (po.elim q.1.2.inspected (fun p => insert p q.1.2.inspected))) :=
      upd_meas_finset2 upd_q_inspected upd_q_inspected
        (fun A _ => finsetCode (po.elim A (fun p => insert p A)))
    have h := upd_q_rec.prodMk (upd_meas_scratch_mk upd_q_core upd_q_step upd_q_active hinsp
      upd_q_ridge upd_q_Mnum upd_q_hatG upd_q_g0 upd_q_resids hT upd_q_done
      upd_q_corePhase upd_q_coreLeft)
    exact h
  | coreReady =>
    have h := upd_q_rec.prodMk (upd_meas_scratch_mk upd_q_core upd_q_step upd_q_active
      upd_q_inspected upd_q_ridge upd_q_Mnum upd_q_hatG upd_q_g0 upd_q_resids upd_q_failed
      upd_q_done hT upd_q_coreLeft)
    exact h
  | heat p =>
    have h := (upd_meas_post (d := d) (m := m) (stageScale u j m)
      (AndersonAC.S6.leverageScale (stageScale u j m))).comp
      ((upd_meas_reridge (stageScale u j m) (AndersonAC.S6.leverageScale (stageScale u j m))).comp
        ((upd_meas_refresh (stageScale u j m)).comp (upd_meas_heat0 (clearingLam n₀ u) p)))
    exact h
  | coreQuery y =>
    have h := (upd_meas_refresh (d := d) (m := m) (stageScale u j m)).comp
      (upd_meas_core0 (clearingLam n₀ u) y)
    exact h
  | finish =>
    have h := upd_q_rec.prodMk (upd_meas_scratch_mk upd_q_core upd_q_step upd_q_active
      upd_q_inspected upd_q_ridge upd_q_Mnum upd_q_hatG upd_q_g0 upd_q_resids upd_q_failed
      hT upd_q_corePhase upd_q_coreLeft)
    exact h

theorem clearingUpdate_eq_byKind (n₀ j : ℕ) (u : ℝ)
    (s : RunRecord d m × ClearScratch d m) (ans : Answer (Torus d m)) :
    clearingUpdate (d := d) (m := m) n₀ j u s ans =
      updByKind n₀ j u (updKindU j u s) (s, ans) := by
  unfold clearingUpdate updKindU
  by_cases h : s.2.failed = true ∨ s.2.done = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    cases hact : actionOf (d := d) (m := m) j u s.1 s.2 <;> rfl

/-- `update` is measurable. -/
theorem block_update_meas (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Measurable (fun p : (RunRecord d m × ClearScratch d m) × Answer (Torus d m) =>
      (clearingBlock (d := d) (m := m) n₀ j u x).update p.1 p.2) := by
  have hkey : ∀ k : ClearKind d m, MeasurableSet {q : UpdQ d m | updKindU j u q.1 = k} :=
    fun k => ((upd_meas_kindU (d := d) (m := m) j u).comp measurable_fst)
      (measurableSet_singleton k)
  exact upd_measurable_of_key (fun q : UpdQ d m => updKindU j u q.1)
    (fun k => updByKind (d := d) (m := m) n₀ j u k) hkey
    (fun k => upd_meas_byKind n₀ j u k)
    (fun q => clearingUpdate_eq_byKind n₀ j u q.1 q.2)

end UpdMaps

/-- (1) The clearing block is measurable. -/
theorem clearingBlock_measurable {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    (clearingBlock (d := d) (m := m) n₀ j u x).IsMeasurable :=
  ⟨block_enter_meas n₀ j u x, block_next_meas n₀ j u x, block_update_meas n₀ j u x,
    block_halted_meas, block_exit_meas n₀ j u x, block_firstFail_meas⟩

/-- Equality of patterns from equality of fields. -/
theorem fp_eq_of_fields {d m : ℕ} {p q : FreshPattern (Torus d m)}
    (hs : p.sites = q.sites) (hh : p.height = q.height)
    (ha : p.aux = q.aux) (ho : p.orders = q.orders) : p = q := by
  cases p with
  | mk s h a o =>
    cases q with
    | mk s' h' a' o' =>
      simp_all

/-- The read pattern is measurable in the entering record
(`FreshPattern` carries `⊤`, so this is the `hcpatm` field).
Fibers are finite Boolean combinations of the site-membership sets
(`patSet_sites_mem`) and the height evaluations. -/
theorem clearingPattern_measurable {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m) :
    Measurable (clearingPattern (d := d) (m := m) n₀ j u x) := by
  classical
  refine measurable_of_singleton_fibers fun π₀ => ?_
  have hfib : (clearingPattern (d := d) (m := m) n₀ j u x) ⁻¹' {π₀}
      = ((⋂ y, ({rc : RunRecord d m |
            y ∈ (clearingPattern (d := d) (m := m) n₀ j u x rc).sites} ∩
            {rc : RunRecord d m | y ∈ π₀.sites} ∪
          ({rc : RunRecord d m |
            y ∈ (clearingPattern (d := d) (m := m) n₀ j u x rc).sites}ᶜ ∩
            {rc : RunRecord d m | y ∈ π₀.sites}ᶜ))) ∩
        ((⋂ y, {rc : RunRecord d m |
            (clearingPattern (d := d) (m := m) n₀ j u x rc).height y =
              π₀.height y}) ∩
        ({rc : RunRecord d m |
          (clearingPattern (d := d) (m := m) n₀ j u x rc).aux = π₀.aux} ∩
        {rc : RunRecord d m |
          (clearingPattern (d := d) (m := m) n₀ j u x rc).orders = π₀.orders}))) := by
    ext rc
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro y
        by_cases hy : y ∈ (clearingPattern (d := d) (m := m) n₀ j u x rc).sites
        · have hy' : y ∈ π₀.sites := by rw [← h]; exact hy
          exact Or.inl ⟨hy, hy'⟩
        · have hy2 : y ∉ π₀.sites := by
            intro hc
            apply hy
            rw [h]
            exact hc
          exact Or.inr ⟨hy, hy2⟩
      · intro y
        rw [h]
      · rw [h]
      · rw [h]
    · intro h
      obtain ⟨hsites, hheight, haux, horders⟩ := h
      have hs : (clearingPattern (d := d) (m := m) n₀ j u x rc).sites = π₀.sites := by
        ext y
        have hy := hsites y
        tauto
      have hh : (clearingPattern (d := d) (m := m) n₀ j u x rc).height = π₀.height := by
        funext y
        exact hheight y
      have hpat : clearingPattern (d := d) (m := m) n₀ j u x rc = π₀ :=
        fp_eq_of_fields hs hh haux horders
      exact hpat
  rw [hfib]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · refine MeasurableSet.iInter fun y => ?_
    have hfix : MeasurableSet {rc : RunRecord d m | y ∈ π₀.sites} := by
      by_cases hy : y ∈ π₀.sites
      · simpa [hy] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (RunRecord d m)))
      · have : {rc : RunRecord d m | y ∈ π₀.sites} = ∅ := by
          ext rc
          simp [hy]
        rw [this]
        exact MeasurableSet.empty
    have hfixc : MeasurableSet {rc : RunRecord d m | y ∈ π₀.sites}ᶜ :=
      hfix.compl
    refine MeasurableSet.union ?_ ?_
    · exact MeasurableSet.inter (patSet_sites_mem n₀ j u x y) hfix
    · exact MeasurableSet.inter (patSet_sites_mem n₀ j u x y).compl hfixc
  · refine MeasurableSet.iInter fun y => ?_
    have hmeas : Measurable (fun rc : RunRecord d m =>
        (clearingPattern (d := d) (m := m) n₀ j u x rc).height y) := by
      have heq : (fun rc : RunRecord d m =>
            (clearingPattern (d := d) (m := m) n₀ j u x rc).height y)
          = (fun rc : RunRecord d m => rc.prefixLength y) := by
        funext rc
        rfl
      rw [heq]
      exact (measurable_pi_apply y).comp pat_meas_prefix
    exact hmeas (measurableSet_singleton (π₀.height y))
  · -- aux is always ∅
    have hpat_aux : ∀ rc : RunRecord d m,
        (clearingPattern (d := d) (m := m) n₀ j u x rc).aux = ∅ := fun rc => rfl
    by_cases h : π₀.aux = ∅
    · have hset : {rc : RunRecord d m |
            (clearingPattern (d := d) (m := m) n₀ j u x rc).aux = π₀.aux} =
          Set.univ := by
        ext rc
        simp [hpat_aux rc, h]
      rw [hset]
      exact MeasurableSet.univ
    · have hset : {rc : RunRecord d m |
            (clearingPattern (d := d) (m := m) n₀ j u x rc).aux = π₀.aux} = ∅ := by
        ext rc
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [hpat_aux rc]
        exact iff_false_intro (fun he => h he.symm)
      rw [hset]
      exact MeasurableSet.empty
  · -- orders is always ∅
    have hpat_ord : ∀ rc : RunRecord d m,
        (clearingPattern (d := d) (m := m) n₀ j u x rc).orders = ∅ := fun rc => rfl
    by_cases h : π₀.orders = ∅
    · have hset : {rc : RunRecord d m |
            (clearingPattern (d := d) (m := m) n₀ j u x rc).orders = π₀.orders} =
          Set.univ := by
        ext rc
        simp [hpat_ord rc, h]
      rw [hset]
      exact MeasurableSet.univ
    · have hset : {rc : RunRecord d m |
            (clearingPattern (d := d) (m := m) n₀ j u x rc).orders = π₀.orders} = ∅ := by
        ext rc
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [hpat_ord rc]
        exact iff_false_intro (fun he => h he.symm)
      rw [hset]
      exact MeasurableSet.empty

/-! ## `fail_local` helpers: record preservation, empty blocks, pattern coverage -/

section FailLocal
variable {d m : ℕ} {n₀ j : ℕ} {u : ℝ} {x : Torus d m} {M : ℕ → ℕ}

/-- Updates never touch the committed record. -/
theorem update_fst (s : RunRecord d m × ClearScratch d m)
    (ans : Answer (Torus d m)) :
    (clearingUpdate (d := d) (m := m) n₀ j u s ans).1 = s.1 := by
  unfold clearingUpdate
  dsimp only
  split
  · rfl
  · cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
    | fail po => rfl
    | coreReady => rfl
    | heat p hg =>
      -- all heat sub-branches return (s.1, ...)
      dsimp only
      split_ifs <;> rfl
    | coreQuery y _ => rfl
    | finish => rfl

/-- Block-local states keep the entering record. -/
theorem state_fst (r : RunRecord d m) (n : ℕ) (ω : RandomSources (Torus d m) M) :
    (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).1 = r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((clearingBlock (d := d) (m := m) n₀ j u x).update
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _).1 = r
    show (clearingUpdate (d := d) (m := m) n₀ j u
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _).1 = r
    rw [update_fst]
    exact ih

/-- Updates fix halted states. -/
theorem update_halted_fixed (s : RunRecord d m × ClearScratch d m)
    (ans : Answer (Torus d m)) (h : s.2.failed ∨ s.2.done) :
    clearingUpdate (d := d) (m := m) n₀ j u s ans = s := by
  unfold clearingUpdate
  simp [h]

/-- The initial scratch is done exactly on empty blocks. -/
theorem init_done_true (r : RunRecord d m)
    (hempty : r.aborted = true ∨ ¬clearingScheduled j m ∨
      theCore (d := d) (m := m) j u x r = ∅) :
    (clearInitScratch (d := d) (m := m) j u x r).done = true := by
  unfold clearInitScratch
  dsimp only
  rcases hempty with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

/-- Empty entering records never fail block-locally. -/
theorem empty_firstFail_empty (r : RunRecord d m)
    (hempty : r.aborted = true ∨ ¬clearingScheduled j m ∨
      theCore (d := d) (m := m) j u x r = ∅) :
    localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) r = ∅ := by
  have hdone : (clearInitScratch (d := d) (m := m) j u x r).done = true :=
    init_done_true r hempty
  have hstate : ∀ n (ω : RandomSources (Torus d m) M),
      localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω =
        (clearingBlock (d := d) (m := m) n₀ j u x).enter r := by
    intro n
    induction n with
    | zero => intro ω; rfl
    | succ n ih =>
      intro ω
      show ((clearingBlock (d := d) (m := m) n₀ j u x).update
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _)
        = _
      show clearingUpdate (d := d) (m := m) n₀ j u
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _ = _
      rw [ih]
      apply update_halted_fixed
      -- enter has done=true
      exact Or.inr hdone
  ext ω
  simp only [localFirstFail, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hcon
  obtain ⟨k, hk, hfk⟩ := hcon
  cases k with
  | zero =>
    have h0 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r 0 ω =
        (r, clearInitScratch (d := d) (m := m) j u x r) := rfl
    have hff : (clearingBlock (d := d) (m := m) n₀ j u x).firstFail
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r 0 ω) = false := by
      rw [h0, clearingBlock_firstFail_eq]
      rfl
    rw [hff] at hfk
    exact Bool.noConfusion hfk
  | succ k =>
    have h0 : (clearingBlock (d := d) (m := m) n₀ j u x).halted
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r 0 ω) = false :=
      hk 0 (Nat.zero_lt_succ k)
    have h0eq : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r 0 ω =
        (r, clearInitScratch (d := d) (m := m) j u x r) := rfl
    have hhalt : (clearingBlock (d := d) (m := m) n₀ j u x).halted
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r 0 ω) = true := by
      rw [h0eq, clearingBlock_halted_eq]
      unfold clearingHalted
      simp [hdone]
    rw [hhalt] at h0
    exact Bool.noConfusion h0

/-- Once `corePhase` holds (with no failure), no later state fails:
core actions never set `failed`. -/
theorem future_no_fail (r : RunRecord d m)
    (n : ℕ) (ω : RandomSources (Torus d m) M)
    (hcore : (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.corePhase = true)
    (hfail : (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.failed = false) :
    ∀ k, n ≤ k →
      (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω).2.failed = false := by
  have key : ∀ k, n ≤ k →
      (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω).2.failed = false ∧
      (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω).2.corePhase = true := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨hfail, hcore⟩
    | succ k hle ih =>
      obtain ⟨hf, hc⟩ := ih
      -- name the pre-state
      set s := localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω with hs
      have hf' : s.2.failed = false := hf
      have hc' : s.2.corePhase = true := hc
      -- corePhase actions discriminate against fail/coreReady/heat:
      -- the coreLeft match (on a variable) is never those constructors.
      have hne_fail : ∀ (o : Option (Torus d m)) (po : Option (Torus d m)),
          (match o with
          | some y => ClearingAction.coreQuery (d := d) (m := m) (j := j)
              (rc := s.1) (sc := s.2) y hc'
          | none => ClearingAction.finish (d := d) (m := m) (j := j)
              (rc := s.1) (sc := s.2)) ≠
          ClearingAction.fail (d := d) (m := m) (j := j)
            (rc := s.1) (sc := s.2) po := by
        intro o po
        cases o <;> simp
      have hne_ready : ∀ (o : Option (Torus d m)),
          (match o with
          | some y => ClearingAction.coreQuery (d := d) (m := m) (j := j)
              (rc := s.1) (sc := s.2) y hc'
          | none => ClearingAction.finish (d := d) (m := m) (j := j)
              (rc := s.1) (sc := s.2)) ≠
          ClearingAction.coreReady (d := d) (m := m) (j := j)
            (rc := s.1) (sc := s.2) := by
        intro o
        cases o <;> simp
      have hne_heat : ∀ (o : Option (Torus d m)) (p : Torus d m)
          (hg : guardHolds (d := d) (m := m) j s.2.core
            (coupledActive s.1) s.1.terminal p),
          (match o with
          | some y => ClearingAction.coreQuery (d := d) (m := m) (j := j)
              (rc := s.1) (sc := s.2) y hc'
          | none => ClearingAction.finish (d := d) (m := m) (j := j)
              (rc := s.1) (sc := s.2)) ≠
          ClearingAction.heat (d := d) (m := m) (j := j)
            (rc := s.1) (sc := s.2) p hg := by
        intro o p hg
        cases o <;> simp
      have hstep : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (k + 1) ω =
          (clearingBlock (d := d) (m := m) n₀ j u x).update s _ := rfl
      rw [hstep]
      show (clearingUpdate (d := d) (m := m) n₀ j u s _).2.failed = false ∧
        (clearingUpdate (d := d) (m := m) n₀ j u s _).2.corePhase = true
      -- update preserves (failed=false, corePhase=true): case on halted first
      by_cases hhalt : s.2.failed ∨ s.2.done
      · -- halted: state fixed
        rw [update_halted_fixed _ _ hhalt]
        exact ⟨hf', hc'⟩
      · -- running with corePhase: action is coreQuery or finish
        push_neg at hhalt
        obtain ⟨hff, hdd⟩ := hhalt
        by_cases hcore : s.2.core = ∅
        · cases hact' : actionOf (d := d) (m := m) j u s.1 s.2 with
          | fail po =>
            exfalso
            unfold actionOf at hact'
            simp [hff, hdd, hcore] at hact'
          | coreReady =>
            exfalso
            unfold actionOf at hact'
            simp [hff, hdd, hcore] at hact'
          | heat p hg =>
            exfalso
            unfold actionOf at hact'
            simp [hff, hdd, hcore] at hact'
          | coreQuery y _ =>
            exfalso
            unfold actionOf at hact'
            simp [hff, hdd, hcore] at hact'
          | finish =>
            refine ⟨?_, ?_⟩ <;>
              (unfold clearingUpdate <;> simp [hff, hdd, hact'] <;> assumption)
        · cases hact' : actionOf (d := d) (m := m) j u s.1 s.2 with
          | fail po =>
            exfalso
            unfold actionOf at hact'
            simp [hff, hdd, hcore, hc'] at hact'
            exact absurd hact' (hne_fail _ _)
          | coreReady =>
            exfalso
            unfold actionOf at hact'
            simp [hff, hdd, hcore, hc'] at hact'
            exact absurd hact' (hne_ready _)
          | heat p hg =>
            exfalso
            unfold actionOf at hact'
            simp [hff, hdd, hcore, hc'] at hact'
            exact absurd hact' (hne_heat _ _ _)
          | coreQuery y _ =>
            refine ⟨?_, ?_⟩ <;>
              (unfold clearingUpdate <;> simp [hff, hdd, hact'] <;> assumption)
          | finish =>
            refine ⟨?_, ?_⟩ <;>
              (unfold clearingUpdate <;> simp [hff, hdd, hact'] <;> assumption)
  exact fun k hk => (key k hk).1

/-- Heat pivots (guard-passing) lie in the read pattern (nonempty case). -/
theorem heat_mem_pattern (r : RunRecord d m)
    (hab : r.aborted = false) (hsch : clearingScheduled j m)
    (hcore : theCore (d := d) (m := m) j u x r ≠ ∅)
    {p : Torus d m}
    (hguard : guardHolds (d := d) (m := m) j
      (theCore (d := d) (m := m) j u x r) (coupledActive r) r.terminal p) :
    p ∈ (clearingPattern (d := d) (m := m) n₀ j u x r).sites := by
  unfold clearingPattern
  simp only
  have hab' : r.aborted = true ↔ False := by simp [hab]
  simp [hab', hsch, hcore]
  obtain ⟨hmem, hterm, _⟩ := hguard
  simp [coupledActive, Finset.mem_sdiff] at hmem ⊢
  exact ⟨⟨hmem.1, hmem.2⟩, hterm⟩

/-- Updates never change the core. -/
theorem update_core (s : RunRecord d m × ClearScratch d m)
    (ans : Answer (Torus d m)) :
    (clearingUpdate (d := d) (m := m) n₀ j u s ans).2.core = s.2.core := by
  unfold clearingUpdate
  dsimp only
  split
  · rfl
  · cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
    | fail po => rfl
    | coreReady => rfl
    | heat p hg =>
      dsimp only
      split_ifs <;> rfl
    | coreQuery y _ => rfl
    | finish => rfl

/-- Block-local scratch cores equal the eligible core. -/
theorem state_core (r : RunRecord d m) (n : ℕ) (ω : RandomSources (Torus d m) M) :
    (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.core =
      theCore (d := d) (m := m) j u x r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((clearingBlock (d := d) (m := m) n₀ j u x).update
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _).2.core = _
    show (clearingUpdate (d := d) (m := m) n₀ j u
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _).2.core = _
    rw [update_core]
    exact ih

/-- Halted-false gives failed-false and done-false. -/
theorem halted_false_iff (s : RunRecord d m × ClearScratch d m) :
    clearingHalted s = false ↔ s.2.failed = false ∧ s.2.done = false := by
  unfold clearingHalted
  cases h1 : s.2.failed <;> cases h2 : s.2.done <;> simp [h1, h2]

/-- Heat residuals agree on pattern-agreeing samples (the query history
`L` is irrelevant for `trueSuffix` answers). -/
theorem heat_resid_agree (r : RunRecord d m)
    (hab : r.aborted = false) (hsch : clearingScheduled j m)
    (hcore : theCore (d := d) (m := m) j u x r ≠ ∅)
    {p : Torus d m}
    (hguard : guardHolds (d := d) (m := m) j
      (theCore (d := d) (m := m) j u x r) (coupledActive r) r.terminal p)
    {L L' : List (Query (Torus d m))}
    {ω ω' : RandomSources (Torus d m) M}
    (hagree : ∀ z ∈ (clearingPattern (d := d) (m := m) n₀ j u x r).signs,
      ω.1 z = ω'.1 z) :
    residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p (r.prefixLength p)
      (localAnswer (Torus d m) M L (Query.trueSuffix p (r.prefixLength p)) ω) =
    residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p (r.prefixLength p)
      (localAnswer (Torus d m) M L' (Query.trueSuffix p (r.prefixLength p)) ω') := by
  have hsites : p ∈ (clearingPattern (d := d) (m := m) n₀ j u x r).sites :=
    heat_mem_pattern r hab hsch hcore hguard
  have hpt : ∀ k : ℕ, (Sum.inl (p, r.prefixLength p + k) :
      AndersonAC.S2.SignIndex (Torus d m)) ∈
      (clearingPattern (d := d) (m := m) n₀ j u x r).signs := by
    intro k
    -- pattern height is prefixLength; aux is empty
    show _ ∈ FreshPattern.signs _
    unfold FreshPattern.signs
    refine Or.inl ?_
    exact ⟨p, hsites, r.prefixLength p + k, Nat.le_add_right _ _, rfl⟩
  unfold residOfAnswer
  have e1 : (fun k => ((localAnswer (Torus d m) M L
      (Query.trueSuffix p (r.prefixLength p)) ω).1
      (Sum.inl (p, r.prefixLength p + k))).getD false)
      = (fun k => ω.1 (Sum.inl (p, r.prefixLength p + k))) := by
    funext k
    have hmem : (Sum.inl (p, r.prefixLength p + k) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈
        AndersonAC.S2.querySigns (Torus d m)
          (Query.trueSuffix p (r.prefixLength p)) :=
      ⟨r.prefixLength p + k, Nat.le_add_right _ _, rfl⟩
    unfold localAnswer
    simp [hmem]
  have e2 : (fun k => ((localAnswer (Torus d m) M L'
      (Query.trueSuffix p (r.prefixLength p)) ω').1
      (Sum.inl (p, r.prefixLength p + k))).getD false)
      = (fun k => ω'.1 (Sum.inl (p, r.prefixLength p + k))) := by
    funext k
    have hmem : (Sum.inl (p, r.prefixLength p + k) :
        AndersonAC.S2.SignIndex (Torus d m)) ∈
        AndersonAC.S2.querySigns (Torus d m)
          (Query.trueSuffix p (r.prefixLength p)) :=
      ⟨r.prefixLength p + k, Nat.le_add_right _ _, rfl⟩
    unfold localAnswer
    simp [hmem]
  unfold AndersonAC.S2.binarySuffix
  congr 1
  funext k
  have h1 := congrFun e1 k
  have h2 := congrFun e2 k
  beta_reduce at h1 h2 ⊢
  rw [h1, h2, hagree _ (hpt k)]

/-- Bool dichotomy: not-false is true. -/
theorem bool_eq_true_of_ne_false {b : Bool} (h : b ≠ false) : b = true := by
  cases b with
  | true => rfl
  | false => exact absurd rfl h

/-- Bool dichotomy: not-true is false. -/
theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬b = true) : b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

/-- Before the first failure, `corePhase` is false (else `future_no_fail`
would contradict the failure). -/
theorem corePhase_false_before (r : RunRecord d m)
    {k : ℕ} {ω : RandomSources (Torus d m) M}
    (hk : ∀ k' < k, (clearingBlock (d := d) (m := m) n₀ j u x).halted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω) = false)
    (hfk : (clearingBlock (d := d) (m := m) n₀ j u x).firstFail
      (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω) = true) :
    ∀ n, n < k →
      (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.corePhase = false := by
  intro n hn
  by_contra hcon
  -- hcon : ¬ corePhase = false, i.e. ≠ false; hence = true (Bool)
  have htrue : (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.corePhase = true :=
    bool_eq_true_of_ne_false hcon
  have hhalt := hk n hn
  rw [clearingBlock_halted_eq] at hhalt
  have hfd := (halted_false_iff _).mp hhalt
  have hlater := future_no_fail (d := d) (m := m) (n₀ := n₀) (j := j) (u := u)
    (x := x) (M := M) r n ω htrue hfd.1 k (Nat.le_of_lt hn)
  have hfailK : (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω).2.failed = true := by
    have := hfk
    rw [clearingBlock_firstFail_eq] at this
    simpa [clearingFirstFail] using this
  rw [hlater] at hfailK
  exact Bool.noConfusion hfailK

end FailLocal

/-- (3) `fail_local` (`hclocal`): the block-local first failure depends only on
the coupled active sites at their prefix heights (no aux, no orders).
Core-suffix queries happen only after the heats succeed, so `firstFail`
is decided by the heat queries alone. -/
theorem clearingBlock_fail_local {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m)
    (M : ℕ → ℕ) (r : RunRecord d m) :
    DependsOnly (Torus d m) (M := M)
      (clearingPattern (d := d) (m := m) n₀ j u x r)
      (localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) r) := by
  classical
  by_cases hempty : (r.aborted = true ∨ ¬clearingScheduled j m ∨
      theCore (d := d) (m := m) j u x r = ∅)
  · -- empty: no failure, so locality is vacuous
    rw [empty_firstFail_empty (d := d) (m := m) (n₀ := n₀) (j := j) (u := u)
      (x := x) (M := M) r hempty]
    intro ω ω' _ _
    simp
  · push_neg at hempty
    obtain ⟨hab_ne, hsch_ne, hcore_ne⟩ := hempty
    have hab : r.aborted = false := bool_eq_false_of_ne_true hab_ne
    have hsch : clearingScheduled j m := hsch_ne
    have hcore : theCore (d := d) (m := m) j u x r ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp hcore_ne
    -- symmetric suffices (orders are empty)
    suffices H : ∀ ω ω' : RandomSources (Torus d m) M,
        (∀ z ∈ (clearingPattern (d := d) (m := m) n₀ j u x r).signs,
          ω.1 z = ω'.1 z) →
        ω ∈ localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) r →
        ω' ∈ localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) r by
      intro ω ω' h1 _
      exact ⟨H _ _ h1, H _ _ (fun z hz => (h1 z hz).symm)⟩
    intro ω ω' hagree hmem
    obtain ⟨k, hk, hfk⟩ := hmem
    -- states agree up to k (corePhase stays false there by corePhase_false_before)
    have hcpfalse : ∀ n, n < k →
        (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.corePhase = false :=
      corePhase_false_before (d := d) (m := m) (n₀ := n₀) (j := j) (u := u)
        (x := x) (M := M) r hk hfk
    have key : ∀ n, n ≤ k →
        localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω =
        localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω' := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        have hn' : n ≤ k := Nat.le_of_succ_le hn
        have hlt : n < k := Nat.lt_of_succ_le hn
        have ihn := ih hn'
        have hcp := hcpfalse n hlt
        have hhalt_n := hk n hlt
        rw [clearingBlock_halted_eq] at hhalt_n
        have hfd := (halted_false_iff _).mp hhalt_n
        have hfst_n : (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).1 = r :=
          state_fst (d := d) (m := m) (n₀ := n₀) (j := j) (u := u) (x := x) (M := M) r n ω
        have hcore_n : (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.core =
            theCore (d := d) (m := m) j u x r :=
          state_core (d := d) (m := m) (n₀ := n₀) (j := j) (u := u) (x := x) (M := M) r n ω
        cases hact' : actionOf (d := d) (m := m) j u
            (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).1
            (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2 with
        | fail po =>
          have e1 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _ := rfl
          have e2 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω' =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω') _ := rfl
          rw [e1, e2, ← ihn]
          -- fail ignores the answer
          show clearingUpdate (d := d) (m := m) n₀ j u _ _ =
            clearingUpdate (d := d) (m := m) n₀ j u _ _
          unfold clearingUpdate
          simp [hact']
        | coreReady =>
          have e1 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _ := rfl
          have e2 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω' =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω') _ := rfl
          rw [e1, e2, ← ihn]
          show clearingUpdate (d := d) (m := m) n₀ j u _ _ =
            clearingUpdate (d := d) (m := m) n₀ j u _ _
          unfold clearingUpdate
          simp [hact']
        | heat p hg =>
          -- guard pivot is in the pattern; residuals agree
          have hg' : guardHolds (d := d) (m := m) j
              (theCore (d := d) (m := m) j u x r) (coupledActive r) r.terminal p := by
            rw [hcore_n, hfst_n] at hg
            exact hg
          have hq : (clearingBlock (d := d) (m := m) n₀ j u x).next
              (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) =
              Query.trueSuffix p (r.prefixLength p) := by
            rw [clearingBlock_next_eq]
            simp [clearingNext, hact', hfst_n]
          -- same, in machineRun form (definitionally equal to the above)
          have hqm_ω : (clearingBlock (d := d) (m := m) n₀ j u x).next
              (machineRun (Torus d m) M ((clearingBlock (d := d) (m := m) n₀ j u x).enter r)
                (clearingBlock (d := d) (m := m) n₀ j u x).next
                (clearingBlock (d := d) (m := m) n₀ j u x).update n ω).1 =
              Query.trueSuffix p (r.prefixLength p) := hq
          have hqm_ω' : (clearingBlock (d := d) (m := m) n₀ j u x).next
              (machineRun (Torus d m) M ((clearingBlock (d := d) (m := m) n₀ j u x).enter r)
                (clearingBlock (d := d) (m := m) n₀ j u x).next
                (clearingBlock (d := d) (m := m) n₀ j u x).update n ω').1 =
              Query.trueSuffix p (r.prefixLength p) := by
            have h := hq
            rw [ihn] at h
            exact h
          have e1 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _ := rfl
          have e2 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω' =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω') _ := rfl
          rw [e1, e2, ← ihn]
          show clearingUpdate (d := d) (m := m) n₀ j u _ _ =
            clearingUpdate (d := d) (m := m) n₀ j u _ _
          -- the two answers give equal heat residuals
          have hxi : ∀ L L' : List (Query (Torus d m)),
              residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p (r.prefixLength p)
                (localAnswer (Torus d m) M L
                  (Query.trueSuffix p (r.prefixLength p)) ω) =
              residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p (r.prefixLength p)
                (localAnswer (Torus d m) M L'
                  (Query.trueSuffix p (r.prefixLength p)) ω') :=
            fun L L' => heat_resid_agree (d := d) (m := m) (n₀ := n₀) (j := j) (u := u)
              (x := x) (M := M) r hab hsch hcore hg' hagree
          obtain ⟨hff, hdd⟩ := hfd
          unfold clearingUpdate
          simp only [hff, hdd, hact', hqm_ω, hqm_ω', hfst_n]
          rw [hxi _ _]
        | coreQuery y hc_ev =>
          -- impossible: corePhase is false here
          exfalso
          have hcp_n : (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω).2.corePhase = true :=
            hc_ev
          rw [hcp] at hcp_n
          exact Bool.noConfusion hcp_n
        | finish =>
          have e1 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω) _ := rfl
          have e2 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r (n + 1) ω' =
              (clearingBlock (d := d) (m := m) n₀ j u x).update
                (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r n ω') _ := rfl
          rw [e1, e2, ← ihn]
          show clearingUpdate (d := d) (m := m) n₀ j u _ _ =
            clearingUpdate (d := d) (m := m) n₀ j u _ _
          unfold clearingUpdate
          simp [hact']
    -- transfer the failure witness
    have hkk := key k (Nat.le_refl k)
    refine ⟨k, ?_, ?_⟩
    · intro k' hk'
      have h1 : localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω =
          localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k' ω' :=
        key k' (Nat.le_of_lt (Nat.lt_of_lt_of_le hk' (Nat.le_refl k)))
      have := hk k' hk'
      rw [clearingBlock_halted_eq, h1] at this
      -- this : halted (state ω') = false; need in Block.halted form
      simpa [clearingBlock_halted_eq] using this
    · have h2 : (clearingBlock (d := d) (m := m) n₀ j u x).firstFail
          (localState M (clearingBlock (d := d) (m := m) n₀ j u x) r k ω') = true := by
        have := hfk
        rw [clearingBlock_firstFail_eq, hkk] at this
        simpa [clearingBlock_firstFail_eq] using this
      exact h2

/-! ## Bridge reindexing helpers: Torus active-subtype ≃ ActiveSite active-subtype -/

section BridgeReindex
variable {d m : ℕ} {rec0 : RunRecord d m}

/-- Canonical equiv between Torus-active-subtype and ActiveSite-active-subtype,
for corresponding active sets (`A` on Torus, `A'` on ActiveSite with the
same `val`-image). Computable with `rfl` simp lemmas. -/
def activeEquiv (A : Finset (Torus d m)) (A' : Finset (ActiveSite rec0))
    (hsub : A ⊆ rec0.endpoint.active)
    (hcorr : A'.image Subtype.val = A) : {i // i ∈ A} ≃ {x // x ∈ A'} where
  toFun := fun i => ⟨⟨i.val, hsub i.property⟩, by
    have : i.val ∈ A'.image Subtype.val := by
      rw [hcorr]
      exact i.property
    obtain ⟨x, hx_mem, hx_val⟩ := Finset.mem_image.mp this
    have : (⟨i.val, hsub i.property⟩ : ActiveSite rec0) = x :=
      Subtype.ext hx_val.symm
    rw [this]
    exact hx_mem⟩
  invFun := fun x => ⟨x.val.val, by
    have : x.val.val ∈ A'.image Subtype.val :=
      Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩
    rw [hcorr] at this
    exact this⟩
  left_inv := by
    intro i
    ext
    rfl
  right_inv := by
    intro x
    ext
    rfl

/-- Simp lemmas for `activeEquiv` values (definitional). -/
@[simp] theorem activeEquiv_val_val (A : Finset (Torus d m)) (A' : Finset (ActiveSite rec0))
    (hsub : A ⊆ rec0.endpoint.active)
    (hcorr : A'.image Subtype.val = A) (i : Torus d m) (hi : i ∈ A) :
    (((activeEquiv (rec0 := rec0) A A' hsub hcorr ⟨i, hi⟩).val).val : Torus d m) = i :=
  rfl

@[simp] theorem activeEquiv_symm_val_val (A : Finset (Torus d m)) (A' : Finset (ActiveSite rec0))
    (hsub : A ⊆ rec0.endpoint.active)
    (hcorr : A'.image Subtype.val = A) (a : {x // x ∈ A'}) :
    (((activeEquiv (rec0 := rec0) A A' hsub hcorr).symm a).val : Torus d m) = a.val.val :=
  rfl

end BridgeReindex

section BridgeCorr
variable {d m : ℕ} {rec0 : RunRecord d m}

/-- Damped matrices correspond under `activeEquiv` reindexing (entrywise
from `M`/`r` correspondence; `Matrix.reindex` commutes with the
damped construction). -/
theorem damped_reindex_corr (A : Finset (Torus d m)) (A' : Finset (ActiveSite rec0))
    (hsub : A ⊆ rec0.endpoint.active)
    (hcorr : A'.image Subtype.val = A)
    (M_T : Matrix {i // i ∈ A} {i // i ∈ A} ℝ)
    (M_A : Matrix {x // x ∈ A'} {x // x ∈ A'} ℝ)
    (r_T : {i // i ∈ A} → ℂ) (r_A : {x // x ∈ A'} → ℂ)
    (t : ℝ)
    (hM : ∀ (i : Torus d m) (hi : i ∈ A) (x : ActiveSite rec0) (hx : x ∈ A'),
      x.val = i → ∀ (j : Torus d m) (hj : j ∈ A) (y : ActiveSite rec0) (hy : y ∈ A'),
      y.val = j → M_T ⟨i, hi⟩ ⟨j, hj⟩ = M_A ⟨x, hx⟩ ⟨y, hy⟩)
    (hr : ∀ (i : Torus d m) (hi : i ∈ A) (x : ActiveSite rec0) (hx : x ∈ A'),
      x.val = i → r_T ⟨i, hi⟩ = r_A ⟨x, hx⟩) :
    ∀ (i : Torus d m) (hi : i ∈ A) (x : ActiveSite rec0) (hx : x ∈ A'),
      x.val = i → ∀ (j : Torus d m) (hj : j ∈ A) (y : ActiveSite rec0) (hy : y ∈ A'),
      y.val = j →
      (AndersonAC.S6.dampedMatrix M_T t r_T) ⟨i, hi⟩ ⟨j, hj⟩ =
        (AndersonAC.S6.dampedMatrix M_A t r_A) ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro i hi x hx hvx j hj y hy hvy
  unfold AndersonAC.S6.dampedMatrix
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hdiag : (Matrix.diagonal r_T ⟨i, hi⟩ ⟨j, hj⟩ : ℂ) =
      Matrix.diagonal r_A ⟨x, hx⟩ ⟨y, hy⟩ := by
    have hiff : ((⟨i, hi⟩ : {i // i ∈ A}) = ⟨j, hj⟩) ↔
        ((⟨x, hx⟩ : {x // x ∈ A'}) = ⟨y, hy⟩) := by
      constructor
      · intro h
        have hval : i = j := congrArg Subtype.val h
        apply Subtype.ext
        show x = y
        apply Subtype.ext
        show x.val = y.val
        rw [hvx, hvy, hval]
      · intro h
        have hval : x = y := congrArg Subtype.val h
        have hval2 : x.val = y.val := congrArg Subtype.val hval
        have hij : i = j := by rw [← hvx, ← hvy]; exact hval2
        apply Subtype.ext
        show i = j
        exact hij
    by_cases h : (⟨i, hi⟩ : {i // i ∈ A}) = ⟨j, hj⟩
    · have h' : (⟨x, hx⟩ : {x // x ∈ A'}) = ⟨y, hy⟩ := hiff.mp h
      simp [h, h']
      exact hr j hj y hy hvy
    · have h' : (⟨x, hx⟩ : {x // x ∈ A'}) ≠ ⟨y, hy⟩ :=
        fun hcon => h (hiff.mpr hcon)
      simp [h, h']
  rw [hdiag, hM i hi x hx hvx j hj y hy hvy]

/-- Active inverses correspond across `activeEquiv` (via
`Matrix.inv_submatrix_equiv`; no nonsingularity needed).
Hypotheses are entrywise (no equivs in statement); the equiv is built
inside from `hcorr`. -/
theorem activeInverse_corr (A : Finset (Torus d m)) (A' : Finset (ActiveSite rec0))
    (hsub : A ⊆ rec0.endpoint.active)
    (hcorr : A'.image Subtype.val = A)
    (M_T : Matrix {i // i ∈ A} {i // i ∈ A} ℝ)
    (M_A : Matrix {x // x ∈ A'} {x // x ∈ A'} ℝ)
    (r_T : {i // i ∈ A} → ℂ) (r_A : {x // x ∈ A'} → ℂ)
    (t : ℝ)
    (hM : ∀ (i : Torus d m) (hi : i ∈ A) (x : ActiveSite rec0) (hx : x ∈ A'),
      x.val = i → ∀ (j : Torus d m) (hj : j ∈ A) (y : ActiveSite rec0) (hy : y ∈ A'),
      y.val = j → M_T ⟨i, hi⟩ ⟨j, hj⟩ = M_A ⟨x, hx⟩ ⟨y, hy⟩)
    (hr : ∀ (i : Torus d m) (hi : i ∈ A) (x : ActiveSite rec0) (hx : x ∈ A'),
      x.val = i → r_T ⟨i, hi⟩ = r_A ⟨x, hx⟩) :
    ∀ (i : Torus d m) (hi : i ∈ A) (x : ActiveSite rec0) (hx : x ∈ A'),
      x.val = i → ∀ (j : Torus d m) (hj : j ∈ A) (y : ActiveSite rec0) (hy : y ∈ A'),
      y.val = j →
      (AndersonAC.S6.activeInverse M_T t r_T) ⟨i, hi⟩ ⟨j, hj⟩ =
        (AndersonAC.S6.activeInverse M_A t r_A) ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro i hi x hx hvx j hj y hy hvy
  set e := activeEquiv (rec0 := rec0) A A' hsub hcorr with he
  -- damped matrices agree on corresponding pairs (already proved entrywise)
  have hD : ∀ (a : Torus d m) (ha : a ∈ A) (u : ActiveSite rec0) (hu : u ∈ A'),
      u.val = a → ∀ (b : Torus d m) (hb : b ∈ A) (v : ActiveSite rec0) (hv : v ∈ A'),
      v.val = b →
      (AndersonAC.S6.dampedMatrix M_T t r_T) ⟨a, ha⟩ ⟨b, hb⟩ =
        (AndersonAC.S6.dampedMatrix M_A t r_A) ⟨u, hu⟩ ⟨v, hv⟩ :=
    fun a ha u hu huv b hb v hv hvv =>
      damped_reindex_corr (rec0 := rec0) A A' hsub hcorr M_T M_A r_T r_A t
        hM hr a ha u hu huv b hb v hv hvv
  -- as a submatrix equation along `e`
  have hDsub : AndersonAC.S6.dampedMatrix M_T t r_T =
      (AndersonAC.S6.dampedMatrix M_A t r_A).submatrix e e := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Matrix.submatrix_apply]
    have hx : ((e ⟨a, ha⟩).val : ActiveSite rec0) ∈ A' := (e ⟨a, ha⟩).property
    have hy : ((e ⟨b, hb⟩).val : ActiveSite rec0) ∈ A' := (e ⟨b, hb⟩).property
    have hvx : ((e ⟨a, ha⟩).val : ActiveSite rec0).val = a :=
      activeEquiv_val_val _ _ _ _ _ _
    have hvy : ((e ⟨b, hb⟩).val : ActiveSite rec0).val = b :=
      activeEquiv_val_val _ _ _ _ _ _
    exact hD a ha _ hx hvx b hb _ hy hvy
  -- inverses commute with submatrix reindexing
  have hinv : (AndersonAC.S6.dampedMatrix M_T t r_T)⁻¹ =
      ((AndersonAC.S6.dampedMatrix M_A t r_A)⁻¹).submatrix e e := by
    rw [hDsub]
    exact Matrix.inv_submatrix_equiv _ e e
  -- activeInverse unfolds to damped inverse; conclude entrywise
  unfold AndersonAC.S6.activeInverse
  rw [hinv]
  simp only [Matrix.submatrix_apply]
  have e1 : e ⟨i, hi⟩ = (⟨x, hx⟩ : {x // x ∈ A'}) := by
    apply Subtype.ext
    show ((e ⟨i, hi⟩).val : ActiveSite rec0) = x
    apply Subtype.ext
    show (((e ⟨i, hi⟩).val : ActiveSite rec0)).val = x.val
    rw [activeEquiv_val_val]
    exact hvx.symm
  have e2 : e ⟨j, hj⟩ = (⟨y, hy⟩ : {x // x ∈ A'}) := by
    apply Subtype.ext
    show ((e ⟨j, hj⟩).val : ActiveSite rec0) = y
    apply Subtype.ext
    show (((e ⟨j, hj⟩).val : ActiveSite rec0)).val = y.val
    rw [activeEquiv_val_val]
    exact hvy.symm
  rw [e1, e2]

end BridgeCorr

/-! (4) The bridge to §6 (`clearingBlock_bridge`, pointwise form of INTERFACE-ISSUES 03:57:19)
is stated and proved in `ClearingBridge.lean` (agent-s78cbridge). -/

end AndersonAC.AgentS78
