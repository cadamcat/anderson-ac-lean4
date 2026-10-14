import AndersonAC.AgentS78.Construction.TileBlockFacts
import AndersonAC.AgentS78.Construction.RecordFresh
import AndersonAC.AgentS78.Construction.Reached
import AndersonAC.AgentS78.Construction.TileBlockMeasurable
import AndersonAC.AgentS78.Construction.MachineRunProof

/-!
# WP10 construction: the pathwise disciplines of the tile block (frozen contracts)

Consumers: `step_of_marking` (MarkingRule.lean, `hblock`, with `pend := RunRecord.pending`,
`lab := RunRecord.latest`, `label n := ⟨j, .tile, tileAnchor⟩`; the distance clause follows
from `y ∈ tileSites` and the tile diameter of the plan) and `fresh_of_declared_aux`
(Freshness.lean, `hblock` with `freshSet := declaredFresh`, and `hpat`).

* `TileMarkingStatement`: a site pending at exit was pending at entry with the same label,
  or it is a site of the tile, labelled with the tile's birth label, and the first trial
  failed (05:512–514, 08:41–47).
* `TileQueryStatement`: the declared-fresh set only shrinks, and no sign declared fresh at
  exit was queried during the block (02-state.tex:96–113).
* `TilePatternStatement`: the pattern's true signs are declared fresh at entry; its
  auxiliary signs and orders lie in the tile's own index sets.

Known adjustments needed in TileBlock.lean for these to hold (agent-s78con, 2026-10-13):
(1) final residual sweep: its `trueSuffix` query reveals the whole suffix, so the committed
site must become terminal (`declaredFresh` excludes terminal sites); (2) terminal sites are
skipped (05:343): `activeIn` also requires `i ∉ x.terminal`, and the pattern's sites exclude
terminal sites (since 2026-10-13 23:58 `declaredFresh` no longer mentions the active set: its
sites are the non-pending, non-terminal ones); (3) on an aborted entering record the pattern is empty (the block halts at
once; `declaredFresh` of an aborted record is empty).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer querySigns SignIndex)

variable {d m : ℕ}

/-- **Tile marking discipline (frozen contract).** -/
def TileMarkingStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x : RunRecord d m) (s : RunRecord d m × TileScratch d m),
    BlockReach (tileBlock P j T) x s → (tileBlock P j T).halted s = true →
    ∀ y ∈ ((tileBlock P j T).exit s).pending,
      (y ∈ x.pending ∧ ((tileBlock P j T).exit s).latest y = x.latest y) ∨
      (((tileBlock P j T).exit s).latest y = ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ ∧
        (tileBlock P j T).firstFail s = true ∧ y ∈ tileSites (P.cover j) T)

def TileMarkingInv (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x : RunRecord d m) (s : RunRecord d m × TileScratch d m) : Prop :=
  ∀ y, y ∈ s.1.pending →
    (y ∈ x.pending ∧ s.1.latest y = x.latest y) ∨
      (s.1.latest y = ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ ∧
        s.2.firstFail = true ∧ y ∈ tileSites (P.cover j) T)

theorem tileMarkingInv_failTrial (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (h : TileMarkingInv P j T x s) :
    TileMarkingInv P j T x (failTrial P j T s) := by
  classical
  unfold TileMarkingInv
  intro y hy
  by_cases ha : s.2.attempt = 0
  · -- first trial fails: whole-tile marking
    have hmark : y ∈ s.1.pending ∨ (y ∈ tileSites (P.cover j) T ∧ y ∈ s.1.endpoint.active) := by
      have hy' : y ∈ (markTile (tileSites (P.cover j) T)
          ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1).pending := by
        by_cases hj : m / 2 < j
        · simpa [failTrial, ha, hj] using hy
        · simpa [failTrial, ha, hj] using hy
      rw [markTile] at hy'
      simp only at hy'
      rcases Finset.mem_union.mp hy' with hold | hnew
      · exact Or.inl hold
      · exact Or.inr (Finset.mem_inter.mp hnew)
    have hlatest : (failTrial P j T s).1.latest y =
        if y ∈ tileSites (P.cover j) T ∧ y ∈ s.1.endpoint.active then
          ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ else s.1.latest y := by
      by_cases hj : m / 2 < j <;> simp [failTrial, ha, hj, markTile]
    have hff : (failTrial P j T s).2.firstFail = true := by
      by_cases hj : m / 2 < j <;> simp [failTrial, ha, hj]
    by_cases hm : y ∈ tileSites (P.cover j) T ∧ y ∈ s.1.endpoint.active
    · right
      rw [hlatest, if_pos hm]
      exact ⟨rfl, hff, hm.1⟩
    · rcases hmark with hold | hnew
      · rcases h y hold with hfirst | hsecond
        · left
          refine ⟨hfirst.1, ?_⟩
          rw [hlatest, if_neg hm]
          exact hfirst.2
        · right
          rw [hlatest, if_neg hm]
          exact ⟨hsecond.1, hff, hsecond.2.2⟩
      · exact absurd hnew hm
  · -- retry fails: record unchanged, failure latched
    have hy' : y ∈ s.1.pending := by
      by_cases hj : m / 2 < j
      · simpa [failTrial, ha, hj] using hy
      · simpa [failTrial, ha, hj, trialScratch] using hy
    have hlatest : (failTrial P j T s).1.latest y = s.1.latest y := by
      by_cases hj : m / 2 < j <;> simp [failTrial, ha, hj]
    have hff : (failTrial P j T s).2.firstFail = true := by
      by_cases hj : m / 2 < j <;> simp [failTrial, ha, hj]
    rcases h y hy' with hfirst | hsecond
    · left
      exact ⟨hfirst.1, by rw [hlatest]; exact hfirst.2⟩
    · right
      exact ⟨by rw [hlatest]; exact hsecond.1, hff, hsecond.2.2⟩

theorem tileMarkingInv_scalarStep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ)
    (h : TileMarkingInv P j T x s) :
    TileMarkingInv P j T x (scalarStep P j T s i ζ) := by
  classical
  unfold scalarStep
  by_cases hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
  · simpa [hok, TileMarkingInv] using h
  · simpa [hok] using tileMarkingInv_failTrial P j T x s h

theorem tileMarkingInv_tileStep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (a : Answer (Torus d m)) (h : TileMarkingInv P j T x s) :
    TileMarkingInv P j T x (tileStep P j T s q a) := by
  unfold tileStep
  cases q with
  | trueDigit i k | auxiliary i | trueSuffix i k =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, TileMarkingInv] using h
    | some i => exact tileMarkingInv_scalarStep P j T x s i _ h
  | nextOrder o =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, TileMarkingInv] using h
    | some i => simpa [tileStep, hs, TileMarkingInv] using h
  | decision =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, commitTrial, TileMarkingInv] using h
    | some i => simpa [tileStep, hs, TileMarkingInv] using h

theorem tileMarkingStatement_proof : TileMarkingStatement := by
  intro d m P j T x s hreach
  have hinv : TileMarkingInv P j T x s := by
    induction hreach with
    | enter =>
      intro y' hy'
      have hpend : y' ∈ x.pending := by
        cases hab : x.aborted <;> simpa [tileBlock, hab] using hy'
      have hl : ((tileBlock P j T).enter x).1.latest y' = x.latest y' := by
        cases hab : x.aborted <;> simpa [tileBlock, hab]
      exact Or.inl ⟨hpend, hl⟩
    | @step s a hreach hnot ih =>
      have hu := tileBlock_update_running P j T s a hnot
      rw [hu]
      let s₀ := (s.1, logQuery (tileQuery P j T s) s.2)
      have hi₀ : TileMarkingInv P j T x s₀ := by
        simpa [TileMarkingInv, s₀, logQuery] using ih
      exact tileMarkingInv_tileStep P j T x s₀ (tileQuery P j T s) a hi₀
  intro hhalt y hy
  have hy' := hinv y (by simpa [tileBlock] using hy)
  simpa [tileBlock] using hy'

/-- **Tile query discipline (frozen contract).** -/
def TileQueryStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M),
    (∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false) →
    (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true →
    declaredFresh ((tileBlock P j T).exit (localState M (tileBlock P j T) x k ω)) ⊆
        declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((tileBlock P j T).exit (localState M (tileBlock P j T) x k ω)),
        z ∉ querySigns (Torus d m) ((tileBlock P j T).next (localState M (tileBlock P j T) x k' ω))

/-- **Tile pattern discipline (frozen contract).** -/
def TilePatternStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (x : RunRecord d m),
    (∀ z ∈ (tilePattern P j T x).signs,
      z ∈ declaredFresh x ∨ ∃ a ∈ tileAuxSet d m j T, z = Sum.inr a) ∧
    ∀ o ∈ (tilePattern P j T x).orders, o ∈ tileOrderSet j T

theorem tilePatternStatement_proof : TilePatternStatement := by
  intro d m P j T x
  constructor
  · intro z hz
    by_cases hab : x.aborted = true
    · simp [FreshPattern.signs, tilePattern, hab] at hz
    · have hab' : x.aborted = false := by cases h : x.aborted <;> simp_all
      rw [FreshPattern.signs] at hz
      rcases hz with htrue | haux
      · rcases htrue with ⟨i, hi, k, hk, rfl⟩
        have hmem : i ∈ (((TS P j T ∩ x.endpoint.active) \ x.pending) \ x.terminal) := by
          simpa [tilePattern, hab'] using hi
        have hpend : i ∉ x.pending := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hmem).1).2
        have hterm : i ∉ x.terminal := (Finset.mem_sdiff.mp hmem).2
        have hk' : x.prefixLength i ≤ k := by simpa [tilePattern, hab'] using hk
        left
        exact ⟨hab', i, k, rfl, hpend, hterm, hk'⟩
      · rcases haux with ⟨a, ha, rfl⟩
        have ha' : a ∈ (((TS P j T ∩ x.endpoint.active) ∩ x.pending) \ x.terminal).image
            (tileAuxIndex j T 0) := by
          simpa [tilePattern, hab'] using ha
        rcases Finset.mem_image.mp ha' with ⟨i, hi, rfl⟩
        right
        exact ⟨_, ⟨0, i, rfl⟩, rfl⟩
  · intro o ho
    have ho' : o ∈ ({tileOrderIndex j T 0} : Finset ℕ) := by
      cases hab : x.aborted <;> simpa [tilePattern, hab] using ho
    have heq : o = tileOrderIndex j T 0 := Finset.mem_singleton.mp ho'
    exact ⟨0, heq⟩

/-- **Tile abort discipline (frozen contract, added 2026-10-14 00:00 UTC).** A tile block
aborts only at a first-trial failure after the cutoff (05:519–521): consumer
`blockRun_of_disciplines.habort` (late slots). -/
def TileAbortStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x : RunRecord d m) (s : RunRecord d m × TileScratch d m),
    BlockReach (tileBlock P j T) x s → (tileBlock P j T).halted s = true →
    ((tileBlock P j T).exit s).aborted = true →
    x.aborted = true ∨ ((tileBlock P j T).firstFail s = true ∧ m / 2 < j)

/-- Abort invariant: a reachable record is aborted only if entered aborted or via a
first-trial failure after the cutoff. -/
def TileAbortInv (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x : RunRecord d m) (s : RunRecord d m × TileScratch d m) : Prop :=
  s.1.aborted = true → x.aborted = true ∨ (s.2.firstFail = true ∧ m / 2 < j)

theorem tileAbortInv_failTrial (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (h : TileAbortInv P j T x s) :
    TileAbortInv P j T x (failTrial P j T s) := by
  classical
  unfold TileAbortInv
  intro hab
  by_cases hj : m / 2 < j
  · right
    exact ⟨by simp [failTrial, hj], hj⟩
  · have hs : s.1.aborted = true := by
      by_cases ha : s.2.attempt = 0
      · simpa [failTrial, ha, hj, markTile] using hab
      · simpa [failTrial, ha, hj] using hab
    rcases h hs with hx | ⟨hff, hcut⟩
    · exact Or.inl hx
    · exact absurd hcut (by omega)

theorem tileAbortInv_scalarStep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ)
    (h : TileAbortInv P j T x s) :
    TileAbortInv P j T x (scalarStep P j T s i ζ) := by
  classical
  unfold scalarStep
  by_cases hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
  · simpa [hok, TileAbortInv] using h
  · simpa [hok] using tileAbortInv_failTrial P j T x s h

theorem tileAbortInv_tileStep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (a : Answer (Torus d m)) (h : TileAbortInv P j T x s) :
    TileAbortInv P j T x (tileStep P j T s q a) := by
  unfold tileStep
  cases q with
  | trueDigit i k | auxiliary i | trueSuffix i k =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, TileAbortInv] using h
    | some i => exact tileAbortInv_scalarStep P j T x s i _ h
  | nextOrder o =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, TileAbortInv] using h
    | some i => simpa [tileStep, hs, TileAbortInv] using h
  | decision =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, commitTrial, TileAbortInv] using h
    | some i => simpa [tileStep, hs, TileAbortInv] using h

theorem tileAbortStatement_proof : TileAbortStatement := by
  intro d m P j T x s hreach
  have hinv : TileAbortInv P j T x s := by
    induction hreach with
    | enter =>
      intro hab'
      cases hbx : x.aborted with
      | true => exact Or.inl rfl
      | false =>
        have : ((tileBlock P j T).enter x).1.aborted = x.aborted := by
          cases habx : x.aborted <;> simp [tileBlock, habx]
        rw [this] at hab'
        simp [hbx] at hab'
    | @step s a hreach hnot ih =>
      have hu := tileBlock_update_running P j T s a hnot
      rw [hu]
      let s₀ := (s.1, logQuery (tileQuery P j T s) s.2)
      have hi₀ : TileAbortInv P j T x s₀ := by
        simpa [TileAbortInv, s₀, logQuery] using ih
      exact tileAbortInv_tileStep P j T x s₀ (tileQuery P j T s) a hi₀
  intro hhalt hab
  have h := hinv (by simpa [tileBlock] using hab)
  simpa [tileBlock] using h

open Classical in
/-- The read pattern of the first `k + 1` states of a tile block (all trials up to number
`k`): the non-pending, non-terminal active sites of the tile from their prefix lengths, the
auxiliary families `a ≤ k` of the tile's sites, and the orders `π_{j,T,a}`, `a ≤ k`
(added 2026-10-14 00:20 UTC; consumer `all_blocks_reached_of_inv`, ReachedInv.lean). -/
def tileHaltPattern {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (k : ℕ) (x : RunRecord d m) : FreshPattern (Torus d m) :=
  if x.aborted then ⟨∅, x.prefixLength, ∅, ∅⟩ else
  { sites := ((tileSites (P.cover j) T ∩ x.endpoint.active) \ x.pending) \ x.terminal
    height := x.prefixLength
    aux := ((Finset.range (k + 1)) ×ˢ tileSites (P.cover j) T).image
      (fun p => tileAuxIndex (d := d) (m := m) j T p.1 p.2)
    orders := (Finset.range (k + 1)).image (tileOrderIndex j T) }

/-- **Tile halting-pattern discipline (frozen contract, added 2026-10-14 00:20 UTC).** The
event "the tile block has not halted within its first `k + 1` states" depends only on
`tileHaltPattern … k x`, which is measurable in the record. -/
def TileHaltPatternStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (k : ℕ),
    Measurable (tileHaltPattern P j T k) ∧
    MeasurableSet {p : RunRecord d m × RandomSources (Torus d m) M |
      p.2 ∈ notHalted M (tileBlock P j T) p.1 k} ∧
    ∀ x : RunRecord d m, DependsOnly (Torus d m) (M := M) (tileHaltPattern P j T k x)
      (notHalted M (tileBlock P j T) x k)

/-- Measurability of the halting pattern in the record (fixed `k`; `aux`/`orders` are
constant in the record). Mirrors `tilePattern_measurable`. -/
theorem tileHaltPattern_measurable (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (k : ℕ) :
    Measurable (tileHaltPattern P j T k) := by
  have hx := RecordMeas.of_measurable (measurable_id (α := RunRecord d m))
  refine measurable_of_factor
    (hx.aborted.prodMk (hx.active.prodMk
      (hx.sites.fst.prodMk (hx.pending.prodMk hx.prefixLength)))) _ ?_
  intro x x' h
  simp only [Prod.mk.injEq, id] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have h1' := finsetCode_injective h1
  have h2' := finsetCode_injective h2
  have h3' := finsetCode_injective h3
  unfold tileHaltPattern
  rw [h0, h1', h2', h3', h4]

open AndersonAC.AgentS78.MachineRunProof in
/-- Joint measurability of the not-halted set (fixed `k`; finite conjunction over
`k' ≤ k` of halted-false, via the proved `MachineRunStatement`). -/
theorem tileHaltMeasurableSet (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ) :
    MeasurableSet {p : RunRecord d m × RandomSources (Torus d m) M |
      p.2 ∈ notHalted M (tileBlock P j T) p.1 k} := by
  classical
  have hmeas := tileBlock_measurable P j T
  obtain ⟨_, hQ, hrunQ⟩ := machineRun_proof (Torus d m) M
    (RunRecord d m × TileScratch d m) (tileBlock P j T).next hmeas.next
    (tileBlock P j T).update hmeas.update
  -- each `k'` gives a measurable halted-false set; intersect finitely many
  have hone : ∀ k' : ℕ, MeasurableSet {p : RunRecord d m × RandomSources (Torus d m) M |
      (tileBlock P j T).halted (localState M (tileBlock P j T) p.1 k' p.2) = false} := by
    intro k'
    have hjoint : Measurable (fun p : RunRecord d m × RandomSources (Torus d m) M =>
        localState M (tileBlock P j T) p.1 k' p.2) := by
      have hj := hrunQ (RunRecord d m) (fun x => (tileBlock P j T).enter x) hmeas.enter k'
      simpa [localState] using hj
    have hhalt : Measurable (fun p : RunRecord d m × RandomSources (Torus d m) M =>
        (tileBlock P j T).halted (localState M (tileBlock P j T) p.1 k' p.2)) :=
      hmeas.halted.comp hjoint
    exact hhalt (measurableSet_singleton false)
  have heq : {p : RunRecord d m × RandomSources (Torus d m) M |
      p.2 ∈ notHalted M (tileBlock P j T) p.1 k} =
      ⋂ k' ∈ Finset.range (k + 1), {p : RunRecord d m × RandomSources (Torus d m) M |
        (tileBlock P j T).halted (localState M (tileBlock P j T) p.1 k' p.2) = false} := by
    ext ⟨x, ω⟩
    simp [notHalted, tileBlock, Finset.mem_range]
  rw [heq]
  exact MeasurableSet.biInter (Finset.range (k + 1)).countable_toSet fun k' _ => hone k'

/-- Single-step attempt bound: an update raises `attempt` by at most one
(`StepShape`; `logQuery` preserves it). -/
theorem tileUpdate_attempt_le (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) :
    ((tileBlock P j T).update s a).2.attempt ≤ s.2.attempt + 1 := by
  classical
  by_cases hh : s.2.halted = true
  · simp [tileBlock_update_halted P j T s a hh]
  · have hf : s.2.halted = false := by simpa using hh
    rw [tileBlock_update_running P j T s a hf]
    have hlog : (s.1, logQuery (tileQuery P j T s) s.2).2.attempt = s.2.attempt := by
      simp [logQuery]
    rcases (tileStep_keeps P j T (s.1, logQuery (tileQuery P j T s) s.2)
      (tileQuery P j T s) a).2 with
      ⟨-, hEq, -, -⟩ | ⟨-, hEq, -⟩ | ⟨hPlus, -, -⟩
    · omega
    · omega
    · omega

/-- Attempt never exceeds the step count (each step raises it by at most one,
via `StepShape`; `logQuery` preserves it). -/
theorem tileAttempt_le_steps (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (ω : RandomSources (Torus d m) M) :
    ∀ n, (localState M (tileBlock P j T) x n ω).2.attempt ≤ n := by
  intro n
  induction n with
  | zero =>
    have h0 : ((tileBlock P j T).enter x).2.attempt = 0 := by
      cases hab : x.aborted <;> simp [tileBlock, hab, initScratch]
    simpa [localState_zero] using h0
  | succ n ih =>
    have hsu := localState_succ M (tileBlock P j T) x n ω
    by_cases hh : (localState M (tileBlock P j T) x n ω).2.halted = true
    · have heq : localState M (tileBlock P j T) x (n + 1) ω =
          localState M (tileBlock P j T) x n ω := by
        rw [hsu, tileBlock_update_halted P j T _ _ hh]
      have hatt : (localState M (tileBlock P j T) x (n + 1) ω).2.attempt =
          (localState M (tileBlock P j T) x n ω).2.attempt := congrArg (·.2.attempt) heq
      omega
    · have hstep : (localState M (tileBlock P j T) x n ω).2.attempt ≤ n := ih
      have hsu2 := localState_succ M (tileBlock P j T) x n ω
      rw [hsu2]
      have hle : ((tileBlock P j T).update (localState M (tileBlock P j T) x n ω)
          (localAnswer (Torus d m) M
            (machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
              (tileBlock P j T).update n ω).2
            ((tileBlock P j T).next (localState M (tileBlock P j T) x n ω)) ω)).2.attempt ≤
          (localState M (tileBlock P j T) x n ω).2.attempt + 1 :=
        tileUpdate_attempt_le P j T _ _
      omega

/-- Monotonicity invariants for the query discipline: pending/terminal only grow,
prefix lengths only grow, abort never clears, the active set never changes. -/
def TileFreshMono (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x : RunRecord d m) (s : RunRecord d m × TileScratch d m) : Prop :=
  x.pending ⊆ s.1.pending ∧ x.terminal ⊆ s.1.terminal ∧
    (∀ i, x.prefixLength i ≤ s.1.prefixLength i) ∧
    (x.aborted = true → s.1.aborted = true) ∧ s.1.endpoint.active = x.endpoint.active

theorem tileFreshMono_failTrial (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (h : TileFreshMono P j T x s) :
    TileFreshMono P j T x (failTrial P j T s) := by
  classical
  obtain ⟨hpend, hterm, hpre, habort, hactive⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ s.1.pending := hpend hy
    by_cases ha : s.2.attempt = 0
    · have hmem : y ∈ (markTile (TS P j T)
          ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1).pending :=
        Finset.mem_union.mpr (Or.inl hy')
      have heq : (failTrial P j T s).1.pending = (markTile (TS P j T)
          ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1).pending := by
        by_cases hj : m / 2 < j <;> simp [failTrial, ha, hj]
      rw [heq]
      exact hmem
    · have heq : (failTrial P j T s).1.pending = s.1.pending := by
        by_cases hj : m / 2 < j <;> simp [failTrial, ha, hj]
      rw [heq]
      exact hy'
  · intro y hy
    have hy' : y ∈ s.1.terminal := hterm hy
    have heq : (failTrial P j T s).1.terminal = s.1.terminal := by
      by_cases ha : s.2.attempt = 0 <;> by_cases hj : m / 2 < j <;>
        simp [failTrial, ha, hj, markTile]
    rw [heq]
    exact hy'
  · intro i
    have hi := hpre i
    have heq : (failTrial P j T s).1.prefixLength = s.1.prefixLength := by
      by_cases ha : s.2.attempt = 0 <;> by_cases hj : m / 2 < j <;>
        simp [failTrial, ha, hj, markTile]
    rw [heq]
    exact hi
  · intro habx
    have hs := habort habx
    by_cases hj : m / 2 < j
    · have heq : (failTrial P j T s).1.aborted = true := by
        by_cases ha : s.2.attempt = 0 <;> simp [failTrial, ha, hj]
      simp [heq]
    · have heq : (failTrial P j T s).1.aborted = s.1.aborted := by
        by_cases ha : s.2.attempt = 0 <;> simp [failTrial, ha, hj, markTile]
      rw [heq]
      exact hs
  · have heq : (failTrial P j T s).1.endpoint.active = s.1.endpoint.active := by
      by_cases ha : s.2.attempt = 0 <;> by_cases hj : m / 2 < j <;>
        simp [failTrial, ha, hj, markTile]
    rw [heq]
    exact hactive

theorem tileFreshMono_scalarStep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ)
    (h : TileFreshMono P j T x s) :
    TileFreshMono P j T x (scalarStep P j T s i ζ) := by
  classical
  unfold scalarStep
  by_cases hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
  · simpa [hok, TileFreshMono] using h
  · simpa [hok] using tileFreshMono_failTrial P j T x s h

theorem tileFreshMono_tileStep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (a : Answer (Torus d m)) (h : TileFreshMono P j T x s) :
    TileFreshMono P j T x (tileStep P j T s q a) := by
  unfold tileStep
  cases q with
  | trueDigit i k | auxiliary i | trueSuffix i k =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, TileFreshMono] using h
    | some i => exact tileFreshMono_scalarStep P j T x s i _ h
  | nextOrder o =>
    cases hs : s.2.site with
    | none => simpa [tileStep, hs, TileFreshMono] using h
    | some i => simpa [tileStep, hs, TileFreshMono] using h
  | decision =>
    cases hs : s.2.site with
    | none =>
      obtain ⟨hpend, hterm, hpre, habort, hactive⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ s.1.pending := hpend hy
        simpa [tileStep, hs, commitTrial] using hy'
      · intro y hy
        have hy' : y ∈ s.1.terminal := hterm hy
        by_cases hfs : IsFinalSweep m j
        · have hdec : decide (IsFinalSweep m j) = true := decide_eq_true hfs
          have hsub : s.1.terminal ⊆
              (commitTrial s.1 s.2 (decide (IsFinalSweep m j))).terminal := by
            simp [commitTrial, hdec]
          exact hsub hy'
        · have hdec : decide (IsFinalSweep m j) = false := decide_eq_false hfs
          simpa [tileStep, hs, commitTrial, hdec] using hy'
      · intro i
        have hi := hpre i
        have hle : s.1.prefixLength i ≤
            (commitTrial s.1 s.2 (decide (IsFinalSweep m j))).prefixLength i := by
          simp only [commitTrial]
          exact Nat.le_add_right _ _
        exact le_trans hi hle
      · intro habx
        have hsab := habort habx
        simpa [tileStep, hs, commitTrial] using hsab
      · simpa [tileStep, hs, commitTrial] using hactive
    | some i => simpa [tileStep, hs, TileFreshMono] using h

theorem tileFreshMono_reach (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (hreach : BlockReach (tileBlock P j T) x s) :
    TileFreshMono P j T x s := by
  induction hreach with
  | enter =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      cases hab : x.aborted <;> simpa [tileBlock, hab] using hy
    · intro y hy
      cases hab : x.aborted <;> simpa [tileBlock, hab] using hy
    · intro i
      cases hab : x.aborted <;>
        simpa [tileBlock, hab] using (le_rfl : x.prefixLength i ≤ x.prefixLength i)
    · intro habx
      cases hab : x.aborted <;> simp_all [tileBlock, hab]
    · cases hab : x.aborted <;> simp [tileBlock, hab]
  | @step s a hreach hnot ih =>
    have hu := tileBlock_update_running P j T s a hnot
    rw [hu]
    let s₀ := (s.1, logQuery (tileQuery P j T s) s.2)
    have hi₀ : TileFreshMono P j T x s₀ := by
      simpa [TileFreshMono, s₀, logQuery] using ih
    exact tileFreshMono_tileStep P j T x s₀ (tileQuery P j T s) a hi₀

/-- Shrinking half of the query discipline, via `declaredFresh_mono`. -/
theorem tileQueryShrink (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hk : ∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false) :
    declaredFresh ((tileBlock P j T).exit (localState M (tileBlock P j T) x k ω)) ⊆
      declaredFresh x := by
  have hreach : BlockReach (tileBlock P j T) x (localState M (tileBlock P j T) x k ω) :=
    localState_reach M (tileBlock P j T) x ω k hk
  have hmono := tileFreshMono_reach P j T x _ hreach
  obtain ⟨hpend, hterm, hpre, habort, -⟩ := hmono
  simp only [tileBlock] at hpend hterm hpre habort ⊢
  apply declaredFresh_mono
  · intro hab
    cases hxb : x.aborted with
    | true =>
      have hs := habort hxb
      simp [hs] at hab
    | false => rfl
  · intro hab i hnp hnt
    refine ⟨fun hm => hnp (hpend hm), fun hm => hnt (hterm hm), hpre i⟩

/-- Single-step pending monotonicity: an update never drops pending sites. -/
theorem tileUpdate_pend_mono (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) :
    s.1.pending ⊆ ((tileBlock P j T).update s a).1.pending := by
  classical
  by_cases hh : s.2.halted = true
  · simp [tileBlock_update_halted P j T s a hh]
  · have hf : s.2.halted = false := by simpa using hh
    rw [tileBlock_update_running P j T s a hf]
    set sL := (s.1, logQuery (tileQuery P j T s) s.2) with hsL
    have hrec : sL.1 = s.1 := rfl
    have hrefl : TileFreshMono P j T sL.1 sL :=
      ⟨fun y hy => hy, fun y hy => hy, fun i => le_rfl, fun h => h, rfl⟩
    have hmono := tileFreshMono_tileStep P j T sL.1 sL (tileQuery P j T s) a hrefl
    simpa [hrec] using hmono.1

/-- Pending sites propagate along the local run. -/
theorem tileLocal_pend_mono (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (ω : RandomSources (Torus d m) M) :
    ∀ n m : ℕ, n ≤ m → (localState M (tileBlock P j T) x n ω).1.pending ⊆
      (localState M (tileBlock P j T) x m ω).1.pending := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact fun y hy => hy
  | succ m hle ih =>
    have hstep : (localState M (tileBlock P j T) x m ω).1.pending ⊆
        (localState M (tileBlock P j T) x (m + 1) ω).1.pending := by
      have hsu := localState_succ M (tileBlock P j T) x m ω
      rw [hsu]
      exact tileUpdate_pend_mono P j T _ _
    exact fun y hy => hstep (ih hy)

/-- Single-step `firstFail` preservation: once true it stays true. -/
theorem tileUpdate_firstFail_mono (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) (h : s.2.firstFail = true) :
    ((tileBlock P j T).update s a).2.firstFail = true := by
  classical
  by_cases hh : s.2.halted = true
  · simp [tileBlock_update_halted P j T s a hh, h]
  · have hf : s.2.halted = false := by simpa using hh
    rw [tileBlock_update_running P j T s a hf]
    set sL := (s.1, logQuery (tileQuery P j T s) s.2) with hsL
    have hff : sL.2.firstFail = true := by simpa [hsL, logQuery] using h
    rcases (tileStep_keeps P j T sL (tileQuery P j T s) a).2 with
      ⟨-, -, hEq, -⟩ | ⟨-, -, himp⟩ | ⟨-, hTrue, -⟩
    · simpa [hEq] using hff
    · exact himp hff
    · exact hTrue

/-- `firstFail` propagates along the local run. -/
theorem tileLocal_firstFail_mono (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (ω : RandomSources (Torus d m) M) :
    ∀ n m : ℕ, n ≤ m → (localState M (tileBlock P j T) x n ω).2.firstFail = true →
      (localState M (tileBlock P j T) x m ω).2.firstFail = true := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact id
  | succ m hle ih =>
    intro htrue
    have hsu := localState_succ M (tileBlock P j T) x m ω
    have hmid := ih htrue
    rw [hsu]
    exact tileUpdate_firstFail_mono P j T _ _ hmid

/-- Single-step outcome for a first-trial active site: an update either keeps `firstFail`
false or marks the site pending (via a first-trial failure). -/
theorem tileStep_mark_or_keep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) (i : Torus d m)
    (hrun : s.2.halted = false) (hff : s.2.firstFail = false) (ha0 : s.2.attempt = 0)
    (hts : i ∈ TS P j T) (hact : i ∈ s.1.endpoint.active) :
    ((tileBlock P j T).update s a).2.firstFail = false ∨
      i ∈ ((tileBlock P j T).update s a).1.pending := by
  classical
  rw [tileBlock_update_running P j T s a hrun]
  set sL := (s.1, logQuery (tileQuery P j T s) s.2) with hsL
  have hrec : sL.1 = s.1 := rfl
  have ha0L : sL.2.attempt = 0 := by simpa [hsL, logQuery] using ha0
  have hffL : sL.2.firstFail = false := by simpa [hsL, logQuery] using hff
  have hactL : i ∈ sL.1.endpoint.active := by simpa [hrec] using hact
  -- failure from attempt 0 marks `i`; reused in the scalar-fail subcases
  have hmark : i ∈ (failTrial P j T sL).1.pending := by
    have heq : (failTrial P j T sL).1.pending = (markTile (TS P j T)
        ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ sL.1).pending := by
      by_cases hj : m / 2 < j <;> simp [failTrial, ha0L, hj]
    rw [heq]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hts, hactL⟩))
  cases hq : tileQuery P j T s with
  | nextOrder o =>
    cases hs : sL.2.site with
    | none =>
      have heq : (tileStep P j T sL (Query.nextOrder o) a).2.firstFail = sL.2.firstFail := by
        simp [tileStep, hs]
      exact Or.inl (heq.trans hffL)
    | some ii =>
      have heq : (tileStep P j T sL (Query.nextOrder o) a).2.firstFail = sL.2.firstFail := by
        simp [tileStep, hs]
      exact Or.inl (heq.trans hffL)
  | decision =>
    cases hs : sL.2.site with
    | none =>
      have heq : (tileStep P j T sL Query.decision a).2.firstFail = sL.2.firstFail := by
        simp [tileStep, hs, commitTrial]
      exact Or.inl (heq.trans hffL)
    | some ii =>
      have heq : (tileStep P j T sL Query.decision a).2.firstFail = sL.2.firstFail := by
        simp [tileStep, hs]
      exact Or.inl (heq.trans hffL)
  | trueDigit ii k =>
    cases hs : sL.2.site with
    | none =>
      have heq : (tileStep P j T sL (Query.trueDigit ii k) a).2.firstFail = sL.2.firstFail := by
        simp [tileStep, hs]
      exact Or.inl (heq.trans hffL)
    | some jj =>
      have hred : tileStep P j T sL (Query.trueDigit ii k) a =
          scalarStep P j T sL jj (tileIncrement P j (Query.trueDigit ii k) a) := by
        simp [tileStep, hs]
      rw [hred]
      by_cases hok : trialOk P j T sL.1
          (extendSeq sL.2.seq
            (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
              (sL.2.seq.state sL.2.seq.length) (jj, false)
              (tileIncrement P j (Query.trueDigit ii k) a / Real.sqrt (sweepW P.u m j)))
            (jj, false)
            (tileIncrement P j (Query.trueDigit ii k) a / Real.sqrt (sweepW P.u m j)))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (jj, false)
            (tileIncrement P j (Query.trueDigit ii k) a / Real.sqrt (sweepW P.u m j)))
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueDigit ii k) a)).2.firstFail = sL.2.firstFail := by
          simp [scalarStep, hok]
        exact Or.inl (heq.trans hffL)
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueDigit ii k) a)).1.pending =
            (failTrial P j T sL).1.pending := by simp [scalarStep, hok]
        exact Or.inr (heq ▸ hmark)
  | auxiliary k =>
    cases hs : sL.2.site with
    | none =>
      have heq : (tileStep P j T sL (Query.auxiliary k) a).2.firstFail = sL.2.firstFail := by
        simp [tileStep, hs]
      exact Or.inl (heq.trans hffL)
    | some jj =>
      have hred : tileStep P j T sL (Query.auxiliary k) a =
          scalarStep P j T sL jj (tileIncrement P j (Query.auxiliary k) a) := by
        simp [tileStep, hs]
      rw [hred]
      by_cases hok : trialOk P j T sL.1
          (extendSeq sL.2.seq
            (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
              (sL.2.seq.state sL.2.seq.length) (jj, false)
              (tileIncrement P j (Query.auxiliary k) a / Real.sqrt (sweepW P.u m j)))
            (jj, false)
            (tileIncrement P j (Query.auxiliary k) a / Real.sqrt (sweepW P.u m j)))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (jj, false)
            (tileIncrement P j (Query.auxiliary k) a / Real.sqrt (sweepW P.u m j)))
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.auxiliary k) a)).2.firstFail = sL.2.firstFail := by
          simp [scalarStep, hok]
        exact Or.inl (heq.trans hffL)
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.auxiliary k) a)).1.pending =
            (failTrial P j T sL).1.pending := by simp [scalarStep, hok]
        exact Or.inr (heq ▸ hmark)
  | trueSuffix ii k =>
    cases hs : sL.2.site with
    | none =>
      have heq : (tileStep P j T sL (Query.trueSuffix ii k) a).2.firstFail = sL.2.firstFail := by
        simp [tileStep, hs]
      exact Or.inl (heq.trans hffL)
    | some jj =>
      have hred : tileStep P j T sL (Query.trueSuffix ii k) a =
          scalarStep P j T sL jj (tileIncrement P j (Query.trueSuffix ii k) a) := by
        simp [tileStep, hs]
      rw [hred]
      by_cases hok : trialOk P j T sL.1
          (extendSeq sL.2.seq
            (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
              (sL.2.seq.state sL.2.seq.length) (jj, false)
              (tileIncrement P j (Query.trueSuffix ii k) a / Real.sqrt (sweepW P.u m j)))
            (jj, false)
            (tileIncrement P j (Query.trueSuffix ii k) a / Real.sqrt (sweepW P.u m j)))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (jj, false)
            (tileIncrement P j (Query.trueSuffix ii k) a / Real.sqrt (sweepW P.u m j)))
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueSuffix ii k) a)).2.firstFail = sL.2.firstFail := by
          simp [scalarStep, hok]
        exact Or.inl (heq.trans hffL)
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueSuffix ii k) a)).1.pending =
            (failTrial P j T sL).1.pending := by simp [scalarStep, hok]
        exact Or.inr (heq ▸ hmark)

/-- A true query's site becomes pending at exit if any failure occurs: the first failure
is from attempt 0 (via `FirstTrialInv`), so whole-tile marking covers the site, and
pending propagates to exit. -/
theorem tileTrueQuery_fail_pending (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k k' : ℕ) (ω : RandomSources (Torus d m) M) (i : Torus d m)
    (hk : ∀ l < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x l ω) = false)
    (hk' : k' < k)
    (h1 : activeIn P j T (localState M (tileBlock P j T) x k' ω).1 i)
    (h2 : usesTrue (localState M (tileBlock P j T) x k' ω) i)
    (hffE : (localState M (tileBlock P j T) x k ω).2.firstFail = true) :
    i ∈ (localState M (tileBlock P j T) x k ω).1.pending := by
  classical
  -- query state is a running first trial with the entering record
  have hrunQ : (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false :=
    hk k' hk'
  obtain ⟨ha0Q, hnpQ⟩ := h2
  have hftQ := localState_induct M (tileBlock P j T) x (FirstTrialInv x)
    (firstTrialInv_enter P j T x)
    (fun s a hs => firstTrialInv_update P j T x s a hs) k' ω
  have hSQx : (localState M (tileBlock P j T) x k' ω).1 = x := hftQ.2 ha0Q hrunQ
  obtain ⟨hts, hactQ, -⟩ := h1
  have hactX : i ∈ x.endpoint.active := hSQx ▸ hactQ
  -- entry has no failure
  have hff0 : (localState M (tileBlock P j T) x 0 ω).2.firstFail = false := by
    cases hab : x.aborted <;> simp [localState_zero, tileBlock, hab, initScratch]
  -- first-true step
  have hex : ∃ m, (localState M (tileBlock P j T) x m ω).2.firstFail = true := ⟨k, hffE⟩
  set m0 := Nat.find hex with hm0
  have hspec : (localState M (tileBlock P j T) x m0 ω).2.firstFail = true :=
    Nat.find_spec hex
  have hm0k : m0 ≤ k := Nat.find_min' hex hffE
  have hm0pos : 0 < m0 := by
    by_contra hcon
    have hz : m0 = 0 := by omega
    rw [hz] at hspec
    simp [hff0] at hspec
  have hlt : m0 - 1 < m0 := by omega
  have hprevFalse : (localState M (tileBlock P j T) x (m0 - 1) ω).2.firstFail = false := by
    have hne := Nat.find_min hex hlt
    cases hfb : (localState M (tileBlock P j T) x (m0 - 1) ω).2.firstFail with
    | true => simp [hfb] at hne
    | false => rfl
  have hprevLt : m0 - 1 < k := by omega
  have hprevRun : (tileBlock P j T).halted (localState M (tileBlock P j T) x (m0 - 1) ω)
      = false := hk (m0 - 1) hprevLt
  -- attempt is still 0 just before the first failure
  have hftPrev := localState_induct M (tileBlock P j T) x (FirstTrialInv x)
    (firstTrialInv_enter P j T x)
    (fun s a hs => firstTrialInv_update P j T x s a hs) (m0 - 1) ω
  have ha0Prev : (localState M (tileBlock P j T) x (m0 - 1) ω).2.attempt = 0 := by
    by_contra hne
    have htrue := hftPrev.1 hne
    cases hfb : (localState M (tileBlock P j T) x (m0 - 1) ω).2.firstFail with
    | true => simp [hfb] at hprevFalse
    | false => simp [hfb] at htrue
  -- active set is constant along the run
  have hrchPrev : BlockReach (tileBlock P j T) x (localState M (tileBlock P j T) x (m0 - 1) ω) :=
    localState_reach M (tileBlock P j T) x ω (m0 - 1)
      (fun l hl => hk l (lt_of_lt_of_le hl (Nat.le_trans (Nat.sub_le m0 1) hm0k)))
  have hmonoPrev := tileFreshMono_reach P j T x _ hrchPrev
  have hactPrev : i ∈ (localState M (tileBlock P j T) x (m0 - 1) ω).1.endpoint.active := by
    rw [hmonoPrev.2.2.2.2]
    exact hactX
  -- the first-failure step marks `i`
  have hm0eq : m0 = (m0 - 1) + 1 := by omega
  have hsu := localState_succ M (tileBlock P j T) x (m0 - 1) ω
  have hstep := tileStep_mark_or_keep P j T
    (localState M (tileBlock P j T) x (m0 - 1) ω)
    (localAnswer (Torus d m) M
      (machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update (m0 - 1) ω).2
      ((tileBlock P j T).next (localState M (tileBlock P j T) x (m0 - 1) ω)) ω)
    i hprevRun hprevFalse ha0Prev hts hactPrev
  rw [← hm0eq] at hsu
  -- `hsu : localState m0 = update ...`; rewrite the step outcome to `m0`
  rw [← hsu] at hstep
  rcases hstep with hkeep | hmark
  · -- kept false contradicts first-true at `m0`
    rw [hkeep] at hspec
    simp at hspec
  · -- marked: propagate to exit
    exact tileLocal_pend_mono P j T M x ω m0 k hm0k hmark

/-- All `firstFail`s before exit are false when exit is false (contrapositive of mono). -/
theorem tileAllFalse_of_exitFalse (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hffE : (localState M (tileBlock P j T) x k ω).2.firstFail = false) :
    ∀ n ≤ k, (localState M (tileBlock P j T) x n ω).2.firstFail = false := by
  intro n hn
  by_contra hcon
  have htrue : (localState M (tileBlock P j T) x n ω).2.firstFail = true := by
    cases hfb : (localState M (tileBlock P j T) x n ω).2.firstFail with
    | true => rfl
    | false => simp [hfb] at hcon
  have hprop := tileLocal_firstFail_mono P j T M x ω n k hn htrue
  simp [hprop] at hffE

/-- A true query's site is marked consumed on a non-failing update. Takes the query
shape from `activeIn`/`usesTrue`/site (digit vs suffix distinguished by the sweep only
for the query value, not for setting `consumed`, which uses `usesTrue` in both cases). -/
theorem tileConsumed_set_of_true (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) (i : Torus d m)
    (hrun : s.2.halted = false) (hsite : s.2.site = some i)
    (h1 : activeIn P j T s.1 i) (hut : usesTrue s i)
    (hUpdFalse : ((tileBlock P j T).update s a).2.firstFail = false) :
    ((tileBlock P j T).update s a).2.consumed i = true := by
  classical
  rw [tileBlock_update_running P j T s a hrun]
  set sL := (s.1, logQuery (tileQuery P j T s) s.2) with hsL
  have hrec : sL.1 = s.1 := rfl
  have hsiteL : sL.2.site = some i := by simpa [hsL, logQuery] using hsite
  have h1L : activeIn P j T sL.1 i := by simpa [hrec] using h1
  -- the query is a true query (digit or suffix); both go to `scalarStep`
  have hqScalar : tileQuery P j T s =
      Query.trueDigit i (s.1.prefixLength i) ∨
      tileQuery P j T s = Query.trueSuffix i (s.1.prefixLength i) := by
    by_cases hfin : IsFinalSweep m j
    · right
      simp [tileQuery, hsite, h1, hut, hfin]
    · left
      simp [tileQuery, hsite, h1, hut, hfin]
  obtain ⟨ha0, hnp⟩ := hut
  have ha0L : sL.2.attempt = 0 := by simpa [hsL, logQuery] using ha0
  have hnpL : i ∉ sL.1.pending := by simpa [hrec] using hnp
  have hutL : usesTrue sL i := ⟨ha0L, hnpL⟩
  rcases hqScalar with hqD | hqS
  · -- digit case
    have hred : tileStep P j T sL (tileQuery P j T s) a =
        scalarStep P j T sL i (tileIncrement P j (tileQuery P j T s) a) := by
      rw [hqD]
      simp [tileStep, hsiteL]
    rw [hred]
    by_cases hok : trialOk P j T sL.1
        (extendSeq sL.2.seq
          (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (i, false)
            (tileIncrement P j (tileQuery P j T s) a / Real.sqrt (sweepW P.u m j)))
          (i, false)
          (tileIncrement P j (tileQuery P j T s) a / Real.sqrt (sweepW P.u m j)))
        (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
          (sL.2.seq.state sL.2.seq.length) (i, false)
          (tileIncrement P j (tileQuery P j T s) a / Real.sqrt (sweepW P.u m j)))
    · have hdec : decide (usesTrue sL i) = true := decide_eq_true hutL
      have heq : (scalarStep P j T sL i
          (tileIncrement P j (tileQuery P j T s) a)).2.consumed =
          Function.update sL.2.consumed i true := by
        simp [scalarStep, hok, hdec]
      rw [heq]
      simp
    · -- failure would set `firstFail`, contradicting `hUpdFalse`
      have htrue : (scalarStep P j T sL i
          (tileIncrement P j (tileQuery P j T s) a)).2.firstFail = true := by
        have heq : (scalarStep P j T sL i
            (tileIncrement P j (tileQuery P j T s) a)).2.firstFail =
            (failTrial P j T sL).2.firstFail := by simp [scalarStep, hok]
        rw [heq]
        by_cases ha : sL.2.attempt = 0 <;> by_cases hj : m / 2 < j <;>
          simp [failTrial, ha, hj]
      have hUpdTrue : ((tileBlock P j T).update s a).2.firstFail = true := by
        rw [tileBlock_update_running P j T s a hrun, ← hsL, hred]
        exact htrue
      simp [hUpdTrue] at hUpdFalse
  · -- suffix case (same setting via `usesTrue`)
    have hred : tileStep P j T sL (tileQuery P j T s) a =
        scalarStep P j T sL i (tileIncrement P j (tileQuery P j T s) a) := by
      rw [hqS]
      simp [tileStep, hsiteL]
    rw [hred]
    by_cases hok : trialOk P j T sL.1
        (extendSeq sL.2.seq
          (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (i, false)
            (tileIncrement P j (tileQuery P j T s) a / Real.sqrt (sweepW P.u m j)))
          (i, false)
          (tileIncrement P j (tileQuery P j T s) a / Real.sqrt (sweepW P.u m j)))
        (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
          (sL.2.seq.state sL.2.seq.length) (i, false)
          (tileIncrement P j (tileQuery P j T s) a / Real.sqrt (sweepW P.u m j)))
    · have hdec : decide (usesTrue sL i) = true := decide_eq_true hutL
      have heq : (scalarStep P j T sL i
          (tileIncrement P j (tileQuery P j T s) a)).2.consumed =
          Function.update sL.2.consumed i true := by
        simp [scalarStep, hok, hdec]
      rw [heq]
      simp
    · have htrue : (scalarStep P j T sL i
          (tileIncrement P j (tileQuery P j T s) a)).2.firstFail = true := by
        have heq : (scalarStep P j T sL i
            (tileIncrement P j (tileQuery P j T s) a)).2.firstFail =
            (failTrial P j T sL).2.firstFail := by simp [scalarStep, hok]
        rw [heq]
        by_cases ha : sL.2.attempt = 0 <;> by_cases hj : m / 2 < j <;>
          simp [failTrial, ha, hj]
      have hUpdTrue : ((tileBlock P j T).update s a).2.firstFail = true := by
        rw [tileBlock_update_running P j T s a hrun, ← hsL, hred]
        exact htrue
      simp [hUpdTrue] at hUpdFalse


/-- In a run with no failure through `k`, every state through `k` is a first trial
(`FirstTrialInv`: a nonzero attempt latches `firstFail`). -/
theorem tileNoFail_attempt0 (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hall : ∀ n ≤ k, (localState M (tileBlock P j T) x n ω).2.firstFail = false) :
    ∀ n ≤ k, (localState M (tileBlock P j T) x n ω).2.attempt = 0 := by
  have hftAll : ∀ n, FirstTrialInv x (localState M (tileBlock P j T) x n ω) :=
    fun n => localState_induct M (tileBlock P j T) x (FirstTrialInv x)
      (firstTrialInv_enter P j T x)
      (fun s a hs => firstTrialInv_update P j T x s a hs) n ω
  intro n hn
  by_cases h : (localState M (tileBlock P j T) x n ω).2.attempt = 0
  · exact h
  · exfalso
    have htrue := (hftAll n).1 h
    have hfalse := hall n hn
    simp [htrue] at hfalse

/-- One scalar step keeps a set `consumed` bit under a non-failing outcome: success updates
`consumed` at its own site (re-setting it at `i` via the stable `usesTrue`, preserving it
elsewhere), failure latches `firstFail`. -/
theorem tileScalar_consumed_keep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (sL : RunRecord d m × TileScratch d m)
    (jj : Torus d m) (ζ : ℝ) (i : Torus d m)
    (hconsL : sL.2.consumed i = true) (hutL : usesTrue sL i)
    (hff : (scalarStep P j T sL jj ζ).2.firstFail = false) :
    (scalarStep P j T sL jj ζ).2.consumed i = true := by
  classical
  by_cases hok : trialOk P j T sL.1
      (extendSeq sL.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
          (sL.2.seq.state sL.2.seq.length) (jj, false)
          (ζ / Real.sqrt (sweepW P.u m j)))
        (jj, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
        (sL.2.seq.state sL.2.seq.length) (jj, false)
        (ζ / Real.sqrt (sweepW P.u m j)))
  · have heq : (scalarStep P j T sL jj ζ).2.consumed =
        Function.update sL.2.consumed jj (decide (usesTrue sL jj)) := by
      simp [scalarStep, hok]
    rw [heq]
    by_cases hji : jj = i
    · subst hji
      have hdec : decide (usesTrue sL jj) = true := decide_eq_true hutL
      simp only [hdec, Function.update_self]
    · have hne : i ≠ jj := fun h => hji h.symm
      rw [Function.update_of_ne hne]
      exact hconsL
  · have heq : (scalarStep P j T sL jj ζ).2.firstFail =
        (failTrial P j T sL).2.firstFail := by simp [scalarStep, hok]
    have hffT : (failTrial P j T sL).2.firstFail = true := by
      by_cases hj : m / 2 < j <;> simp [failTrial, hj]
    rw [heq, hffT] at hff
    cases hff

/-- Single-step `consumed` preservation: a non-failing update keeps a set `consumed` bit.
Failures always latch `firstFail` (contrapositive eliminates them); all other queries leave
`consumed` untouched except a successful scalar step, which re-sets it at its site via the
stable `usesTrue` (attempt 0, record `x`, `i ∉ x.pending`) and preserves it elsewhere. -/
theorem tileConsumed_keep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) (i : Torus d m) (x : RunRecord d m)
    (hcons : s.2.consumed i = true)
    (hff : ((tileBlock P j T).update s a).2.firstFail = false)
    (ha0 : s.2.attempt = 0) (hrec : s.1 = x) (hnp : i ∉ x.pending) :
    ((tileBlock P j T).update s a).2.consumed i = true := by
  classical
  by_cases hh : s.2.halted = true
  · rw [tileBlock_update_halted P j T s a hh]
    exact hcons
  · have hrun : s.2.halted = false := by simpa using hh
    rw [tileBlock_update_running P j T s a hrun]
    set sL := (s.1, logQuery (tileQuery P j T s) s.2) with hsL
    have hrecL : sL.1 = s.1 := rfl
    have ha0L : sL.2.attempt = 0 := by simpa [hsL, logQuery] using ha0
    have hnpL : i ∉ sL.1.pending := by simpa [hrecL, hrec] using hnp
    have hutL : usesTrue sL i := ⟨ha0L, hnpL⟩
    have hconsL : sL.2.consumed i = true := by simpa [hsL, logQuery] using hcons
    have eGen : (tileBlock P j T).update s a =
        tileStep P j T sL (tileQuery P j T s) a := by
      rw [tileBlock_update_running P j T s a hrun, ← hsL]
    cases hq : tileQuery P j T s with
    | nextOrder o =>
      simpa [tileStep] using hconsL
    | decision =>
      cases hs : sL.2.site with
      | none => simpa [tileStep, hs] using hconsL
      | some jj => simpa [tileStep, hs] using hconsL
    | trueDigit ii kk =>
      cases hs : sL.2.site with
      | none => simpa [tileStep, hs] using hconsL
      | some jj =>
        have hred : tileStep P j T sL (Query.trueDigit ii kk) a =
            scalarStep P j T sL jj (tileIncrement P j (Query.trueDigit ii kk) a) := by
          simp [tileStep, hs]
        rw [hred]
        refine tileScalar_consumed_keep P j T sL jj _ i hconsL hutL ?_
        have e2 := eGen
        rw [hq] at e2
        rw [← hred, ← e2]
        exact hff
    | auxiliary kk =>
      cases hs : sL.2.site with
      | none => simpa [tileStep, hs] using hconsL
      | some jj =>
        have hred : tileStep P j T sL (Query.auxiliary kk) a =
            scalarStep P j T sL jj (tileIncrement P j (Query.auxiliary kk) a) := by
          simp [tileStep, hs]
        rw [hred]
        refine tileScalar_consumed_keep P j T sL jj _ i hconsL hutL ?_
        have e2 := eGen
        rw [hq] at e2
        rw [← hred, ← e2]
        exact hff
    | trueSuffix ii kk =>
      cases hs : sL.2.site with
      | none => simpa [tileStep, hs] using hconsL
      | some jj =>
        have hred : tileStep P j T sL (Query.trueSuffix ii kk) a =
            scalarStep P j T sL jj (tileIncrement P j (Query.trueSuffix ii kk) a) := by
          simp [tileStep, hs]
        rw [hred]
        refine tileScalar_consumed_keep P j T sL jj _ i hconsL hutL ?_
        have e2 := eGen
        rw [hq] at e2
        rw [← hred, ← e2]
        exact hff

/-- A set `consumed` bit persists along a failure-free run: every intermediate state is a
running first trial with the entering record, so each step preserves it. -/
theorem tileConsumed_persist (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k k' : ℕ) (ω : RandomSources (Torus d m) M) (i : Torus d m)
    (hall : ∀ n ≤ k, (localState M (tileBlock P j T) x n ω).2.firstFail = false)
    (hftAll : ∀ n, FirstTrialInv x (localState M (tileBlock P j T) x n ω))
    (hk : ∀ l < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x l ω) = false)
    (hcons0 : (localState M (tileBlock P j T) x (k' + 1) ω).2.consumed i = true)
    (hnpX : i ∉ x.pending) :
    ∀ n, k' + 1 ≤ n → n < k →
      (localState M (tileBlock P j T) x n ω).2.consumed i = true := by
  have ha0All := tileNoFail_attempt0 P j T M x k ω hall
  intro n hn1 hn2
  revert hn2
  induction n, hn1 using Nat.le_induction with
  | base =>
    intro _
    exact hcons0
  | succ m hle ih =>
    intro hm2
    have hm_lt : m < k := by omega
    have hm1_le : m + 1 ≤ k := by omega
    have hrun : (tileBlock P j T).halted (localState M (tileBlock P j T) x m ω) = false :=
      hk m hm_lt
    have ha0 : (localState M (tileBlock P j T) x m ω).2.attempt = 0 :=
      ha0All m (by omega)
    have hrec : (localState M (tileBlock P j T) x m ω).1 = x :=
      (hftAll m).2 ha0 hrun
    have ihm := ih (by omega)
    have hsu := localState_succ M (tileBlock P j T) x m ω
    rw [hsu]
    refine tileConsumed_keep P j T _ _ i x ihm ?_ ha0 hrec hnpX
    rw [← hsu]
    exact hall (m + 1) hm1_le

/-- A non-failing update that halts is a commit: every other query leaves the block running
(or latches `firstFail`). In particular the query is `decision` with no exposed site. -/
theorem tileHalt_commit_step (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m))
    (hrun : s.2.halted = false)
    (hhalt : ((tileBlock P j T).update s a).2.halted = true)
    (hff : ((tileBlock P j T).update s a).2.firstFail = false) :
    ((tileBlock P j T).update s a).1 =
      commitTrial s.1 s.2 (decide (IsFinalSweep m j)) ∧
    tileQuery P j T s = Query.decision ∧ s.2.site = none := by
  classical
  rw [tileBlock_update_running P j T s a hrun] at hhalt hff ⊢
  set sL := (s.1, logQuery (tileQuery P j T s) s.2) with hsL
  have hrecL : sL.1 = s.1 := rfl
  have hhaltL : sL.2.halted = false := by simpa [hsL, logQuery] using hrun
  have hffT : (failTrial P j T sL).2.firstFail = true := by
    by_cases hj : m / 2 < j <;> simp [failTrial, hj]
  have eGen : tileStep P j T (s.1, logQuery (tileQuery P j T s) s.2) (tileQuery P j T s) a =
      tileStep P j T sL (tileQuery P j T s) a := by rw [hsL]
  rw [eGen] at hhalt hff ⊢
  revert hhalt hff
  cases hq : tileQuery P j T s with
  | nextOrder o =>
    intro hhalt _
    have hst : (tileStep P j T sL (Query.nextOrder o) a).2.halted = false := by
      simpa [tileStep] using hhaltL
    rw [hst] at hhalt
    cases hhalt
  | decision =>
    cases hs : sL.2.site with
    | none =>
      intro _ _
      refine ⟨?_, rfl, ?_⟩
      · have hstep : (tileStep P j T sL Query.decision a).1 =
            commitTrial sL.1 sL.2 (decide (IsFinalSweep m j)) := by
          simp [tileStep, hs]
        rw [hstep]
        unfold commitTrial
        rw [hrecL]
        have hseq : sL.2.seq = s.2.seq := by simp [hsL, logQuery]
        have hadd : sL.2.added = s.2.added := by simp [hsL, logQuery]
        have hcs : sL.2.consumed = s.2.consumed := by simp [hsL, logQuery]
        rw [hseq, hadd, hcs]
      · simpa [hsL, logQuery] using hs
    | some jj =>
      intro hhalt _
      have hst : (tileStep P j T sL Query.decision a).2.halted = false := by
        simpa [tileStep, hs] using hhaltL
      rw [hst] at hhalt
      cases hhalt
  | trueDigit ii kk =>
    cases hs : sL.2.site with
    | none =>
      intro hhalt _
      have hst : (tileStep P j T sL (Query.trueDigit ii kk) a).2.halted = false := by
        simpa [tileStep, hs] using hhaltL
      rw [hst] at hhalt
      cases hhalt
    | some jj =>
      intro hhalt hff
      have hred : tileStep P j T sL (Query.trueDigit ii kk) a =
          scalarStep P j T sL jj (tileIncrement P j (Query.trueDigit ii kk) a) := by
        simp [tileStep, hs]
      by_cases hok : trialOk P j T sL.1
          (extendSeq sL.2.seq
            (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
              (sL.2.seq.state sL.2.seq.length) (jj, false)
              (tileIncrement P j (Query.trueDigit ii kk) a / Real.sqrt (sweepW P.u m j)))
            (jj, false) (tileIncrement P j (Query.trueDigit ii kk) a / Real.sqrt (sweepW P.u m j)))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (jj, false)
            (tileIncrement P j (Query.trueDigit ii kk) a / Real.sqrt (sweepW P.u m j)))
      · have hhaltS : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueDigit ii kk) a)).2.halted = sL.2.halted := by
          simp [scalarStep, hok]
        rw [hred, hhaltS, hhaltL] at hhalt
        cases hhalt
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueDigit ii kk) a)).2.firstFail =
            (failTrial P j T sL).2.firstFail := by simp [scalarStep, hok]
        rw [hred, heq, hffT] at hff
        cases hff
  | auxiliary kk =>
    cases hs : sL.2.site with
    | none =>
      intro hhalt _
      have hst : (tileStep P j T sL (Query.auxiliary kk) a).2.halted = false := by
        simpa [tileStep, hs] using hhaltL
      rw [hst] at hhalt
      cases hhalt
    | some jj =>
      intro hhalt hff
      have hred : tileStep P j T sL (Query.auxiliary kk) a =
          scalarStep P j T sL jj (tileIncrement P j (Query.auxiliary kk) a) := by
        simp [tileStep, hs]
      by_cases hok : trialOk P j T sL.1
          (extendSeq sL.2.seq
            (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
              (sL.2.seq.state sL.2.seq.length) (jj, false)
              (tileIncrement P j (Query.auxiliary kk) a / Real.sqrt (sweepW P.u m j)))
            (jj, false) (tileIncrement P j (Query.auxiliary kk) a / Real.sqrt (sweepW P.u m j)))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (jj, false)
            (tileIncrement P j (Query.auxiliary kk) a / Real.sqrt (sweepW P.u m j)))
      · have hhaltS : (scalarStep P j T sL jj
            (tileIncrement P j (Query.auxiliary kk) a)).2.halted = sL.2.halted := by
          simp [scalarStep, hok]
        rw [hred, hhaltS, hhaltL] at hhalt
        cases hhalt
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.auxiliary kk) a)).2.firstFail =
            (failTrial P j T sL).2.firstFail := by simp [scalarStep, hok]
        rw [hred, heq, hffT] at hff
        cases hff
  | trueSuffix ii kk =>
    cases hs : sL.2.site with
    | none =>
      intro hhalt _
      have hst : (tileStep P j T sL (Query.trueSuffix ii kk) a).2.halted = false := by
        simpa [tileStep, hs] using hhaltL
      rw [hst] at hhalt
      cases hhalt
    | some jj =>
      intro hhalt hff
      have hred : tileStep P j T sL (Query.trueSuffix ii kk) a =
          scalarStep P j T sL jj (tileIncrement P j (Query.trueSuffix ii kk) a) := by
        simp [tileStep, hs]
      by_cases hok : trialOk P j T sL.1
          (extendSeq sL.2.seq
            (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
              (sL.2.seq.state sL.2.seq.length) (jj, false)
              (tileIncrement P j (Query.trueSuffix ii kk) a / Real.sqrt (sweepW P.u m j)))
            (jj, false) (tileIncrement P j (Query.trueSuffix ii kk) a / Real.sqrt (sweepW P.u m j)))
          (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) sL.1.r)
            (sL.2.seq.state sL.2.seq.length) (jj, false)
            (tileIncrement P j (Query.trueSuffix ii kk) a / Real.sqrt (sweepW P.u m j)))
      · have hhaltS : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueSuffix ii kk) a)).2.halted = sL.2.halted := by
          simp [scalarStep, hok]
        rw [hred, hhaltS, hhaltL] at hhalt
        cases hhalt
      · have heq : (scalarStep P j T sL jj
            (tileIncrement P j (Query.trueSuffix ii kk) a)).2.firstFail =
            (failTrial P j T sL).2.firstFail := by simp [scalarStep, hok]
        rw [hred, heq, hffT] at hff
        cases hff

/-- Exit record of a failure-free run containing a true query: the halting step commits, and
the queried site's `consumed` bit (set by its query step) persists into the commit, so the
commit advances its prefix (digit sweep) or terminals it (final sweep). -/
theorem tileNoFail_trueQuery_exit (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k k' : ℕ) (ω : RandomSources (Torus d m) M) (i : Torus d m)
    (hk : ∀ l < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x l ω) = false)
    (hhalt : (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true)
    (hall : ∀ n ≤ k, (localState M (tileBlock P j T) x n ω).2.firstFail = false)
    (hk' : k' < k)
    (hsite : (localState M (tileBlock P j T) x k' ω).2.site = some i)
    (h1 : activeIn P j T (localState M (tileBlock P j T) x k' ω).1 i)
    (h2 : usesTrue (localState M (tileBlock P j T) x k' ω) i) :
    (localState M (tileBlock P j T) x k ω).1 =
      commitTrial (localState M (tileBlock P j T) x (k - 1) ω).1
        (localState M (tileBlock P j T) x (k - 1) ω).2 (decide (IsFinalSweep m j)) ∧
    (localState M (tileBlock P j T) x (k - 1) ω).1 = x ∧
    (localState M (tileBlock P j T) x (k - 1) ω).2.consumed i = true := by
  classical
  have hftAll : ∀ n, FirstTrialInv x (localState M (tileBlock P j T) x n ω) :=
    fun n => localState_induct M (tileBlock P j T) x (FirstTrialInv x)
      (firstTrialInv_enter P j T x)
      (fun s a hs => firstTrialInv_update P j T x s a hs) n ω
  have ha0All := tileNoFail_attempt0 P j T M x k ω hall
  have hk1 : 1 ≤ k := by omega
  have hrunKm1 : (tileBlock P j T).halted (localState M (tileBlock P j T) x (k - 1) ω) = false :=
    hk (k - 1) (by omega)
  have ha0Km1 : (localState M (tileBlock P j T) x (k - 1) ω).2.attempt = 0 :=
    ha0All (k - 1) (by omega)
  have hrecKm1 : (localState M (tileBlock P j T) x (k - 1) ω).1 = x :=
    (hftAll (k - 1)).2 ha0Km1 hrunKm1
  have hrunQ : (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false :=
    hk k' hk'
  have ha0Q : (localState M (tileBlock P j T) x k' ω).2.attempt = 0 :=
    ha0All k' (by omega)
  have hrecQ : (localState M (tileBlock P j T) x k' ω).1 = x :=
    (hftAll k').2 ha0Q hrunQ
  have hnpX : i ∉ x.pending := hrecQ ▸ h2.2
  have hkEq : k = (k - 1) + 1 := by omega
  have hsu0 := localState_succ M (tileBlock P j T) x (k - 1) ω
  rw [← hkEq] at hsu0
  obtain ⟨aKm1, hsu⟩ : ∃ a, localState M (tileBlock P j T) x k ω =
      (tileBlock P j T).update (localState M (tileBlock P j T) x (k - 1) ω) a :=
    ⟨_, hsu0⟩
  have hhaltU : ((tileBlock P j T).update (localState M (tileBlock P j T) x (k - 1) ω)
      aKm1).2.halted = true := by
    rw [← hsu]
    simpa [tileBlock_halted] using hhalt
  have hffU : ((tileBlock P j T).update (localState M (tileBlock P j T) x (k - 1) ω)
      aKm1).2.firstFail = false := by
    rw [← hsu]
    exact hall k le_rfl
  obtain ⟨hexit, hqDec, -⟩ := tileHalt_commit_step P j T
    (localState M (tileBlock P j T) x (k - 1) ω) aKm1 hrunKm1 hhaltU hffU
  have hexitK : (localState M (tileBlock P j T) x k ω).1 =
      commitTrial (localState M (tileBlock P j T) x (k - 1) ω).1
        (localState M (tileBlock P j T) x (k - 1) ω).2 (decide (IsFinalSweep m j)) := by
    rw [hsu]
    exact hexit
  -- the query at `k'` is scalar, but the halting query (at `k - 1`) is a decision
  have hqScalar : tileQuery P j T (localState M (tileBlock P j T) x k' ω) ≠ Query.decision := by
    by_cases hfin : IsFinalSweep m j
    · have hqq : tileQuery P j T (localState M (tileBlock P j T) x k' ω) =
          Query.trueSuffix i ((localState M (tileBlock P j T) x k' ω).1.prefixLength i) := by
        simp [tileQuery, hsite, h1, h2, hfin]
      rw [hqq]
      intro h
      cases h
    · have hqq : tileQuery P j T (localState M (tileBlock P j T) x k' ω) =
          Query.trueDigit i ((localState M (tileBlock P j T) x k' ω).1.prefixLength i) := by
        simp [tileQuery, hsite, h1, h2, hfin]
      rw [hqq]
      intro h
      cases h
  have hkk : k' + 1 < k := by
    by_contra hcon
    have hkkEq : k - 1 = k' := by omega
    have hqqEq : tileQuery P j T (localState M (tileBlock P j T) x (k - 1) ω) =
        tileQuery P j T (localState M (tileBlock P j T) x k' ω) := by rw [hkkEq]
    rw [hqDec] at hqqEq
    exact hqScalar hqqEq.symm
  have hconsSet : (localState M (tileBlock P j T) x (k' + 1) ω).2.consumed i = true := by
    have hqk' : k' + 1 ≤ k := by omega
    have hallK'1 : (localState M (tileBlock P j T) x (k' + 1) ω).2.firstFail = false :=
      hall (k' + 1) hqk'
    have hsuQ := localState_succ M (tileBlock P j T) x k' ω
    rw [hsuQ]
    rw [hsuQ] at hallK'1
    exact tileConsumed_set_of_true P j T (localState M (tileBlock P j T) x k' ω) _ i
      hrunQ hsite h1 h2 hallK'1
  have hconsKm1 : (localState M (tileBlock P j T) x (k - 1) ω).2.consumed i = true :=
    tileConsumed_persist P j T M x k k' ω i hall hftAll hk hconsSet hnpX (k - 1)
      (by omega) (by omega)
  exact ⟨hexitK, hrecKm1, hconsKm1⟩


/-- Unqueried half of the query discipline: no pre-halting query hits `declaredFresh exit`.
True queries (digit/suffix) are the only nontrivial cases; orders/decisions read no signs
and auxiliary queries read `inr` signs only. -/
theorem tileQueryUnqueried (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hk : ∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false)
    (hhalt : (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true) :
    ∀ k' < k, ∀ z ∈ declaredFresh
      ((tileBlock P j T).exit (localState M (tileBlock P j T) x k ω)),
      z ∉ querySigns (Torus d m) ((tileBlock P j T).next (localState M (tileBlock P j T) x k' ω)) := by
  intro k' hk' z hz
  have hs' : localState M (tileBlock P j T) x k' ω =
      localState M (tileBlock P j T) x k' ω := rfl
  have hrun : (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false :=
    hk k' hk'
  have hnext : (tileBlock P j T).next (localState M (tileBlock P j T) x k' ω) =
      tileQuery P j T (localState M (tileBlock P j T) x k' ω) :=
    tileBlock_next_running P j T _ hrun
  rw [hnext]
  -- exit record and its freshness
  set sExit := localState M (tileBlock P j T) x k ω with hsExit
  set sQ := localState M (tileBlock P j T) x k' ω with hsQ
  -- if exit is aborted, declaredFresh is empty
  by_cases habExit : sExit.1.aborted = true
  · have hempty : declaredFresh (sExit.1) = ∅ := declaredFresh_aborted _ habExit
    have hz' : z ∈ declaredFresh sExit.1 := by simpa [tileBlock, hsExit] using hz
    rw [hempty] at hz'
    simp at hz'
  · -- exit is a commit; analyze the query
    unfold tileQuery at ⊢
    rcases hsite : sQ.2.site with _ | i
    · simp only
      split_ifs
      · intro hzmem
        simp [querySigns] at hzmem
      · intro hzmem
        simp [querySigns] at hzmem
    · simp only
      split_ifs with h1 h2 h3 h4
      · -- trueSuffix: suffix signs avoid `declaredFresh exit`
        intro hzmem
        simp only [querySigns, Set.mem_setOf_eq] at hzmem
        obtain ⟨kk, hkk, hzmemEq⟩ := hzmem
        rcases hz with ⟨habE, i', k'', hzEq, hnpE, hntE, hleE⟩
        -- `z = inl (i',k'') = inl (i,kk)`, so `i' = i`
        have hpair : (i', k'') = (i, kk) := by
          have hzz : (Sum.inl (i', k'') : SignIndex (Torus d m)) = Sum.inl (i, kk) :=
            hzEq.symm.trans hzmemEq
          simpa using hzz
        have hii : i' = i := congrArg Prod.fst hpair
        rw [hii] at hnpE hntE
        -- `hleE : exit.prefixLength i ≤ k''`; keep for the no-fail half
        by_cases hffE : sExit.2.firstFail = true
        · -- a failure marked `i`; pending propagates to exit
          have h1e : activeIn P j T (localState M (tileBlock P j T) x k' ω).1 i := by
            simpa [hsQ] using h1
          have h2e : usesTrue (localState M (tileBlock P j T) x k' ω) i := by
            simpa [hsQ] using h2
          have hffEe : (localState M (tileBlock P j T) x k ω).2.firstFail = true := by
            simpa [hsExit] using hffE
          have hpend := tileTrueQuery_fail_pending P j T M x k k' ω i hk hk' h1e h2e hffEe
          have hnpE' : i ∉ (localState M (tileBlock P j T) x k ω).1.pending := by
            simpa [tileBlock, hsExit] using hnpE
          exact absurd hpend hnpE'
        · -- no failure: the suffix site was consumed, hence terminal in the final sweep
          have hffEf : sExit.2.firstFail = false := by
            cases hfb : sExit.2.firstFail with
            | true => simp [hfb] at hffE
            | false => rfl
          have hall : ∀ n ≤ k, (localState M (tileBlock P j T) x n ω).2.firstFail = false :=
            tileAllFalse_of_exitFalse P j T M x k ω (by simpa [hsExit] using hffEf)
          obtain ⟨hexit, -, hconsKm1⟩ := tileNoFail_trueQuery_exit P j T M x k k' ω i
            hk hhalt hall hk' (by simpa [hsQ] using hsite) (by simpa [hsQ] using h1)
            (by simpa [hsQ] using h2)
          have hntE' : i ∉ (localState M (tileBlock P j T) x k ω).1.terminal := by
            simpa [tileBlock, hsExit] using hntE
          have hfin : IsFinalSweep m j := h3
          have hdec : decide (IsFinalSweep m j) = true := decide_eq_true hfin
          have htermEq : (commitTrial (localState M (tileBlock P j T) x (k - 1) ω).1
              (localState M (tileBlock P j T) x (k - 1) ω).2
              (decide (IsFinalSweep m j))).terminal =
              (localState M (tileBlock P j T) x (k - 1) ω).1.terminal ∪
                Finset.univ.filter (fun ii =>
                  (localState M (tileBlock P j T) x (k - 1) ω).2.consumed ii = true) := by
            simp [commitTrial, hdec]
          rw [hexit, htermEq, Finset.mem_union, not_or] at hntE'
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hconsKm1⟩) hntE'.2
      · -- trueDigit: singleton sign avoids `declaredFresh exit`
        intro hzmem
        simp only [querySigns, Set.mem_singleton_iff] at hzmem
        rcases hz with ⟨habE, i', k'', hzEq, hnpE, hntE, hleE⟩
        -- `z = inl (i',k'') = inl (i, h)`, so `i' = i`
        have hpair : (i', k'') = (i, sQ.1.prefixLength i) := by
          have hzz : (Sum.inl (i', k'') : SignIndex (Torus d m)) =
              Sum.inl (i, sQ.1.prefixLength i) := hzEq.symm.trans hzmem
          simpa using hzz
        have hii : i' = i := congrArg Prod.fst hpair
        rw [hii] at hnpE hntE
        by_cases hffE : sExit.2.firstFail = true
        · -- a failure marked `i`; pending propagates to exit
          have h1e : activeIn P j T (localState M (tileBlock P j T) x k' ω).1 i := by
            simpa [hsQ] using h1
          have h2e : usesTrue (localState M (tileBlock P j T) x k' ω) i := by
            simpa [hsQ] using h2
          have hffEe : (localState M (tileBlock P j T) x k ω).2.firstFail = true := by
            simpa [hsExit] using hffE
          have hpend := tileTrueQuery_fail_pending P j T M x k k' ω i hk hk' h1e h2e hffEe
          have hnpE' : i ∉ (localState M (tileBlock P j T) x k ω).1.pending := by
            simpa [tileBlock, hsExit] using hnpE
          exact absurd hpend hnpE'
        · -- no failure: the digit was consumed, prefix advanced past the queried sign
          have hffEf : sExit.2.firstFail = false := by
            cases hfb : sExit.2.firstFail with
            | true => simp [hfb] at hffE
            | false => rfl
          have hall : ∀ n ≤ k, (localState M (tileBlock P j T) x n ω).2.firstFail = false :=
            fun n hn => by
              have hEf : (localState M (tileBlock P j T) x k ω).2.firstFail = false := by
                simpa [hsExit] using hffEf
              by_contra hcon
              have htrue : (localState M (tileBlock P j T) x n ω).2.firstFail = true := by
                cases hfb : (localState M (tileBlock P j T) x n ω).2.firstFail with
                | true => rfl
                | false => simp [hfb] at hcon
              have hprop := tileLocal_firstFail_mono P j T M x ω n k hn htrue
              simp [hprop] at hEf
          have hftAll : ∀ n, FirstTrialInv x (localState M (tileBlock P j T) x n ω) :=
            fun n => localState_induct M (tileBlock P j T) x (FirstTrialInv x)
              (firstTrialInv_enter P j T x)
              (fun s a hs => firstTrialInv_update P j T x s a hs) n ω
          -- query state has the entering record
          obtain ⟨ha0Q, hnpQ⟩ := h2
          have hSQx : sQ.1 = x :=
            (hftAll k').2 ha0Q (by simpa [tileBlock_halted] using hrun)
          have hHx : sQ.1.prefixLength i = x.prefixLength i := by rw [hSQx]
          have hnpX : i ∉ x.pending := hSQx ▸ hnpQ
          have hkk : k'' = sQ.1.prefixLength i := congrArg Prod.snd hpair
          -- heights force `exit.prefixLength i ≤ x.prefixLength i`
          have hleXi : sExit.1.prefixLength i ≤ x.prefixLength i := by
            rw [hii] at hleE
            have hleE' : sExit.1.prefixLength i ≤ k'' := hleE
            omega
          -- but the commit advanced it by one (digit sweep, non-final)
          have hk1 : 1 ≤ k := by omega
          have hrunKm1 : (tileBlock P j T).halted
              (localState M (tileBlock P j T) x (k - 1) ω) = false :=
            hk (k - 1) (by omega)
          have hfalseKm1 : (localState M (tileBlock P j T) x (k - 1) ω).2.firstFail = false :=
            hall (k - 1) (by omega)
          have hattempt0Km1 : (localState M (tileBlock P j T) x (k - 1) ω).2.attempt = 0 := by
            by_contra hne
            have htrue := (hftAll (k - 1)).1 hne
            cases hfb : (localState M (tileBlock P j T) x (k - 1) ω).2.firstFail with
            | true => simp [hfb] at hfalseKm1
            | false => simp [hfb] at htrue
          have hrecKm1 : (localState M (tileBlock P j T) x (k - 1) ω).1 = x :=
            (hftAll (k - 1)).2 hattempt0Km1 hrunKm1
          -- the halting update committed (not a failure, by `hall`)
          have hhaltK : (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true := by
            simpa [hsExit] using hhalt
          have hkEq : k = (k - 1) + 1 := by omega
          have hsuK := localState_succ M (tileBlock P j T) x (k - 1) ω
          rw [← hkEq] at hsuK
          -- identify the commit: only decision-none halts without failing
          -- consumed `i` was set at `k'+1` (via the helper; failure would set `firstFail`)
          have hconsSet : (localState M (tileBlock P j T) x (k' + 1) ω).2.consumed i = true := by
            have hqk' : k' + 1 ≤ k := by omega
            have hallK'1 : (localState M (tileBlock P j T) x (k' + 1) ω).2.firstFail = false :=
              hall (k' + 1) hqk'
            have hsuQ := localState_succ M (tileBlock P j T) x k' ω
            have hsiteE : (localState M (tileBlock P j T) x k' ω).2.site = some i := by
              simpa [hsQ] using hsite
            have h1e : activeIn P j T (localState M (tileBlock P j T) x k' ω).1 i := by
              simpa [hsQ] using h1
            have h2sQ : usesTrue sQ i := ⟨ha0Q, hnpQ⟩
            have h2e : usesTrue (localState M (tileBlock P j T) x k' ω) i := by
              simpa [hsQ] using h2sQ
            have hrunQ' : (tileBlock P j T).halted
                (localState M (tileBlock P j T) x k' ω) = false := hk k' hk'
            rw [hsuQ]
            rw [hsuQ] at hallK'1
            exact tileConsumed_set_of_true P j T
              (localState M (tileBlock P j T) x k' ω) _ i
              hrunQ' hsiteE h1e h2e hallK'1
          -- finish via the no-fail exit equation: the commit advanced the prefix by one
          obtain ⟨hexit, -, hconsKm1⟩ := tileNoFail_trueQuery_exit P j T M x k k' ω i
            hk hhalt hall hk' (by simpa [hsQ] using hsite) (by simpa [hsQ] using h1)
            (⟨by simpa [hsQ] using ha0Q, by simpa [hsQ] using hnpQ⟩)
          have hnfin : ¬ IsFinalSweep m j := h3
          have hdec : decide (IsFinalSweep m j) = false := decide_eq_false hnfin
          have hpreEq : (commitTrial (localState M (tileBlock P j T) x (k - 1) ω).1
              (localState M (tileBlock P j T) x (k - 1) ω).2
              (decide (IsFinalSweep m j))).prefixLength i =
              (localState M (tileBlock P j T) x (k - 1) ω).1.prefixLength i + 1 := by
            simp [commitTrial, hdec, hconsKm1]
          have hsEq : sExit.1 = (localState M (tileBlock P j T) x k ω).1 := by rw [hsExit]
          rw [hsEq, hexit, hpreEq, hrecKm1] at hleXi
          omega
      · intro hzmem
        simp [querySigns] at hzmem
      · intro hzmem
        -- auxiliary query: declaredFresh has only `inl` signs
        simp only [querySigns, Set.mem_singleton_iff] at hzmem
        rcases hz with ⟨hab, ii, kk, rfl, hnp, hnt, hle⟩
        simp at hzmem
      · intro hzmem
        simp [querySigns] at hzmem

theorem tileQueryStatement_proof : TileQueryStatement := by
  intro d m P j T M x k ω hk hhalt
  exact ⟨tileQueryShrink P j T M x k ω hk,
    tileQueryUnqueried P j T M x k ω hk hhalt⟩

/-- A running state with `attempt ≤ k` reads only `tileHaltPattern k x` coordinates
(first trial via `tileQuery_reads_pattern` + `tilePattern ⊆ haltPattern`; retries via
their family/order `a ≤ k`). -/
theorem tileQuery_reads_haltPattern (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (k : ℕ)
    (x : RunRecord d m) (s : RunRecord d m × TileScratch d m)
    (hxx : s.2.attempt = 0 → s.1 = x) (hxaborted : x.aborted = false)
    (ha : s.2.attempt ≤ k) :
    (∀ z ∈ querySigns (Torus d m) (tileQuery P j T s),
      z ∈ (tileHaltPattern P j T k x).signs) ∧
    (∀ o, tileQuery P j T s = Query.nextOrder o →
      o ∈ (tileHaltPattern P j T k x).orders) := by
  -- split on whether this is still the first trial
  by_cases ha0 : s.2.attempt = 0
  · -- first trial: narrow to `tilePattern`, which sits inside the halt pattern
    have hSx : s.1 = x := hxx ha0
    subst hSx
    have hpat := tileQuery_reads_pattern P j T s.1 s rfl hxaborted ha0
    constructor
    · intro z hz
      have hzpat := hpat.1 z hz
      -- `tilePattern.signs ⊆ haltPattern.signs` (family/order `0 ∈ range (k+1)`)
      simp only [FreshPattern.signs] at hzpat ⊢
      rcases hzpat with ⟨i, hi, kk, hhk, rfl⟩ | ⟨aa, haa, rfl⟩
      · exact Or.inl ⟨i, by simpa [tilePattern, tileHaltPattern, hxaborted] using hi, kk, by
          simpa [tilePattern, tileHaltPattern, hxaborted] using hhk, rfl⟩
      · -- auxiliary family `0`: `0 ≤ k` so it lies in the halt `aux`
        right
        refine ⟨_, ?_, rfl⟩
        have haa' : aa ∈ ((((TS P j T ∩ s.1.endpoint.active) ∩ s.1.pending) \
            s.1.terminal).image (tileAuxIndex j T 0)) := by
          simpa [tilePattern, hxaborted] using haa
        rcases Finset.mem_image.mp haa' with ⟨ii, hii, rfl⟩
        have hmem : (0, ii) ∈ (Finset.range (k + 1)) ×ˢ tileSites (P.cover j) T := by
          rw [Finset.mem_product]
          refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
          have h1 : ii ∈ ((TS P j T ∩ s.1.endpoint.active) ∩ s.1.pending) :=
            (Finset.mem_sdiff.mp hii).1
          have h2 : ii ∈ TS P j T ∩ s.1.endpoint.active :=
            (Finset.mem_inter.mp h1).1
          exact (Finset.mem_inter.mp h2).1
        have himg : tileAuxIndex j T 0 ii ∈
            (((Finset.range (k + 1)) ×ˢ tileSites (P.cover j) T).image
              (fun p => tileAuxIndex (d := d) (m := m) j T p.1 p.2)) := by
          rw [Finset.mem_image]
          exact ⟨(0, ii), hmem, rfl⟩
        have haux : tileAuxIndex j T 0 ii ∈ (tileHaltPattern P j T k s.1).aux := by
          simpa [tilePattern, tileHaltPattern, hxaborted] using himg
        exact haux
    · intro o ho
      have hoPat := hpat.2 o ho
      -- `tilePattern.orders = {order 0} ⊆ halt orders` (`0 ∈ range (k+1)`)
      have ho0 : o = tileOrderIndex j T 0 := by
        simpa [tilePattern, hxaborted] using hoPat
      have hmem0 : (0 : ℕ) ∈ Finset.range (k + 1) :=
        Finset.mem_range.mpr (by omega)
      have hordEq : (tileHaltPattern P j T k s.1).orders =
          (Finset.range (k + 1)).image (tileOrderIndex j T) := by
        simp [tileHaltPattern, hxaborted]
      rw [hordEq, Finset.mem_image]
      exact ⟨0, hmem0, ho0.symm⟩
  · -- retry `a ≥ 1` (so `a ≤ k`): only family-`a` aux signs and order `a` are read.
    -- Mirror `tileQuery_reads_pattern`: specialize the goal first, then intro.
    have haPos : 1 ≤ s.2.attempt := by omega
    have hnt : ∀ ii, ¬ usesTrue s ii := by
      intro ii hcon
      exact ha0 (hcon.1)
    constructor
    · -- signs: only auxiliary family-`a` signs (true branches impossible)
      unfold tileQuery
      rcases hs : s.2.site with _ | ii
      · simp only
        split_ifs
        · intro z hz
          simp [querySigns] at hz
        · intro z hz
          simp [querySigns] at hz
      · -- site exposed: full case split (as in `tileQuery_reads_pattern`);
        -- true leaves are impossible (`hnt`), the rest read aux/empty.
        simp only
        split_ifs with h1 h2 h3 h4
        · -- `usesTrue` true + final: `trueSuffix` (impossible)
          intro z hz
          exact absurd h2 (hnt _)
        · -- `usesTrue` true + digit: impossible likewise
          intro z hz
          exact absurd h2 (hnt _)
        · -- `usesTrue` false + aux already used: `decision` (no signs)
          intro z hz
          simp [querySigns, tileQuery, hs, h1, h2, h4] at hz
        · -- `usesTrue` false + fresh aux: `auxiliary` family `a ≤ k`
          intro z hz
          simp only [querySigns, Set.mem_singleton_iff] at hz
          have hzEq : z = Sum.inr (tileAuxIndex j T s.2.attempt ii) := hz
          right
          refine ⟨_, ?_, hzEq⟩
          have hmem : (s.2.attempt, ii) ∈
              (Finset.range (k + 1)) ×ˢ tileSites (P.cover j) T := by
            rw [Finset.mem_product]
            exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha), h1.1⟩
          have himg : tileAuxIndex j T s.2.attempt ii ∈
              (((Finset.range (k + 1)) ×ˢ tileSites (P.cover j) T).image
                (fun p => tileAuxIndex (d := d) (m := m) j T p.1 p.2)) := by
            rw [Finset.mem_image]
            exact ⟨(s.2.attempt, ii), hmem, rfl⟩
          have haux : tileAuxIndex j T s.2.attempt ii ∈
              (tileHaltPattern P j T k x).aux := by
            simpa [tileHaltPattern, hxaborted] using himg
          exact haux
        · -- inactive site: `decision` (no signs)
          intro z hz
          simp [querySigns, tileQuery, hs, h1] at hz
    · -- orders: only `order a` with `a ≤ k` (or decisions, which are not orders)
      unfold tileQuery
      rcases hs : s.2.site with _ | ii
      · simp only
        split_ifs with hlt
        · intro o ho
          cases ho
          have hmem : s.2.attempt ∈ Finset.range (k + 1) :=
            Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
          have himg : tileOrderIndex j T s.2.attempt ∈
              (Finset.range (k + 1)).image (tileOrderIndex j T) := by
            rw [Finset.mem_image]
            exact ⟨s.2.attempt, hmem, rfl⟩
          have hord : tileOrderIndex j T s.2.attempt ∈
              (tileHaltPattern P j T k x).orders := by
            simpa [tileHaltPattern, hxaborted] using himg
          exact hord
        · intro o ho
          cases ho
      · simp only [hnt]
        split_ifs with h1 h2 h3 h4 <;> intro o ho <;> cases ho

/-- Coupling for `notHalted`: agreeing samples run identically through step `k`,
so halting agrees. Aborted entries halt at once (empty `notHalted`); otherwise queries
read halt-pattern coordinates (`tileQuery_reads_haltPattern` with attempt `≤ k`). -/
theorem tileHaltDependsOnly (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (k : ℕ)
    (x : RunRecord d m) :
    DependsOnly (Torus d m) (M := M) (tileHaltPattern P j T k x)
      (notHalted M (tileBlock P j T) x k) := by
  classical
  -- one direction for arbitrary agreeing samples, then symmetry
  suffices H : ∀ ω ω' : RandomSources (Torus d m) M,
      (∀ z ∈ (tileHaltPattern P j T k x).signs, ω.1 z = ω'.1 z) →
      (∀ o ∈ (tileHaltPattern P j T k x).orders, ω.2 o = ω'.2 o) →
      ω ∈ notHalted M (tileBlock P j T) x k → ω' ∈ notHalted M (tileBlock P j T) x k by
    intro ω ω' h1 h2
    exact ⟨H ω ω' h1 h2, H ω' ω (fun z hz => (h1 z hz).symm) (fun o ho => (h2 o ho).symm)⟩
  intro ω ω' h1 h2 hω
  -- aborted entry halts at once, so `notHalted` is empty (both sides false)
  by_cases hxab : x.aborted = true
  · exfalso
    have hno : ∀ n, (localState M (tileBlock P j T) x n ω).2.halted = true := by
      intro n
      exact localState_induct M (tileBlock P j T) x
        (fun s => s.2.halted = true)
        (by simp [tileBlock, hxab, initScratch])
        (fun s a hs => by
          rw [tileBlock_update_halted P j T s a hs]; exact hs) n ω
    have h0 := hω 0 (by omega)
    have hhalt0 : (tileBlock P j T).halted (localState M (tileBlock P j T) x 0 ω) = true := by
      simpa [tileBlock] using hno 0
    simp [hhalt0] at h0
  · -- entered running: couple the runs through step `k`
    have hxaborted : x.aborted = false := by cases h : x.aborted <;> simp_all
    have hftAll : ∀ n, FirstTrialInv x (localState M (tileBlock P j T) x n ω) :=
      fun n => localState_induct M (tileBlock P j T) x (FirstTrialInv x)
        (firstTrialInv_enter P j T x)
        (fun s a hs => firstTrialInv_update P j T x s a hs) n ω
    have hagree : ∀ n ≤ k,
        machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
          (tileBlock P j T).update n ω =
        machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
          (tileBlock P j T).update n ω' := by
      intro n hn
      induction n with
      | zero => rfl
      | succ n ih =>
        have ihn := ih (by omega)
        rw [machineRun_succ, machineRun_succ, ← ihn]
        set s := (machineRun (Torus d m) M ((tileBlock P j T).enter x)
          (tileBlock P j T).next (tileBlock P j T).update n ω).1 with hs
        have hss : s = localState M (tileBlock P j T) x n ω := rfl
        -- attempt bound for the pattern families
        have hatt : s.2.attempt ≤ k := by
          have hle := tileAttempt_le_steps P j T M x ω n
          have hsn : s.2.attempt =
              (localState M (tileBlock P j T) x n ω).2.attempt := by
            simp [hs, localState, machineState]
          omega
        -- record equality when in the first trial (for true queries)
        have hxx : s.2.attempt = 0 → s.1 = x := by
          intro ha0
          have hsq : s.1 = (localState M (tileBlock P j T) x n ω).1 := by
            simp [hs, localState, machineState]
          have hft := hftAll n
          have hrun_n : (tileBlock P j T).halted
              (localState M (tileBlock P j T) x n ω) = false := by
            -- `n < k` here (since `succ n ≤ k`), and `notHalted` at `n` holds
            have hnk : n < k := by omega
            -- `hω` gives not-halted at every `k' ≤ k`; specialize to `n`
            have hnk' : n ≤ k := by omega
            exact hω n hnk'
          have hrec : (localState M (tileBlock P j T) x n ω).1 = x :=
            hft.2 (by simpa [hs, localState, machineState] using ha0) hrun_n
          simpa [hsq] using hrec
        obtain ⟨hr1, hr2⟩ := tileQuery_reads_haltPattern P j T k x s hxx hxaborted hatt
        have hnext : (tileBlock P j T).next s = tileQuery P j T s := by
          have hrun_s : (tileBlock P j T).halted s = false := by
            have hnk : n ≤ k := by omega
            have hnk' : n < k + 1 := by omega
            -- transfer `notHalted` at `n` through the agreed prefix
            have hnol : (tileBlock P j T).halted
                (localState M (tileBlock P j T) x n ω) = false :=
              hω n (by omega)
            simpa [hs, localState, machineState] using hnol
          have h2h : s.2.halted = false := by simpa [tileBlock] using hrun_s
          simp [tileBlock, h2h]
        rw [localAnswer_congr M _ ((tileBlock P j T).next s)
          (tileHaltPattern P j T k x)
          (by rw [hnext]; exact hr1) (by rw [hnext]; exact hr2) ω ω' h1 h2]
    have hstate : ∀ n ≤ k, localState M (tileBlock P j T) x n ω =
        localState M (tileBlock P j T) x n ω' := fun n hn => by
      unfold localState machineState
      rw [hagree n hn]
    intro k' hk'
    have hkk' : k' ≤ k := hk'
    rw [← hstate k' hkk']
    exact hω k' hk'

/-- The halting-pattern discipline assembles the three proved parts: measurability of the
pattern, joint measurability of the not-halted event, and its dependence only on the
pattern (`tileHaltDependsOnly`, by coupling agreeing samples through step `k`). -/
theorem tileHaltPatternStatement_proof : TileHaltPatternStatement := by
  intro d m P j T M k
  exact ⟨tileHaltPattern_measurable P j T k, tileHaltMeasurableSet P j T M k,
    fun x => tileHaltDependsOnly P j T M k x⟩

end AndersonAC.AgentS78
