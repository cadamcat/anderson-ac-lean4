import AndersonAC.AgentS78.Construction.TileTrialHalt
import AndersonAC.AgentS78.Construction.TileRetryIndep
import AndersonAC.AgentS78.Construction.TileBlockMeasurable
import AndersonAC.AgentS78.Construction.BlockRun
import AndersonAC.AgentS78.Construction.MachineRunProof

/-!
# Retry bound from the one-trial bound
Paper: 05-local-sweeps.tex:940–961 (retries), 05:495–510 (rollback, marking, retry state).

**`tileRetry_of_trialBound : TileTrialBoundStatement d C → TileRetryStatement d C`.**

At a digit sweep before the cutoff (`j ≤ ⌊m/2⌋`) the first failure marks the whole tile
pending (`markTile`, record `xm`) and starts retry `1`; retry `a ≥ 1` starts from the record
`xm` with the committed prefix, reads only the order `π_{j,T,a}` and the auxiliary family
`a` (every active site of the tile is pending in `xm`), and never a true sign.

* Coupling (`sim_step`, `retry_fail_coupled`): the run of retry `a` on `ω` is the first trial
  from `xm` on the relabelled sample `swapω a ω` (order `0 ↔ a`, auxiliary family `0 ↔ a`),
  step by step, as long as retry `a` runs. Hence "retry `a` fails" lies in
  `swapω a ⁻¹' localFirstFail xm`.
* `reachedAttempt K ⊆ H 0 ∩ … ∩ H (K-1)` with `H 0 = localFirstFail x` (first trial) and
  `H a = swapω a ⁻¹' localFirstFail xm`.
* `H a` is decided by the coordinates `Z a` (true signs, family `0`, order `0` for `a = 0`;
  family `a`, order `a` otherwise), pairwise disjoint, so the `H a` are independent
  (`Retry.measure_inter_of_depOn`), and `swapω a` preserves the law
  (`Retry.measurePreserving_relabel`). Each factor is at most `p` by the one-trial bound at `x`
  and at `xm` (`markTile` keeps `TileGoodCore` before the final sweep).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw querySigns SignIndex Order)

/-! ## The block run as an iteration of a state map -/

section StateStep
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

/-- The answer to `c` computed from the block's own order counts. -/
def stAnswer (s : RunRecord d m × TileScratch d m) (c : Query (Torus d m))
    (ω : RandomSources (Torus d m) M) : Answer (Torus d m) := by
  classical
  exact (fun x => if x ∈ querySigns (Torus d m) c then some (ω.1 x) else none,
    match c with
    | .nextOrder o => if h : s.2.orderCount o < M o then
        some ((ω.2 o ⟨s.2.orderCount o, h⟩).val) else none
    | _ => none)

theorem localAnswer_eq_stAnswer (L : List (Query (Torus d m)))
    (s : RunRecord d m × TileScratch d m) (c : Query (Torus d m))
    (ω : RandomSources (Torus d m) M)
    (h : ∀ o, L.count (Query.nextOrder o) = s.2.orderCount o) :
    localAnswer (Torus d m) M L c ω = stAnswer M s c ω := by
  unfold localAnswer stAnswer
  refine Prod.ext rfl ?_
  cases c with
  | nextOrder o => simp only [h o]
  | _ => rfl

/-- One step of the block, with answers from the state's own order counts. -/
def stepF (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m) :
    RunRecord d m × TileScratch d m :=
  (tileBlock P j T).update s (stAnswer M s ((tileBlock P j T).next s) ω)

theorem enter_orderCount (x : RunRecord d m) (o : ℕ) :
    ((tileBlock P j T).enter x).2.orderCount o = 0 := by
  simp only [tileBlock]; split_ifs <;> rfl

theorem run_count (x : RunRecord d m) (ω : RandomSources (Torus d m) M) (k o : ℕ) :
    (machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update k ω).2.count (Query.nextOrder o) =
      (localState M (tileBlock P j T) x k ω).2.orderCount o := by
  induction k with
  | zero =>
    show ([] : List (Query (Torus d m))).count _ = ((tileBlock P j T).enter x).2.orderCount o
    rw [enter_orderCount]; rfl
  | succ k ih =>
    rw [machineRun_succ, List.count_append, ih, localState_succ]
    set s := localState M (tileBlock P j T) x k ω with hs
    have hs' : (machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update k ω).1 = s := rfl
    rw [hs']
    by_cases hh : s.2.halted = true
    · rw [tileBlock_update_halted P j T s _ hh]
      have : (tileBlock P j T).next s = Query.decision := by simp [tileBlock, hh]
      rw [this]; simp
    · have hf : s.2.halted = false := by simpa using hh
      rw [tileBlock_update_running P j T s _ hf, (tileStep_keeps P j T _ _ _).1.orderCount,
        tileBlock_next_running P j T s hf]
      by_cases hq : tileQuery P j T s = Query.nextOrder o
      · simp [hq, logQuery]
      · have hq' : (tileQuery P j T s == Query.nextOrder o) = false := by
          rw [beq_eq_false_iff_ne]; exact hq
        simp [logQuery, hq]

theorem localState_succ_stepF (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) :
    localState M (tileBlock P j T) x (k + 1) ω =
      stepF P j T M ω (localState M (tileBlock P j T) x k ω) := by
  rw [localState_succ, stepF, localAnswer_eq_stAnswer]
  exact fun o => run_count P j T M x ω k o

theorem localState_add (x : RunRecord d m) (n k : ℕ) (ω : RandomSources (Torus d m) M) :
    localState M (tileBlock P j T) x (n + k) ω =
      (stepF P j T M ω)^[k] (localState M (tileBlock P j T) x n ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, localState_succ_stepF, ih, Function.iterate_succ_apply']

theorem stepF_halted (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m)
    (h : s.2.halted = true) : stepF P j T M ω s = s :=
  tileBlock_update_halted P j T s _ h

end StateStep

/-! ## Structure of the run from a record: trials, marking, retry starts -/

section RunFacts
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

/-- The record after the first-trial failure: the whole tile marked pending (05:512–514). -/
def tileMark (x : RunRecord d m) : RunRecord d m :=
  markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ x

theorem tileStep_eq_failTrial (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (a : Answer (Torus d m)) (h : (tileStep P j T s q a).2.attempt ≠ s.2.attempt) :
    tileStep P j T s q a = failTrial P j T s := by
  have hsc : ∀ i ζ, (scalarStep P j T s i ζ).2.attempt ≠ s.2.attempt →
      scalarStep P j T s i ζ = failTrial P j T s := by
    intro i ζ hne
    rcases scalarStep_cases P j T s i ζ with ⟨ha, -⟩ | hf
    · exact absurd ha hne
    · exact hf
  revert h
  unfold tileStep
  rcases q with ⟨i, hh⟩ | k | ⟨i, hh⟩ | o | _
  · rcases s.2.site with _ | i'
    · intro h; exact absurd rfl h
    · exact hsc i' _
  · rcases s.2.site with _ | i'
    · intro h; exact absurd rfl h
    · exact hsc i' _
  · rcases s.2.site with _ | i'
    · intro h; exact absurd rfl h
    · exact hsc i' _
  · intro h; exact absurd rfl h
  · rcases s.2.site with _ | i'
    · intro h; exact absurd rfl h
    · intro h; exact absurd rfl h

theorem failTrial_eq (hj : ¬ m / 2 < j) (s : RunRecord d m × TileScratch d m) :
    failTrial P j T s =
      (if s.2.attempt = 0 then tileMark P j T s.1 else s.1,
        { trialScratch (if s.2.attempt = 0 then tileMark P j T s.1 else s.1) s.2
            (s.2.attempt + 1) with firstFail := true }) := by
  unfold failTrial tileMark
  simp only [hj, if_false]

/-- The query log of a step touches only the current trial's order and family. -/
theorem logQuery_future (s : RunRecord d m × TileScratch d m) (b : ℕ) (hb : s.2.attempt < b) :
    (logQuery (tileQuery P j T s) s.2).orderCount (tileOrderIndex j T b) =
        s.2.orderCount (tileOrderIndex j T b) ∧
      ∀ i : Torus d m, (logQuery (tileQuery P j T s) s.2).auxUsed (tileAuxIndex j T b i) =
        s.2.auxUsed (tileAuxIndex j T b i) := by
  refine ⟨?_, fun i => ?_⟩
  · have hne : tileQuery P j T s ≠ Query.nextOrder (tileOrderIndex j T b) := by
      intro h
      have := (tileOrderIndex_injective (tileQuery_nextOrder P j T s _ h).1).2.2
      omega
    simp [logQuery, hne]
  · have hne : tileQuery P j T s ≠ Query.auxiliary (tileAuxIndex j T b i) := by
      intro h
      obtain ⟨⟨i', hi'⟩, -⟩ := tileQuery_auxiliary P j T s _ h
      have := (tileAuxIndex_injective hi').2.2.1
      omega
    simp [logQuery, hne]

/-- Invariant of the run from `x` at a digit sweep before the cutoff. -/
def RetryInv (x : RunRecord d m) (s : RunRecord d m × TileScratch d m) : Prop :=
  (∀ b, s.2.attempt < b → s.2.orderCount (tileOrderIndex j T b) = 0 ∧
      ∀ i : Torus d m, s.2.auxUsed (tileAuxIndex j T b i) = false) ∧
    (s.2.halted = false → s.2.attempt = 0 → s.1 = x) ∧
    (s.2.halted = false → s.2.attempt ≠ 0 → s.1 = tileMark P j T x)

theorem retryInv_enter (x : RunRecord d m) (hab : x.aborted = false) :
    RetryInv P j T x ((tileBlock P j T).enter x) := by
  simp only [RetryInv, tileBlock, hab, Bool.false_eq_true, if_false]
  refine ⟨fun b _ => ⟨rfl, fun _ => rfl⟩, ?_, ?_⟩ <;> simp [initScratch]

/-- One step of the running block: same trial, or a failure starting the next retry. -/
theorem update_cases (hj : ¬ m / 2 < j) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) :
    (tileBlock P j T).update s a = s ∨
    (s.2.halted = false ∧
      (tileBlock P j T).update s a =
        tileStep P j T (s.1, logQuery (tileQuery P j T s) s.2) (tileQuery P j T s) a ∧
      ((tileBlock P j T).update s a).2.attempt = s.2.attempt ∧
      ((tileBlock P j T).update s a).2.orderCount = (logQuery (tileQuery P j T s) s.2).orderCount ∧
      ((tileBlock P j T).update s a).2.auxUsed = (logQuery (tileQuery P j T s) s.2).auxUsed ∧
      (((tileBlock P j T).update s a).2.halted = false →
        ((tileBlock P j T).update s a).1 = s.1)) ∨
    (s.2.halted = false ∧
      (tileBlock P j T).update s a = failTrial P j T (s.1, logQuery (tileQuery P j T s) s.2) ∧
      ((tileBlock P j T).update s a).2.attempt = s.2.attempt + 1) := by
  by_cases hh : s.2.halted = true
  · exact Or.inl (tileBlock_update_halted P j T s a hh)
  have hf : s.2.halted = false := by simpa using hh
  right
  rw [tileBlock_update_running P j T s a hf]
  set s₀ : RunRecord d m × TileScratch d m := (s.1, logQuery (tileQuery P j T s) s.2)
  have hk := tileStep_keeps P j T s₀ (tileQuery P j T s) a
  by_cases hatt : (tileStep P j T s₀ (tileQuery P j T s) a).2.attempt = s₀.2.attempt
  · left
    refine ⟨hf, rfl, hatt, hk.1.orderCount, hk.1.auxUsed, fun hh' => ?_⟩
    rcases hk.2 with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨e1, -⟩
    · exact e1
    · rw [e1] at hh'; exact absurd hh' (by simp)
    · exact absurd e1 (by rw [hatt]; omega)
  · right
    have he := tileStep_eq_failTrial P j T s₀ _ a hatt
    refine ⟨hf, he, ?_⟩
    rw [he, failTrial_eq P j T hj]
    rfl

theorem retryInv_update (hj : ¬ m / 2 < j) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) (a : Answer (Torus d m))
    (h : RetryInv P j T x s) : RetryInv P j T x ((tileBlock P j T).update s a) := by
  rcases update_cases P j T hj s a with he | ⟨hf, -, hatt, hoc, hau, hrec⟩ | ⟨hf, he, hatt⟩
  · rw [he]; exact h
  · refine ⟨fun b hb => ?_, fun hh ha => ?_, fun hh ha => ?_⟩
    · rw [hatt] at hb
      obtain ⟨h1, h2⟩ := logQuery_future P j T s b hb
      refine ⟨by rw [hoc, h1]; exact (h.1 b hb).1, fun i => ?_⟩
      rw [hau, h2 i]; exact (h.1 b hb).2 i
    · rw [hrec hh]; exact h.2.1 hf (by rw [← hatt]; exact ha)
    · rw [hrec hh]; exact h.2.2 hf (by rw [← hatt]; exact ha)
  · have hfe := failTrial_eq P j T hj (s.1, logQuery (tileQuery P j T s) s.2)
    refine ⟨fun b hb => ?_, fun _ ha => ?_, fun _ _ => ?_⟩
    · rw [hatt] at hb
      have hb' : s.2.attempt < b := by omega
      obtain ⟨h1, h2⟩ := logQuery_future P j T s b hb'
      rw [he, hfe]
      refine ⟨?_, fun i => ?_⟩
      · show (logQuery (tileQuery P j T s) s.2).orderCount _ = 0
        rw [h1]; exact (h.1 b hb').1
      · show (logQuery (tileQuery P j T s) s.2).auxUsed _ = false
        rw [h2 i]; exact (h.1 b hb').2 i
    · rw [hatt] at ha; exact absurd ha (Nat.succ_ne_zero _)
    · rw [he, hfe]
      show (if (logQuery (tileQuery P j T s) s.2).attempt = 0 then tileMark P j T s.1 else s.1) = _
      have : (logQuery (tileQuery P j T s) s.2).attempt = s.2.attempt := rfl
      rw [this]
      split_ifs with h0
      · rw [h.2.1 hf h0]
      · exact h.2.2 hf h0

theorem retryInv_run (hj : ¬ m / 2 < j) (x : RunRecord d m) (hab : x.aborted = false)
    (k : ℕ) (ω : RandomSources (Torus d m) M) :
    RetryInv P j T x (localState M (tileBlock P j T) x k ω) :=
  localState_induct M (tileBlock P j T) x (RetryInv P j T x) (retryInv_enter P j T x hab)
    (fun s a hs => retryInv_update P j T hj x s a hs) k ω

end RunFacts

/-! ## One step, case by case -/

section Cases
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

theorem stepF_running (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m)
    (hh : s.2.halted = false) :
    stepF P j T M ω s = tileStep P j T (s.1, logQuery (tileQuery P j T s) s.2)
      (tileQuery P j T s) (stAnswer M s (tileQuery P j T s) ω) := by
  unfold stepF
  rw [tileBlock_next_running P j T s hh, tileBlock_update_running P j T s _ hh]

theorem tileQuery_none (s : RunRecord d m × TileScratch d m) (hs : s.2.site = none) :
    tileQuery P j T s =
      if s.2.orderCount (tileOrderIndex j T s.2.attempt) < (TS P j T).card then
        Query.nextOrder (tileOrderIndex j T s.2.attempt) else Query.decision := by
  unfold tileQuery; rw [hs]

theorem tileQuery_inactive (s : RunRecord d m × TileScratch d m) (i : Torus d m)
    (hs : s.2.site = some i) (hi : ¬ activeIn P j T s.1 i) :
    tileQuery P j T s = Query.decision := by
  unfold tileQuery; rw [hs]; simp only [hi, if_false]

theorem tileQuery_aux (s : RunRecord d m × TileScratch d m) (i : Torus d m)
    (hs : s.2.site = some i) (hi : activeIn P j T s.1 i) (hu : ¬ usesTrue s i) :
    tileQuery P j T s = if s.2.auxUsed (tileAuxIndex j T s.2.attempt i) = true then
      Query.decision else Query.auxiliary (tileAuxIndex j T s.2.attempt i) := by
  unfold tileQuery; rw [hs]; simp only [hi, hu, if_true, if_false]

theorem tileIncrement_aux (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m)
    (k : ℕ) :
    tileIncrement P j (Query.auxiliary k) (stAnswer M s (Query.auxiliary k) ω) =
      digitAmp P.u (j - 1) * S2.signValue (ω.1 (Sum.inr k)) := by
  simp [tileIncrement, answeredSign, stAnswer, querySigns]

theorem exposedSite_congr (s s' : RunRecord d m × TileScratch d m) (h1 : s.1 = s'.1)
    (h2 : s.2.seq = s'.2.seq) (v : Option ℕ) :
    exposedSite P j T s v = exposedSite P j T s' v := by
  unfold exposedSite; rw [h1, h2]

end Cases

/-! ## The coupling of retry `a` with the first trial from the marked record -/

section Coupling
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

/-- Retry state `s` (trial `a`, record `xm`) and first-trial state `s'` (record `xm`) agree
on everything the trial reads and writes. -/
structure SimRel (xm : RunRecord d m) (a : ℕ) (s s' : RunRecord d m × TileScratch d m) :
    Prop where
  record : s.1 = xm
  record' : s'.1 = xm
  seq : s.2.seq = s'.2.seq
  site : s.2.site = s'.2.site
  added : s.2.added = s'.2.added
  consumed : s.2.consumed = s'.2.consumed
  halted : s.2.halted = false
  halted' : s'.2.halted = false
  att : s.2.attempt = a
  att' : s'.2.attempt = 0
  ff' : s'.2.firstFail = false
  count : s.2.orderCount (tileOrderIndex j T a) = s'.2.orderCount (tileOrderIndex j T 0)
  aux : ∀ i : Torus d m, s.2.auxUsed (tileAuxIndex j T a i) = s'.2.auxUsed (tileAuxIndex j T 0 i)

/-- **One coupled step.** -/
theorem sim_step (hj : ¬ m / 2 < j) (xm : RunRecord d m)
    (hpend : ∀ i ∈ TS P j T, i ∈ xm.endpoint.active → i ∈ xm.pending)
    (a : ℕ) (ha : a ≠ 0) (ω ω' : RandomSources (Torus d m) M)
    (hMa : M (tileOrderIndex j T a) = M (tileOrderIndex j T 0))
    (hord : ∀ (c : ℕ) (h : c < M (tileOrderIndex j T a)) (h' : c < M (tileOrderIndex j T 0)),
      ((ω.2 (tileOrderIndex j T a)) ⟨c, h⟩ : ℕ) = ((ω'.2 (tileOrderIndex j T 0)) ⟨c, h'⟩ : ℕ))
    (hsign : ∀ i : Torus d m,
      ω.1 (Sum.inr (tileAuxIndex j T a i)) = ω'.1 (Sum.inr (tileAuxIndex j T 0 i)))
    (s s' : RunRecord d m × TileScratch d m) (hR : SimRel P j T xm a s s') :
    SimRel P j T xm a (stepF P j T M ω s) (stepF P j T M ω' s') ∨
    ((stepF P j T M ω s).2.halted = true ∧ (stepF P j T M ω s).2.attempt = a) ∨
    ((stepF P j T M ω s).2.attempt = a + 1 ∧ (stepF P j T M ω' s').2.firstFail = true) := by
  rcases s with ⟨r1, ⟨att, seq, site, added, consumed, halted, ff, oc, au⟩⟩
  rcases s' with ⟨r2, ⟨att', seq', site', added', consumed', halted', ff', oc', au'⟩⟩
  obtain ⟨hr, hr', hseq, hsite, hadd, hcons, hh, hh', hatt, hatt', hff', hc, hau⟩ := hR
  simp only at hr hr' hseq hsite hadd hcons hh hh' hatt hatt' hff' hc hau
  subst r1 r2 seq' site' added' consumed' halted halted' att att' ff'
  rw [stepF_running P j T M ω _ rfl, stepF_running P j T M ω' _ rfl]
  cases site with
  | none =>
    rw [tileQuery_none P j T _ rfl, tileQuery_none P j T _ rfl]
    simp only
    by_cases hlt : oc (tileOrderIndex j T a) < (TS P j T).card
    · have hlt' : oc' (tileOrderIndex j T 0) < (TS P j T).card := by rw [← hc]; exact hlt
      rw [if_pos hlt, if_pos hlt']
      have hans : (stAnswer M (xm, ⟨a, seq, none, added, consumed, false, ff, oc, au⟩)
            (Query.nextOrder (tileOrderIndex j T a)) ω).2 =
          (stAnswer M (xm, ⟨0, seq, none, added, consumed, false, false, oc', au'⟩)
            (Query.nextOrder (tileOrderIndex j T 0)) ω').2 := by
        simp only [stAnswer]
        by_cases hm : oc (tileOrderIndex j T a) < M (tileOrderIndex j T a)
        · have hm' : oc' (tileOrderIndex j T 0) < M (tileOrderIndex j T 0) := by
            rw [← hc, ← hMa]; exact hm
          rw [dif_pos hm, dif_pos hm']
          congr 1
          have := hord _ hm (hc ▸ hm')
          rw [this]
          congr 2
          exact Fin.ext hc
        · have hm' : ¬ oc' (tileOrderIndex j T 0) < M (tileOrderIndex j T 0) := by
            rw [← hc, ← hMa]; exact hm
          rw [dif_neg hm, dif_neg hm']
      left
      refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simp only [tileStep]
        rw [hans]
        exact exposedSite_congr P j T _ _ rfl rfl _
      · simp [tileStep, logQuery, hc]
      · intro i; simp [tileStep, logQuery, hau i]
    · rw [if_neg hlt, if_neg (by rw [← hc]; exact hlt)]
      right; left
      simp [tileStep, logQuery]
  | some i =>
    by_cases hact : activeIn P j T xm i
    · have hu : ¬ usesTrue (xm, ⟨a, seq, some i, added, consumed, false, ff, oc, au⟩) i :=
        fun h => ha h.1
      have hu' : ¬ usesTrue (xm, ⟨0, seq, some i, added, consumed, false, false, oc', au'⟩) i :=
        fun h => h.2 (hpend i hact.1 hact.2.1)
      rw [tileQuery_aux P j T _ i rfl hact hu, tileQuery_aux P j T _ i rfl hact hu']
      simp only
      by_cases hused : au (tileAuxIndex j T a i) = true
      · have hused' : au' (tileAuxIndex j T 0 i) = true := by rw [← hau i]; exact hused
        rw [if_pos hused, if_pos hused']
        left
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · simp [tileStep, logQuery, hc]
        · intro i'; simp [tileStep, logQuery, hau i']
      · have hused' : ¬ au' (tileAuxIndex j T 0 i) = true := by rw [← hau i]; exact hused
        rw [if_neg hused, if_neg hused']
        simp only [tileStep]
        rw [tileIncrement_aux, tileIncrement_aux, ← hsign i]
        simp only [logQuery]
        unfold scalarStep
        simp only
        have hp : i ∈ xm.pending := hpend i hact.1 hact.2.1
        by_cases hok : trialOk P j T xm (extendSeq seq (stepLive (sweepScale P.u m j)
            (portR (sweepTheta P.u m j) xm.r) (seq.state seq.length) (i, false)
            (digitAmp P.u (j - 1) * S2.signValue (ω.1 (Sum.inr (tileAuxIndex j T a i))) /
              √(sweepW P.u m j))) (i, false)
            (digitAmp P.u (j - 1) * S2.signValue (ω.1 (Sum.inr (tileAuxIndex j T a i))) /
              √(sweepW P.u m j)))
            (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) xm.r) (seq.state seq.length)
              (i, false) (digitAmp P.u (j - 1) * S2.signValue (ω.1 (Sum.inr (tileAuxIndex j T a i))) /
                √(sweepW P.u m j)))
        · rw [if_pos hok, if_pos hok]
          left
          refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
          · simp [usesTrue, ha, hp]
          · simp [hc]
          · intro i'
            simp only
            rw [hau i']
            congr 1
            simp only [Query.auxiliary.injEq, decide_eq_decide]
            constructor
            · intro h; rw [(tileAuxIndex_injective h).2.2.2]
            · intro h; rw [(tileAuxIndex_injective h).2.2.2]
        · rw [if_neg hok, if_neg hok]
          right; right
          rw [failTrial_eq P j T hj, failTrial_eq P j T hj]
          simp [trialScratch, ha]
    · rw [tileQuery_inactive P j T _ i rfl hact, tileQuery_inactive P j T _ i rfl hact]
      left
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simp [tileStep, logQuery, hc]
      · intro i'; simp [tileStep, logQuery, hau i']

end Coupling

/-! ## The relabelling `order 0 ↔ a`, `family 0 ↔ a` -/

section Swap

/-- Exchange the auxiliary families `0` and `a` of tile `T` of sweep `j` (on all indices of
the form `tileAuxIndex j T b r`, any `r`). -/
def famSwap (j T a n : ℕ) : ℕ :=
  if n.unpair.1 = 0 ∧ n.unpair.2.unpair.1.unpair.1 = Nat.pair j T ∧
      n.unpair.2.unpair.1.unpair.2 = 0 then
    Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair j T) a) n.unpair.2.unpair.2)
  else if n.unpair.1 = 0 ∧ n.unpair.2.unpair.1.unpair.1 = Nat.pair j T ∧
      n.unpair.2.unpair.1.unpair.2 = a then
    Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair j T) 0) n.unpair.2.unpair.2)
  else n

theorem famSwap_pair (j T a b r : ℕ) :
    famSwap j T a (Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair j T) b) r)) =
      Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair j T)
        (if b = 0 then a else if b = a then 0 else b)) r) := by
  unfold famSwap
  simp only [Nat.unpair_pair, true_and]
  by_cases h0 : b = 0
  · simp [h0]
  · by_cases ha : b = a
    · subst ha; simp [h0]
    · simp [h0, ha]

theorem famSwap_decomp (n : ℕ) : n = Nat.pair n.unpair.1
    (Nat.pair (Nat.pair n.unpair.2.unpair.1.unpair.1 n.unpair.2.unpair.1.unpair.2)
      n.unpair.2.unpair.2) := by
  simp [Nat.pair_unpair]

theorem famSwap_other (j T a n : ℕ)
    (h : ¬ ∃ b r, n = Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair j T) b) r)) :
    famSwap j T a n = n := by
  unfold famSwap
  split_ifs with h1 h2
  · exfalso; apply h
    refine ⟨n.unpair.2.unpair.1.unpair.2, n.unpair.2.unpair.2, ?_⟩
    conv_lhs => rw [famSwap_decomp n]
    rw [h1.1, h1.2.1]
  · exfalso; apply h
    refine ⟨n.unpair.2.unpair.1.unpair.2, n.unpair.2.unpair.2, ?_⟩
    conv_lhs => rw [famSwap_decomp n]
    rw [h2.1, h2.2.1]
  · rfl

theorem famSwap_involutive (j T a : ℕ) : Function.Involutive (famSwap j T a) := by
  intro n
  by_cases h : ∃ b r, n = Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair j T) b) r)
  · obtain ⟨b, r, rfl⟩ := h
    rw [famSwap_pair, famSwap_pair]
    congr 3
    by_cases h0 : b = 0
    · subst h0
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha]
    · by_cases ha : b = a
      · subst ha; simp [h0]
      · simp [h0, ha]
  · rw [famSwap_other j T a n h, famSwap_other j T a n h]

theorem famSwap_aux_zero {d m : ℕ} (j T a : ℕ) (i : Torus d m) :
    famSwap j T a (tileAuxIndex j T 0 i) = tileAuxIndex j T a i := by
  unfold tileAuxIndex
  rw [famSwap_pair]; simp

variable {d m : ℕ}

/-- The sign relabelling: auxiliary families `0 ↔ a`. -/
def auxPerm (d m j T a : ℕ) : Equiv.Perm (SignIndex (Torus d m)) :=
  Equiv.sumCongr (Equiv.refl _) (famSwap_involutive j T a).toPerm

/-- The order relabelling: `π_{j,T,0} ↔ π_{j,T,a}`. -/
def ordPerm (j T a : ℕ) : Equiv.Perm ℕ := Equiv.swap (tileOrderIndex j T 0) (tileOrderIndex j T a)

theorem ordPerm_sizes {P : TilePlan d m} {j : ℕ} {T : Fin (P.cover j).cover.count} {M : ℕ → ℕ}
    (hsz : TileOrderSizes P j T M) (a : ℕ) : ∀ o, M (ordPerm j T a o) = M o := by
  intro o
  unfold ordPerm
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hsz, hsz]
  · rw [h2, hsz, hsz]
  · rfl

/-- The relabelled sample: retry `a` of `ω` read as a first trial. -/
def swapω {P : TilePlan d m} {j : ℕ} {T : Fin (P.cover j).cover.count} {M : ℕ → ℕ}
    (hsz : TileOrderSizes P j T M) (a : ℕ) (ω : RandomSources (Torus d m) M) :
    RandomSources (Torus d m) M :=
  Retry.relabel (auxPerm d m j T a) (ordPerm j T a) (ordPerm_sizes hsz a) ω

theorem swapω_sign {P : TilePlan d m} {j : ℕ} {T : Fin (P.cover j).cover.count} {M : ℕ → ℕ}
    (hsz : TileOrderSizes P j T M) (a : ℕ) (ω : RandomSources (Torus d m) M) (i : Torus d m) :
    (swapω hsz a ω).1 (Sum.inr (tileAuxIndex j T 0 i)) = ω.1 (Sum.inr (tileAuxIndex j T a i)) := by
  show ω.1 (auxPerm d m j T a (Sum.inr (tileAuxIndex j T 0 i))) = _
  simp only [auxPerm, Equiv.sumCongr_apply, Sum.map_inr, Function.Involutive.coe_toPerm]
  rw [famSwap_aux_zero]

theorem order_val_congr {M : ℕ → ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω : RandomSources ι M) {o1 o2 : ℕ} (h : o1 = o2) (c : ℕ) (h1 : c < M o1) (h2 : c < M o2) :
    ((ω.2 o1) ⟨c, h1⟩ : ℕ) = ((ω.2 o2) ⟨c, h2⟩ : ℕ) := by
  subst h; rfl

theorem swapω_order {P : TilePlan d m} {j : ℕ} {T : Fin (P.cover j).cover.count} {M : ℕ → ℕ}
    (hsz : TileOrderSizes P j T M) (a : ℕ) (ω : RandomSources (Torus d m) M) (c : ℕ)
    (h : c < M (tileOrderIndex j T a)) (h' : c < M (tileOrderIndex j T 0)) :
    ((ω.2 (tileOrderIndex j T a)) ⟨c, h⟩ : ℕ) =
      (((swapω hsz a ω).2 (tileOrderIndex j T 0)) ⟨c, h'⟩ : ℕ) := by
  rw [swapω, Retry.relabel_snd_val]
  exact order_val_congr ω (by simp [ordPerm]) c _ _

theorem swapω_order_eq {P : TilePlan d m} {j : ℕ} {T : Fin (P.cover j).cover.count}
    {M : ℕ → ℕ} (hsz : TileOrderSizes P j T M) (a : ℕ) (ω ω' : RandomSources (Torus d m) M)
    (h : ω.2 (tileOrderIndex j T a) = ω'.2 (tileOrderIndex j T a)) :
    (swapω hsz a ω).2 (tileOrderIndex j T 0) = (swapω hsz a ω').2 (tileOrderIndex j T 0) := by
  have he : ordPerm j T a (tileOrderIndex j T 0) = tileOrderIndex j T a := by simp [ordPerm]
  have h' : ω.2 (ordPerm j T a (tileOrderIndex j T 0)) =
      ω'.2 (ordPerm j T a (tileOrderIndex j T 0)) := by rw [he]; exact h
  show Retry.castOrd _ (ω.2 (ordPerm j T a (tileOrderIndex j T 0))) =
    Retry.castOrd _ (ω'.2 (ordPerm j T a (tileOrderIndex j T 0)))
  rw [h']

end Swap

/-! ## Run-level coupling -/

section RunCoupling
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

abbrev runSt (x : RunRecord d m) (ω : RandomSources (Torus d m) M) (n : ℕ) :
    RunRecord d m × TileScratch d m :=
  localState M (tileBlock P j T) x n ω

theorem run_halted_persist (x : RunRecord d m) (ω : RandomSources (Torus d m) M) (n : ℕ)
    (h : (runSt P j T M x ω n).2.halted = true) :
    ∀ k, runSt P j T M x ω (n + k) = runSt P j T M x ω n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, runSt, localState_succ_stepF, ← runSt, ih]
    exact stepF_halted P j T M ω _ h

theorem run_attempt_step (hj : ¬ m / 2 < j) (x : RunRecord d m)
    (ω : RandomSources (Torus d m) M) (n : ℕ) :
    (runSt P j T M x ω (n + 1)).2.attempt = (runSt P j T M x ω n).2.attempt ∨
    ((runSt P j T M x ω (n + 1)).2.attempt = (runSt P j T M x ω n).2.attempt + 1 ∧
      (runSt P j T M x ω n).2.halted = false ∧
      runSt P j T M x ω (n + 1) = failTrial P j T ((runSt P j T M x ω n).1,
        logQuery (tileQuery P j T (runSt P j T M x ω n)) (runSt P j T M x ω n).2)) := by
  rw [runSt, localState_succ_stepF, ← runSt]
  unfold stepF
  rcases update_cases P j T hj (runSt P j T M x ω n) (stAnswer M (runSt P j T M x ω n)
      ((tileBlock P j T).next (runSt P j T M x ω n)) ω) with he | ⟨-, -, hatt, -⟩ | ⟨hf, he, hatt⟩
  · left; rw [he]
  · left; exact hatt
  · right; exact ⟨hatt, hf, he⟩

theorem run_attempt_mono (hj : ¬ m / 2 < j) (x : RunRecord d m)
    (ω : RandomSources (Torus d m) M) (n k : ℕ) :
    (runSt P j T M x ω n).2.attempt ≤ (runSt P j T M x ω (n + k)).2.attempt := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [← Nat.add_assoc]
    rcases run_attempt_step P j T M hj x ω (n + k) with h | ⟨h, -⟩ <;> omega

theorem run_attempt_zero (x : RunRecord d m) (ω : RandomSources (Torus d m) M) :
    (runSt P j T M x ω 0).2.attempt = 0 := by
  show ((tileBlock P j T).enter x).2.attempt = 0
  simp only [tileBlock]; split_ifs <;> rfl

/-- Before the first time `b ≤ attempt`, the run is still running (if it reaches `b`). -/
theorem run_running_before (x : RunRecord d m)
    (ω : RandomSources (Torus d m) M) (N n : ℕ) (hn : n < N) (b : ℕ)
    (hN : b ≤ (runSt P j T M x ω N).2.attempt) (hlt : (runSt P j T M x ω n).2.attempt < b) :
    (runSt P j T M x ω n).2.halted = false := by
  by_contra hh
  have hh' : (runSt P j T M x ω n).2.halted = true := by simpa using hh
  have := run_halted_persist P j T M x ω n hh' (N - n)
  rw [Nat.add_sub_cancel' hn.le] at this
  rw [this] at hN; omega

/-- **First-trial failure.** Reaching trial `1` means the first trial failed. -/
theorem first_fail_of_reached (x : RunRecord d m)
    (ω : RandomSources (Torus d m) M) (hω : ω ∈ reachedAttempt P j T M x 1) :
    ω ∈ localFirstFail M (tileBlock P j T) x := by
  classical
  obtain ⟨N, hN⟩ := hω
  have hex : ∃ n, 1 ≤ (runSt P j T M x ω n).2.attempt := ⟨N, hN⟩
  set N₁ := Nat.find hex
  have hN₁ : 1 ≤ (runSt P j T M x ω N₁).2.attempt := Nat.find_spec hex
  refine ⟨N₁, fun k hk => ?_, ?_⟩
  · have hlt : (runSt P j T M x ω k).2.attempt < 1 := by
      have := Nat.find_min hex hk; omega
    exact run_running_before P j T M x ω N₁ k hk 1 hN₁ hlt
  · have hinv : FirstTrialInv x (runSt P j T M x ω N₁) :=
      localState_induct M (tileBlock P j T) x (FirstTrialInv x) (firstTrialInv_enter P j T x)
        (fun s a hs => firstTrialInv_update P j T x s a hs) N₁ ω
    exact hinv.1 (by omega)

theorem tileMark_pending (x : RunRecord d m) :
    ∀ i ∈ TS P j T, i ∈ (tileMark P j T x).endpoint.active → i ∈ (tileMark P j T x).pending := by
  intro i hi ha
  simp only [tileMark, markTile] at ha ⊢
  exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, ha⟩)

theorem tileMark_aborted (x : RunRecord d m) : (tileMark P j T x).aborted = x.aborted := rfl

/-- **Retry failure.** Reaching trial `b + 1` (`b ≥ 1`) means that retry `b` failed, and then
the first trial from the marked record fails on the relabelled sample. -/
theorem retry_fail_of_reached (hj : ¬ m / 2 < j) (x : RunRecord d m) (hab : x.aborted = false)
    (hsz : TileOrderSizes P j T M) (b : ℕ) (hb : b ≠ 0) (ω : RandomSources (Torus d m) M)
    (hω : ω ∈ reachedAttempt P j T M x (b + 1)) :
    swapω hsz b ω ∈ localFirstFail M (tileBlock P j T) (tileMark P j T x) := by
  classical
  set xm := tileMark P j T x with hxm
  set ω' := swapω hsz b ω with hω'
  obtain ⟨N, hN⟩ := hω
  have hN' : b + 1 ≤ (runSt P j T M x ω N).2.attempt := hN
  have exb : ∃ n, b ≤ (runSt P j T M x ω n).2.attempt := ⟨N, by omega⟩
  have exb1 : ∃ n, b + 1 ≤ (runSt P j T M x ω n).2.attempt := ⟨N, hN⟩
  obtain ⟨Nb, hNb, hNbmin⟩ : ∃ Nb, b ≤ (runSt P j T M x ω Nb).2.attempt ∧
      ∀ n < Nb, ¬ b ≤ (runSt P j T M x ω n).2.attempt :=
    ⟨Nat.find exb, Nat.find_spec exb, fun n hn => Nat.find_min exb hn⟩
  obtain ⟨N1, hN1, hN1min⟩ : ∃ N1, b + 1 ≤ (runSt P j T M x ω N1).2.attempt ∧
      ∀ n < N1, ¬ b + 1 ≤ (runSt P j T M x ω n).2.attempt :=
    ⟨Nat.find exb1, Nat.find_spec exb1, fun n hn => Nat.find_min exb1 hn⟩
  -- the start of retry `b`
  obtain ⟨p, rfl⟩ : ∃ p, Nb = p + 1 := by
    rcases Nb with _ | p
    · rw [run_attempt_zero] at hNb; omega
    · exact ⟨p, rfl⟩
  have hAp : (runSt P j T M x ω p).2.attempt < b := by
    have := hNbmin p (Nat.lt_succ_self p); omega
  rcases run_attempt_step P j T M hj x ω p with hsame | ⟨hatt, hrun, heq⟩
  · omega
  have hAb' : (runSt P j T M x ω (p + 1)).2.attempt = b := by omega
  have hNb_le : p + 1 ≤ N1 := by
    by_contra hcon
    exact hNbmin N1 (by omega) (by omega)
  have hNb_lt : p + 1 < N1 := by
    rcases Nat.eq_or_lt_of_le hNb_le with h | h
    · rw [← h] at hN1; omega
    · exact h
  -- during retry `b`
  have hAb : ∀ k, p + 1 + k < N1 → (runSt P j T M x ω (p + 1 + k)).2.attempt = b := by
    intro k hk
    have h1 := run_attempt_mono P j T M hj x ω (p + 1) k
    have h2 := hN1min (p + 1 + k) hk
    omega
  have hrunning : ∀ n < N1, (runSt P j T M x ω n).2.halted = false := by
    intro n hn
    have : (runSt P j T M x ω n).2.attempt < b + 1 := by have := hN1min n hn; omega
    exact run_running_before P j T M x ω N1 n hn (b + 1) hN1 this
  -- the coupled start
  have hinv := retryInv_run P j T M hj x hab p ω
  have hrecp : (if (runSt P j T M x ω p).2.attempt = 0 then
      tileMark P j T (runSt P j T M x ω p).1 else (runSt P j T M x ω p).1) = xm := by
    split_ifs with h0
    · rw [hinv.2.1 hrun h0]
    · exact hinv.2.2 hrun h0
  have hfut := hinv.1 b hAp
  have hlog := logQuery_future P j T (runSt P j T M x ω p) b hAp
  have hstart : SimRel P j T xm b (runSt P j T M x ω (p + 1))
      (localState M (tileBlock P j T) xm 0 ω') := by
    rw [heq, failTrial_eq P j T hj]
    have hent : localState M (tileBlock P j T) xm 0 ω' = (xm, initScratch xm) := by
      show (tileBlock P j T).enter xm = _
      simp [tileBlock, hxm, tileMark_aborted, hab]
    rw [hent]
    have hla : (logQuery (tileQuery P j T (runSt P j T M x ω p)) (runSt P j T M x ω p).2).attempt =
        (runSt P j T M x ω p).2.attempt := rfl
    simp only [trialScratch, hla]
    refine ⟨hrecp, rfl, by rw [hrecp]; rfl, rfl, rfl, rfl, hrun, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · show (runSt P j T M x ω p).2.attempt + 1 = b; omega
    · show (logQuery _ _).orderCount _ = 0
      rw [hlog.1]; exact hfut.1
    · intro i
      show (logQuery _ _).auxUsed _ = false
      rw [hlog.2 i]; exact hfut.2 i
  -- coupled steps
  have hMa : M (tileOrderIndex j T b) = M (tileOrderIndex j T 0) := by rw [hsz, hsz]
  have hord := swapω_order hsz b ω
  have hsign : ∀ i : Torus d m, ω.1 (Sum.inr (tileAuxIndex j T b i)) =
      ω'.1 (Sum.inr (tileAuxIndex j T 0 i)) := fun i => (swapω_sign hsz b ω i).symm
  have hstep := fun s s' (hR : SimRel P j T xm b s s') =>
    sim_step P j T M hj xm (tileMark_pending P j T x) b hb ω ω' hMa hord hsign s s' hR
  have hsim : ∀ k, p + 1 + k < N1 → SimRel P j T xm b (runSt P j T M x ω (p + 1 + k))
      (localState M (tileBlock P j T) xm k ω') := by
    intro k
    induction k with
    | zero => intro _; exact hstart
    | succ k ih =>
      intro hk
      have hR := ih (by omega)
      rcases hstep _ _ hR with h | ⟨hh, -⟩ | ⟨ha1, -⟩
      · rw [← Nat.add_assoc, runSt, localState_succ_stepF, localState_succ_stepF]; exact h
      · exfalso
        have := hrunning (p + 1 + (k + 1)) hk
        rw [← Nat.add_assoc, runSt, localState_succ_stepF] at this
        rw [this] at hh; exact Bool.false_ne_true hh
      · exfalso
        have := hAb (k + 1) hk
        rw [← Nat.add_assoc, runSt, localState_succ_stepF] at this
        rw [runSt] at ha1
        omega
  -- the failing step
  obtain ⟨k0, hk0⟩ : ∃ k0, p + 1 + k0 + 1 = N1 := ⟨N1 - (p + 1) - 1, by omega⟩
  have hR0 := hsim k0 (by omega)
  rcases hstep _ _ hR0 with h | ⟨-, ha0⟩ | ⟨-, hff⟩
  · exfalso
    have := h.att
    rw [runSt, ← localState_succ_stepF, hk0] at this
    have h2 : b + 1 ≤ (localState M (tileBlock P j T) x N1 ω).2.attempt := hN1
    omega
  · exfalso
    rw [runSt, ← localState_succ_stepF, hk0] at ha0
    have h2 : b + 1 ≤ (localState M (tileBlock P j T) x N1 ω).2.attempt := hN1
    omega
  · refine ⟨k0 + 1, fun k' hk' => (hsim k' (by omega)).halted', ?_⟩
    rw [localState_succ_stepF]; exact hff

end RunCoupling

/-! ## Independence of the trial failures and the retry bound -/

section Final
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

/-- Coordinates read by trial `b`: true signs, family `0` and order `0` for the first trial;
family `b` and order `b` for retry `b`. -/
def trialCoords (d m j Tn b : ℕ) : Set (Retry.Coord (Torus d m)) :=
  if b = 0 then
    {c | (∃ p, c = Sum.inl (Sum.inl p)) ∨
      (∃ i : Torus d m, c = Sum.inl (Sum.inr (tileAuxIndex j Tn 0 i))) ∨
      c = Sum.inr (tileOrderIndex j Tn 0)}
  else
    {c | (∃ i : Torus d m, c = Sum.inl (Sum.inr (tileAuxIndex j Tn b i))) ∨
      c = Sum.inr (tileOrderIndex j Tn b)}

theorem trialCoords_disjoint (d m j Tn : ℕ) {b b' : ℕ} (hne : b ≠ b') :
    Disjoint (trialCoords d m j Tn b) (trialCoords d m j Tn b') := by
  rw [Set.disjoint_left]
  intro c hc hc'
  unfold trialCoords at hc hc'
  by_cases h0 : b = 0 <;> by_cases h0' : b' = 0
  · exact hne (h0.trans h0'.symm)
  · rw [if_pos h0] at hc; rw [if_neg h0'] at hc'
    simp only [Set.mem_setOf_eq] at hc hc'
    rcases hc with ⟨p, rfl⟩ | ⟨i, rfl⟩ | rfl <;> rcases hc' with ⟨i', h'⟩ | h' <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h'
    · exact h0' ((tileAuxIndex_injective h').2.2.1.symm)
    · exact h0' ((tileOrderIndex_injective h').2.2.symm)
  · rw [if_neg h0] at hc; rw [if_pos h0'] at hc'
    simp only [Set.mem_setOf_eq] at hc hc'
    rcases hc' with ⟨p, rfl⟩ | ⟨i, rfl⟩ | rfl <;> rcases hc with ⟨i', h'⟩ | h' <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h'
    · exact h0 ((tileAuxIndex_injective h').2.2.1.symm)
    · exact h0 ((tileOrderIndex_injective h').2.2.symm)
  · rw [if_neg h0] at hc; rw [if_neg h0'] at hc'
    simp only [Set.mem_setOf_eq] at hc hc'
    rcases hc with ⟨i, rfl⟩ | rfl <;> rcases hc' with ⟨i', h'⟩ | h' <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h'
    · exact hne (tileAuxIndex_injective h').2.2.1
    · exact hne (tileOrderIndex_injective h').2.2

/-- The failure event of trial `b`. -/
def trialFail (x : RunRecord d m) (hsz : TileOrderSizes P j T M) (b : ℕ) :
    Set (RandomSources (Torus d m) M) :=
  if b = 0 then localFirstFail M (tileBlock P j T) x
  else swapω hsz b ⁻¹' localFirstFail M (tileBlock P j T) (tileMark P j T x)

theorem localFirstFail_measurableSet (y : RunRecord d m) :
    MeasurableSet (localFirstFail M (tileBlock P j T) y) :=
  measurable_prodMk_left (localFirstFail_measurable machineRun_proof M (tileBlock P j T)
    (tileBlock_measurable P j T))

theorem trialFail_measurableSet (x : RunRecord d m) (hsz : TileOrderSizes P j T M) (b : ℕ) :
    MeasurableSet (trialFail P j T M x hsz b) := by
  unfold trialFail
  split_ifs
  · exact localFirstFail_measurableSet P j T M x
  · exact (Retry.measurePreserving_relabel _ _ _).measurable
      (localFirstFail_measurableSet P j T M _)

theorem tilePattern_aux_mem' (x : RunRecord d m) {a : ℕ} (ha : a ∈ (tilePattern P j T x).aux) :
    ∃ i : Torus d m, a = tileAuxIndex j T 0 i := by
  classical
  unfold tilePattern at ha
  split_ifs at ha
  · simp at ha
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, rfl⟩

theorem tilePattern_orders_eq' (x : RunRecord d m) {o : ℕ}
    (ho : o ∈ (tilePattern P j T x).orders) : o = tileOrderIndex j T 0 := by
  classical
  unfold tilePattern at ho
  split_ifs at ho <;> simpa using ho

theorem tilePattern_sites_mem' (x : RunRecord d m) {i : Torus d m}
    (hi : i ∈ (tilePattern P j T x).sites) :
    i ∈ TS P j T ∧ i ∈ x.endpoint.active ∧ i ∉ x.pending := by
  classical
  unfold tilePattern at hi
  split_ifs at hi
  · simp at hi
  · simp only [Finset.mem_sdiff, Finset.mem_inter] at hi
    exact ⟨hi.1.1.1, hi.1.1.2, hi.1.2⟩

theorem trialFail_depOn (x : RunRecord d m) (hsz : TileOrderSizes P j T M) (b : ℕ) :
    Retry.DepOn (trialCoords d m j T b) (trialFail P j T M x hsz b) := by
  unfold trialFail trialCoords
  by_cases h0 : b = 0
  · simp only [if_pos h0]
    intro ω ω' h1 h2
    apply tileBlock_fail_local P j T M x
    · intro z hz
      rcases hz with ⟨i, -, k, -, rfl⟩ | ⟨a, ha, rfl⟩
      · exact h1 _ (Or.inl ⟨_, rfl⟩)
      · obtain ⟨i, rfl⟩ := tilePattern_aux_mem' P j T x ha
        exact h1 _ (Or.inr (Or.inl ⟨i, rfl⟩))
    · intro o ho
      rw [tilePattern_orders_eq' P j T x ho]
      exact h2 _ (Or.inr (Or.inr rfl))
  · simp only [if_neg h0]
    intro ω ω' h1 h2
    simp only [Set.mem_preimage]
    apply tileBlock_fail_local P j T M (tileMark P j T x)
    · intro z hz
      rcases hz with ⟨i, hi, k, -, rfl⟩ | ⟨a, ha, rfl⟩
      · exfalso
        obtain ⟨h1i, h2i, h3i⟩ := tilePattern_sites_mem' P j T (tileMark P j T x) hi
        exact h3i (tileMark_pending P j T x i h1i h2i)
      · obtain ⟨i, rfl⟩ := tilePattern_aux_mem' P j T (tileMark P j T x) ha
        rw [swapω_sign, swapω_sign]
        exact h1 _ (Or.inl ⟨i, rfl⟩)
    · intro o ho
      rw [tilePattern_orders_eq' P j T (tileMark P j T x) ho]
      exact swapω_order_eq hsz b ω ω' (h2 _ (Or.inr rfl))

/-- The intersection of the first `K` trial failures. -/
def allFail (x : RunRecord d m) (hsz : TileOrderSizes P j T M) :
    ℕ → Set (RandomSources (Torus d m) M)
  | 0 => Set.univ
  | K + 1 => allFail x hsz K ∩ trialFail P j T M x hsz K

theorem allFail_measurableSet (x : RunRecord d m) (hsz : TileOrderSizes P j T M) (K : ℕ) :
    MeasurableSet (allFail P j T M x hsz K) := by
  induction K with
  | zero => exact MeasurableSet.univ
  | succ K ih => exact ih.inter (trialFail_measurableSet P j T M x hsz K)

theorem allFail_depOn (x : RunRecord d m) (hsz : TileOrderSizes P j T M) (K : ℕ) :
    Retry.DepOn {c | ∃ b < K, c ∈ trialCoords d m j T b} (allFail P j T M x hsz K) := by
  induction K with
  | zero => intro ω ω' _ _; simp [allFail]
  | succ K ih =>
    refine Retry.depOn_inter (Retry.depOn_mono ?_ ih)
      (Retry.depOn_mono ?_ (trialFail_depOn P j T M x hsz K))
    · rintro c ⟨b, hb, hc⟩; exact ⟨b, by omega, hc⟩
    · intro c hc; exact ⟨K, by omega, hc⟩

theorem allFail_le (x : RunRecord d m) (hsz : TileOrderSizes P j T M) (p : ENNReal)
    (hp : ∀ b, sourcesLaw (Torus d m) M (trialFail P j T M x hsz b) ≤ p) (K : ℕ) :
    sourcesLaw (Torus d m) M (allFail P j T M x hsz K) ≤ p ^ K := by
  induction K with
  | zero => simp [allFail]
  | succ K ih =>
    show sourcesLaw (Torus d m) M (allFail P j T M x hsz K ∩ trialFail P j T M x hsz K) ≤ _
    rw [Retry.measure_inter_of_depOn _ _ ?_ _ _ (allFail_measurableSet P j T M x hsz K)
      (trialFail_measurableSet P j T M x hsz K) (allFail_depOn P j T M x hsz K)
      (trialFail_depOn P j T M x hsz K), pow_succ]
    · exact mul_le_mul' ih (hp K)
    · rw [Set.disjoint_left]
      rintro c ⟨b, hb, hc⟩ hc'
      exact Set.disjoint_left.mp (trialCoords_disjoint d m j T (Nat.ne_of_lt hb)) hc hc'

theorem reached_subset_allFail (hj : ¬ m / 2 < j) (x : RunRecord d m) (hab : x.aborted = false)
    (hsz : TileOrderSizes P j T M) (K : ℕ) :
    reachedAttempt P j T M x K ⊆ allFail P j T M x hsz K := by
  intro ω hω
  have key : ∀ K' ≤ K, ω ∈ allFail P j T M x hsz K' := by
    intro K'
    induction K' with
    | zero => intro _; trivial
    | succ K' ih =>
      intro hK
      refine ⟨ih (by omega), ?_⟩
      have hr : ω ∈ reachedAttempt P j T M x (K' + 1) := by
        obtain ⟨k, hk⟩ := hω; exact ⟨k, by omega⟩
      unfold trialFail
      by_cases h0 : K' = 0
      · rw [if_pos h0]; subst h0
        exact first_fail_of_reached P j T M x ω hr
      · rw [if_neg h0]
        exact retry_fail_of_reached P j T M hj x hab hsz K' h0 ω hr
  exact key K le_rfl

theorem tileGoodCore_mark {C : ℝ} (x : RunRecord d m) (hnf : ¬ IsFinalSweep m j)
    (h : TileGoodCore C P j T x) : TileGoodCore C P j T (tileMark P j T x) :=
  { h with
    final_no_pending := fun hf => absurd hf hnf
    final_prefix := fun hf => absurd hf hnf }

end Final

/-- Retries (05-local-sweeps.tex:940–961). The one-trial bound implies the
retry estimates: before the cutoff, the block of a non-aborted good record reaches trial
`K` with probability at most `p^K`, `p = exp(−t^{−c})`, with the same `c, t0`. -/
theorem tileRetry_of_trialBound :
    ∀ (d : ℕ) (C : ℝ), TileTrialBoundStatement d C → TileRetryStatement d C := by
  intro d C h
  obtain ⟨c, hc, t0, ht0, hb⟩ := h
  refine ⟨c, hc, t0, ht0, ?_⟩
  intro m P j T M x hu hn0 hjm hsz hab hgood hsmall K
  have hj : ¬ m / 2 < j := by omega
  have hnf : ¬ IsFinalSweep m j := by unfold IsFinalSweep; omega
  set p := Real.exp (-S45.power (sweepScale P.u m j) (-c)) with hp
  have hp0 : 0 ≤ p := (Real.exp_pos _).le
  have hfirst : sourcesLaw (Torus d m) M (localFirstFail M (tileBlock P j T) x) ≤
      ENNReal.ofReal p := hb m P j T M x hu hn0 (by omega) hsz hab hgood hsmall
  have hmark : sourcesLaw (Torus d m) M
      (localFirstFail M (tileBlock P j T) (tileMark P j T x)) ≤ ENNReal.ofReal p :=
    hb m P j T M (tileMark P j T x) hu hn0 (by omega) hsz hab
      (tileGoodCore_mark P j T x hnf hgood) hsmall
  have htrial : ∀ b, sourcesLaw (Torus d m) M (trialFail P j T M x hsz b) ≤ ENNReal.ofReal p := by
    intro b
    unfold trialFail
    split_ifs
    · exact hfirst
    · have hmp := (Retry.measurePreserving_relabel (auxPerm d m j T b) (ordPerm j T b)
        (ordPerm_sizes hsz b)).measure_preimage
          (localFirstFail_measurableSet P j T M (tileMark P j T x)).nullMeasurableSet
      exact (le_of_eq hmp).trans hmark
  calc sourcesLaw (Torus d m) M (reachedAttempt P j T M x K)
      ≤ sourcesLaw (Torus d m) M (allFail P j T M x hsz K) :=
        measure_mono (reached_subset_allFail P j T M hj x hab hsz K)
    _ ≤ ENNReal.ofReal p ^ K := allFail_le P j T M x hsz _ htrial K
    _ = ENNReal.ofReal (p ^ K) := (ENNReal.ofReal_pow hp0 K).symm

end AndersonAC.AgentS78
