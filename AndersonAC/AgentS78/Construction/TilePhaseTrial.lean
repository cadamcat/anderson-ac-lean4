import AndersonAC.AgentS78.Construction.TilePhase

/-!
# WP10 construction, tile phase (b): one tile block keeps the tile-phase invariant

agent-s78tphase (2026-10-14). The states of the tile block of `T` reached from a record `x`
(for **any** answers, `BlockReach`) satisfy `ReachInv`: while running, the record is `x` up to
pending/latest marks (`markTile`, 05:512–514), and the scratch prefix extends `x.sweep` by
`S45.StepRel` deletions of active bit ports of `T`, each tested by `trialOk` (05:466–504):
valid at every new length, with the trial's local budget; when halted, the exit is aborted or
the commit of such a prefix (`CommitGood`). Combined with the completeness of the accepted
trial (every active bit port of `T` deleted; `TileAcceptComplete`, see INTERFACE-ISSUES 01:05:
true on real answers, false for arbitrary ones), the exit satisfies the invariant with `T`
processed: `tileBlock_keeps`.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query Answer signValue binarySuffix)

variable {d m : ℕ}

section Update
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

/-- The physical increment of a scalar slot at site `i` of the record `x` is a digit
(`|ζ| = √(3 s_{j−1}/4)`) or, at the final sweep, a true suffix from `prefixLength i`. -/
def ZetaBound (x : RunRecord d m) (i : Torus d m) (ζ : ℝ) : Prop :=
  |ζ| ≤ digitAmp P.u (j - 1) ∨
    (IsFinalSweep m j ∧ |ζ| ≤ |couplingOf P.u P.n₀| / (2 : ℝ) ^ (x.prefixLength i))

theorem exposedSite_live (s : RunRecord d m × TileScratch d m) (v : Option ℕ) (i : Torus d m)
    (h : exposedSite P j T s v = some i) :
    ((i, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live := by
  unfold exposedSite at h
  rcases v with _ | v
  · simp at h
  · simp only at h
    rcases hs : siteAt (TS P j T) v with _ | i'
    · rw [hs] at h; simp at h
    · rw [hs] at h
      simp only at h
      split_ifs at h with hc
      · cases h; exact hc.2

theorem abs_signValue (b : Bool) : |signValue b| = 1 := by
  cases b <;> simp [signValue]

theorem digitAmp_nonneg (u : ℝ) (n : ℕ) : 0 ≤ digitAmp u n := Real.sqrt_nonneg _

theorem zetaBound_digit (x : RunRecord d m) (i : Torus d m) (b : Bool) :
    ZetaBound P j x i (digitAmp P.u (j - 1) * signValue b) := by
  left
  rw [abs_mul, abs_signValue, mul_one, abs_of_nonneg (digitAmp_nonneg _ _)]

/-- The exit record of an acceptance, by its properties (robust to the form of `commitTrial`). -/
def CommitShape (s : RunRecord d m × TileScratch d m) (y : RunRecord d m) : Prop :=
  y.sweep = s.2.seq ∧ y.endpoint = s.1.endpoint ∧ y.r = s.1.r ∧ y.aborted = s.1.aborted ∧
    y.pending = s.1.pending ∧ y.installed = (fun i => s.1.installed i + s.2.added i) ∧
    ∀ i, s.2.consumed i = false →
      (i ∈ y.terminal ↔ i ∈ s.1.terminal) ∧ y.prefixLength i = s.1.prefixLength i

theorem activeIn_mem {x : RunRecord d m} {i : Torus d m} (h : activeIn P j T x i) :
    i ∈ TS P j T ∧ i ∈ x.endpoint.active := by
  unfold activeIn at h; tauto

/-- **One step of the running tile block**: four shapes. -/
theorem tile_update_cases (s : RunRecord d m × TileScratch d m) (hrun : s.2.halted = false)
    (a : Answer (Torus d m)) :
    let s' := (tileBlock P j T).update s a
    let t := sweepScale P.u m j
    let r := portR (sweepTheta P.u m j) s.1.r
    let a0 := s.2.seq.state s.2.seq.length
    -- (A) an order slot, a skip, or a no-op: only the exposed site changes
    (s'.1 = s.1 ∧ s'.2.seq = s.2.seq ∧ s'.2.halted = false ∧ s'.2.consumed = s.2.consumed ∧ s'.2.added = s.2.added ∧
      (∀ i, s'.2.site = some i → ((i, false) : Port d m) ∈ a0.live ∨ s.2.site = some i)) ∨
    -- (B) acceptance: commit of the scratch prefix
    (s'.2.halted = true ∧ CommitShape s s'.1) ∨
    -- (C) a deletion that passed the test
    (∃ i ζ, s.2.site = some i ∧ activeIn P j T s.1 i ∧ ZetaBound P j s.1 i ζ ∧
      trialOk P j T s.1
        (extendSeq s.2.seq (stepLive t r a0 ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)))
          ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)))
        (stepDen t r a0 ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j))) ∧
      s'.1 = s.1 ∧
      s'.2.seq = extendSeq s.2.seq
        (stepLive t r a0 ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)))
        ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)) ∧
      s'.2.site = none ∧ s'.2.halted = false ∧
      s'.2.added = Function.update s.2.added i (s.2.added i + ζ) ∧
      (∀ i', i' ≠ i → s'.2.consumed i' = s.2.consumed i')) ∨
    -- (D) a failed test
    (∃ sc : TileScratch d m, sc.seq = s.2.seq ∧ sc.attempt = s.2.attempt ∧
      sc.halted = s.2.halted ∧ s' = failTrial P j T (s.1, sc)) := by
  classical
  intro s' t r a0
  have hs' : s' = tileStep P j T (s.1, logQuery (tileQuery P j T s) s.2)
      (tileQuery P j T s) a := tileBlock_update_running P j T s a hrun
  clear_value s'
  subst hs'
  rcases hsite : s.2.site with _ | i
  · -- no exposed site: an order query or the acceptance decision
    have hq : tileQuery P j T s =
        if s.2.orderCount (tileOrderIndex j T s.2.attempt) < (TS P j T).card then
          Query.nextOrder (tileOrderIndex j T s.2.attempt) else Query.decision := by
      unfold tileQuery; rw [hsite]
    rw [hq]
    split_ifs with hlt
    · left
      refine ⟨rfl, rfl, hrun, rfl, rfl, fun i hi => Or.inl ?_⟩
      exact exposedSite_live P j T _ _ i hi
    · right; left
      refine ⟨by simp [tileStep, logQuery, hsite], by simp [tileStep, logQuery, hsite, commitTrial],
        by simp [tileStep, logQuery, hsite, commitTrial], by simp [tileStep, logQuery, hsite, commitTrial],
        by simp [tileStep, logQuery, hsite, commitTrial], by simp [tileStep, logQuery, hsite, commitTrial],
        by simp [tileStep, logQuery, hsite, commitTrial], fun i hi => ?_⟩
      (simp [tileStep, logQuery, hsite, commitTrial, hi]) <;> split_ifs <;> simp [hi]
  · -- an exposed site
    rw [← hsite]
    by_cases hact : activeIn P j T s.1 i
    · -- the scalar step, or the decision on a used auxiliary sign
      have hscalar : ∀ q : Query (Torus d m),
          (∀ b, ZetaBound P j s.1 i (tileIncrement P j q b)) →
          (q ≠ Query.decision) → (∀ o, q ≠ Query.nextOrder o) →
          let s' := tileStep P j T (s.1, logQuery q s.2) q a
          (s'.1 = s.1 ∧ s'.2.seq = s.2.seq ∧ s'.2.halted = false ∧
              s'.2.consumed = s.2.consumed ∧ s'.2.added = s.2.added ∧
              (∀ i', s'.2.site = some i' → ((i', false) : Port d m) ∈ a0.live ∨
                s.2.site = some i')) ∨
            (s'.2.halted = true ∧ CommitShape s s'.1) ∨
            (∃ i ζ, s.2.site = some i ∧ activeIn P j T s.1 i ∧ ZetaBound P j s.1 i ζ ∧
              trialOk P j T s.1
                (extendSeq s.2.seq (stepLive t r a0 ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)))
                  ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)))
                (stepDen t r a0 ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j))) ∧
              s'.1 = s.1 ∧
              s'.2.seq = extendSeq s.2.seq
                (stepLive t r a0 ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)))
                ((i, false) : Port d m) (ζ / Real.sqrt (sweepW P.u m j)) ∧
              s'.2.site = none ∧ s'.2.halted = false ∧
              s'.2.added = Function.update s.2.added i (s.2.added i + ζ) ∧
              (∀ i', i' ≠ i → s'.2.consumed i' = s.2.consumed i')) ∨
            (∃ sc : TileScratch d m, sc.seq = s.2.seq ∧ sc.attempt = s.2.attempt ∧
              sc.halted = s.2.halted ∧ s' = failTrial P j T (s.1, sc)) := by
        intro q hζ hdec hord
        have hstep : tileStep P j T (s.1, logQuery q s.2) q a =
            scalarStep P j T (s.1, logQuery q s.2) i (tileIncrement P j q a) := by
          rcases q with ⟨i₀, h₀⟩ | k | ⟨i₀, h₀⟩ | o | _
          · simp [tileStep, logQuery, hsite]
          · simp [tileStep, logQuery, hsite]
          · simp [tileStep, logQuery, hsite]
          · exact absurd rfl (hord o)
          · exact absurd rfl hdec
        simp only
        rw [hstep]
        unfold scalarStep
        dsimp only
        split_ifs with hok
        · right; right; left
          exact ⟨i, tileIncrement P j q a, hsite, hact, hζ a, hok, rfl, rfl, rfl, hrun, rfl,
            fun i' hi' => by simp [logQuery, Function.update_of_ne hi']⟩
        · right; right; right
          exact ⟨logQuery q s.2, rfl, rfl, rfl, rfl⟩
      have hq : tileQuery P j T s =
          if usesTrue s i then
            (if IsFinalSweep m j then Query.trueSuffix i (s.1.prefixLength i)
              else Query.trueDigit i (s.1.prefixLength i))
          else
            (if s.2.auxUsed (tileAuxIndex j T s.2.attempt i) then Query.decision
              else Query.auxiliary (tileAuxIndex j T s.2.attempt i)) := by
        unfold tileQuery; rw [hsite]; simp only [hact, if_true]
      rw [hq]
      split_ifs with hu hf hau
      · refine hscalar (Query.trueSuffix i (s.1.prefixLength i))
          (fun b => Or.inr ⟨hf, ?_⟩) (by simp) (by simp)
        simp only [tileIncrement]; exact AndersonAC.S2.binarySuffix_bound _ _ _
      · exact hscalar (Query.trueDigit i (s.1.prefixLength i))
          (fun b => by simp only [tileIncrement]; exact zetaBound_digit P j s.1 i _)
          (by simp) (by simp)
      · left
        refine ⟨?_, ?_, ?_, ?_, ?_, fun i' hi' => ?_⟩ <;> simp_all [tileStep, logQuery]
      · exact hscalar (Query.auxiliary (tileAuxIndex j T s.2.attempt i))
          (fun b => by simp only [tileIncrement]; exact zetaBound_digit P j s.1 i _)
          (by simp) (by simp)
    · have hq : tileQuery P j T s = Query.decision := by
        unfold tileQuery; rw [hsite]; simp only [hact, if_false]
      rw [hq]
      left
      refine ⟨?_, ?_, ?_, ?_, ?_, fun i' hi' => ?_⟩ <;> simp_all [tileStep, logQuery]

end Update

end AndersonAC.AgentS78

/-! ## The reach invariant of a tile block -/

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query Answer)

variable {d m : ℕ}

section Reach
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

/-- The new steps of a prefix `q` over the committed `x.sweep` are tested deletions of active
bit ports of `T` (05:338–504). -/
structure NewSteps (x : RunRecord d m) (q : S45.Sequence (Port d m)) : Prop where
  ext : SeqExtends x.sweep q
  wf : q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
  steps : ∀ k, x.sweep.length ≤ k → k < q.length → ∃ i ∈ TS P j T, i ∈ x.endpoint.active ∧
    q.pivot k = some ((i, false) : Port d m) ∧ |q.scalar k| ≤ 2 * Real.sqrt (sweepScale P.u m j)
  valid : ∀ k, x.sweep.length < k → k ≤ q.length →
    q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (stageD0 P j x) k
  budget : S45.localBudget (P.cover j).cover T
    (q.Jrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
      (Finset.Ico x.sweep.length q.length))
    (q.Lrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
      (Finset.Ico x.sweep.length q.length))
    (q.lagRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
      (Finset.Ico x.sweep.length q.length))
    (q.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) Finset.univ
      (Finset.Ico x.sweep.length q.length))
    (q.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) S45.reserves
      (Finset.Ico x.sweep.length q.length))

/-- A running state of the block of `T` entered with `x`. -/
structure TrialRun (x : RunRecord d m) (s : RunRecord d m × TileScratch d m) : Prop where
  sweep : s.1.sweep = x.sweep
  endpoint : s.1.endpoint = x.endpoint
  r : s.1.r = x.r
  aborted : s.1.aborted = false
  terminal : s.1.terminal = x.terminal
  prefixLength : s.1.prefixLength = x.prefixLength
  pending_final : IsFinalSweep m j → s.1.pending = x.pending
  seq : NewSteps P j T x s.2.seq
  site : ∀ i, s.2.site = some i →
    ((i, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live
  consumed : ∀ i, i ∉ TS P j T → s.2.consumed i = false
  installed : s.1.installed = x.installed
  added : ∀ i, s.2.added i = sweepIncrement (sweepTheta P.u m j) s.2.seq i -
    sweepIncrement (sweepTheta P.u m j) x.sweep i

/-- The exit record of an accepted trial. -/
structure CommitGood (x y : RunRecord d m) : Prop where
  endpoint : y.endpoint = x.endpoint
  r : y.r = x.r
  aborted : y.aborted = false
  outside : ∀ i, i ∉ TS P j T →
    (i ∈ y.terminal ↔ i ∈ x.terminal) ∧ y.prefixLength i = x.prefixLength i
  pending_final : IsFinalSweep m j → y.pending = x.pending
  seq : NewSteps P j T x y.sweep
  installed : ∀ i, y.installed i = x.installed i +
    (sweepIncrement (sweepTheta P.u m j) y.sweep i - sweepIncrement (sweepTheta P.u m j) x.sweep i)

/-- The reach invariant. -/
def ReachInv (x : RunRecord d m) (s : RunRecord d m × TileScratch d m) : Prop :=
  (s.2.halted = false → TrialRun P j T x s) ∧
    (s.2.halted = true → s.1.aborted = true ∨ CommitGood P j T x s.1)

/-- Scalar bound hypothesis (`|ξ| ≤ 2√t` for every possible slot increment; proved from the
scales in `xi_bound`). -/
def XiBound (x : RunRecord d m) : Prop :=
  ∀ i ζ, i ∈ TS P j T → i ∈ x.endpoint.active → ZetaBound P j x i ζ →
    (IsFinalSweep m j → x.prefixLength i = m - P.n₀) →
    |ζ / Real.sqrt (sweepW P.u m j)| ≤ 2 * Real.sqrt (sweepScale P.u m j)

theorem localBudget_zero {t b C' : ℝ} {dist : Port d m → Port d m → ℝ}
    (cov : S45.TileCover (P := Port d m) (I := Torus d m) d t b C' dist) (S : Fin cov.count)
    (ht : 0 ≤ t) : S45.localBudget cov S 0 0 0 0 0 := by
  have hp : ∀ e, 0 ≤ S45.power t e := fun e => Real.rpow_nonneg ht e
  refine ⟨fun i _ => by simpa using hp _, fun i _ => ⟨by simpa using hp _, by simpa using hp _⟩,
    ?_, ?_⟩
  · have : S45.mask (cov.inner S) (0 : S45.CMat (Port d m)) = 0 := by
      funext a b; simp [S45.mask, S45.pad, S45.restrict]
    rw [this, norm_zero]; exact hp _
  · have : S45.pullback (cov.coords S).B (0 : S45.RMat (Port d m)) = 0 := by
      simp [S45.pullback]
    rw [this, norm_zero]; exact hp _

theorem stageD0_congr {x y : RunRecord d m} (h0 : y.sweep.state 0 = x.sweep.state 0)
    (hr : y.r = x.r) : stageD0 P j y = stageD0 P j x := by
  unfold stageD0; rw [h0, hr]

theorem newSteps_refl (x : RunRecord d m)
    (hwf : x.sweep.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r))
    (ht : 0 ≤ sweepScale P.u m j) : NewSteps P j T x x.sweep where
  ext := SeqExtends.refl _
  wf := hwf
  steps := fun k h1 h2 => absurd h2 (not_lt.mpr h1)
  valid := fun k h1 h2 => absurd h2 (not_le.mpr h1)
  budget := by
    simp only [Finset.Ico_self, S45.Sequence.Jrecord, S45.Sequence.Lrecord,
      S45.Sequence.lagRecord, S45.Sequence.rowRecord, Finset.sum_empty]
    exact localBudget_zero _ T ht

end Reach

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query Answer)

variable {d m : ℕ}

open Classical in
theorem sweepIncrement_extend_aux {d m : ℕ} (θ : ℝ) (q : S45.Sequence (Port d m))
    (b : S45.LiveState (Port d m)) (y : Port d m) (ξ : ℝ) (i : Torus d m) :
    sweepIncrement θ (extendSeq q b y ξ) i = sweepIncrement θ q i + Real.sqrt (1 - θ) *
      (if (extendSeq q b y ξ).pivot q.length = some ((i, false) : Port d m) then ξ else 0) := by
  unfold sweepIncrement
  rw [extendSeq_length, Finset.sum_range_succ, mul_add, extendSeq_scalar_last]
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≠ q.length := (Finset.mem_range.mp hk).ne
  have h1 : (extendSeq q b y ξ).pivot k = q.pivot k := by simp [extendSeq, hk']
  have h2 : (extendSeq q b y ξ).scalar k = q.scalar k := by simp [extendSeq, hk']
  rw [h1, h2]

theorem sweepIncrement_extend_self {d m : ℕ} (θ : ℝ) (q : S45.Sequence (Port d m))
    (b : S45.LiveState (Port d m)) (ξ : ℝ) (i : Torus d m) :
    sweepIncrement θ (extendSeq q b ((i, false) : Port d m) ξ) i =
      sweepIncrement θ q i + Real.sqrt (1 - θ) * ξ := by
  have h1 := sweepIncrement_extend_aux θ q b ((i, false) : Port d m) ξ i
  have hp : (extendSeq q b ((i, false) : Port d m) ξ).pivot q.length =
      some ((i, false) : Port d m) := extendSeq_pivot_last _ _ _ _
  rw [if_pos hp] at h1
  exact h1

theorem sweepIncrement_extend_ne {d m : ℕ} (θ : ℝ) (q : S45.Sequence (Port d m))
    (b : S45.LiveState (Port d m)) (ξ : ℝ) {i i' : Torus d m} (hne : i' ≠ i) :
    sweepIncrement θ (extendSeq q b ((i, false) : Port d m) ξ) i' = sweepIncrement θ q i' := by
  have h1 := sweepIncrement_extend_aux θ q b ((i, false) : Port d m) ξ i'
  have hp : ¬ (extendSeq q b ((i, false) : Port d m) ξ).pivot q.length =
      some ((i', false) : Port d m) := by
    have hp0 := extendSeq_pivot_last q b ((i, false) : Port d m) ξ
    intro h
    exact hne (congrArg Prod.fst (Option.some.inj (hp0.symm.trans h))).symm
  rw [if_neg hp, mul_zero, add_zero] at h1
  exact h1

section Preserve
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
  (hwf : x.sweep.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r))
  (ht : 0 ≤ sweepScale P.u m j)
include hwf ht

theorem trialRun_fresh (y : RunRecord d m) (sc : TileScratch d m)
    (hsw : y.sweep = x.sweep) (hen : y.endpoint = x.endpoint) (hr : y.r = x.r)
    (hab : y.aborted = false) (hte : y.terminal = x.terminal)
    (hpl : y.prefixLength = x.prefixLength) (hpf : IsFinalSweep m j → y.pending = x.pending)
    (hseq : sc.seq = x.sweep) (hsite : sc.site = none) (hcons : sc.consumed = fun _ => false)
    (hinst : y.installed = x.installed) (hadd : sc.added = fun _ => 0) :
    TrialRun P j T x (y, sc) where
  sweep := hsw
  endpoint := hen
  r := hr
  aborted := hab
  terminal := hte
  prefixLength := hpl
  pending_final := hpf
  seq := by rw [hseq]; exact newSteps_refl P j T x hwf ht
  site := fun i hi => by simp [hsite] at hi
  consumed := fun i _ => by simp [hcons]
  installed := hinst
  added := fun i => by simp [hadd, hseq]

theorem reachInv_enter (hab : x.aborted = false) :
    ReachInv P j T x ((tileBlock P j T).enter x) := by
  have he : (tileBlock P j T).enter x = (x, initScratch x) := by
    simp [tileBlock, hab]
  rw [he]
  refine ⟨fun _ => trialRun_fresh P j T x hwf ht x _ rfl rfl rfl hab rfl rfl (fun _ => rfl)
    rfl rfl rfl rfl rfl, fun h => by simp [initScratch] at h⟩

variable (hxi : XiBound P j T x)
  (hfp : IsFinalSweep m j → ∀ i ∈ TS P j T, i ∈ x.endpoint.active →
    x.prefixLength i = m - P.n₀) (hw : 0 < sweepW P.u m j)
include hxi hfp hw

theorem reachInv_update (s : RunRecord d m × TileScratch d m) (hrun : s.2.halted = false)
    (h : TrialRun P j T x s) (a : Answer (Torus d m)) :
    ReachInv P j T x ((tileBlock P j T).update s a) := by
  rcases tile_update_cases P j T s hrun a with
    ⟨h1, h2, h3, h4, h4', h5⟩ | ⟨h1, hc1, hc2, hc3, hc4, hc5, hc7, hc6⟩ |
      ⟨i, ζ, hsite, hact, hζ, hok, h1, h2, h3, h4, h4', h5⟩ | ⟨sc, hsc1, hsc2, hsc3, hsc4⟩
  · -- (A)
    refine ⟨fun _ => ?_, fun hh => by rw [h3] at hh; exact absurd hh (by simp)⟩
    refine ⟨by rw [h1]; exact h.sweep, by rw [h1]; exact h.endpoint, by rw [h1]; exact h.r,
      by rw [h1]; exact h.aborted, by rw [h1]; exact h.terminal,
      by rw [h1]; exact h.prefixLength, fun hf => by rw [h1]; exact h.pending_final hf,
      by rw [h2]; exact h.seq, fun i hi => ?_, fun i hi => by rw [h4]; exact h.consumed i hi,
      by rw [h1]; exact h.installed, fun i => by rw [h4', h2]; exact h.added i⟩
    rw [h2]
    rcases h5 i hi with h5 | h5
    · exact h5
    · exact h.site i h5
  · -- (B) acceptance
    refine ⟨fun hh => by rw [h1] at hh; exact absurd hh (by simp), fun _ => Or.inr ?_⟩
    refine ⟨by rw [hc2]; exact h.endpoint, by rw [hc3]; exact h.r, by rw [hc4]; exact h.aborted,
      fun i hi => ?_, fun hf => by rw [hc5]; exact h.pending_final hf, by rw [hc1]; exact h.seq,
      fun i => ?_⟩
    · obtain ⟨ht, hp⟩ := hc6 i (h.consumed i hi)
      exact ⟨by rw [ht, h.terminal], by rw [hp, h.prefixLength]⟩
    · simp only [hc7, hc1, h.installed]; rw [h.added i]
  · -- (C) a tested deletion
    refine ⟨fun _ => ?_, fun hh => by rw [h4] at hh; exact absurd hh (by simp)⟩
    have hi : i ∈ TS P j T := (activeIn_mem P j T hact).1
    have hia : i ∈ x.endpoint.active := h.endpoint ▸ (activeIn_mem P j T hact).2
    have hlive := h.site i hsite
    have hrr : portR (sweepTheta P.u m j) s.1.r = portR (sweepTheta P.u m j) x.r := by
      rw [h.r]
    have hD : stageD0 P j s.1 = stageD0 P j x :=
      stageD0_congr P j (by rw [h.sweep]) h.r
    have hlen : s.1.sweep.length = x.sweep.length := by rw [h.sweep]
    unfold trialOk at hok
    dsimp only at hok
    rw [hrr, hD, hlen] at hok
    rw [hrr] at h2
    set ξ := ζ / Real.sqrt (sweepW P.u m j) with hξ
    set q := s.2.seq with hq
    have hext := extendSeq_extends q
      (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (q.state q.length)
        ((i, false) : Port d m) ξ) ((i, false) : Port d m) ξ
    have hwf' := extendSeq_wellFormed _ _ q h.seq.wf ((i, false) : Port d m) ξ hlive hok.1
    have hζx : ZetaBound P j x i ζ := by
      unfold ZetaBound at hζ ⊢; rw [← h.prefixLength]; exact hζ
    have hxib := hxi i ζ hi hia hζx (fun hf => hfp hf i hi hia)
    refine ⟨by rw [h1]; exact h.sweep, by rw [h1]; exact h.endpoint, by rw [h1]; exact h.r,
      by rw [h1]; exact h.aborted, by rw [h1]; exact h.terminal,
      by rw [h1]; exact h.prefixLength, fun hf => by rw [h1]; exact h.pending_final hf,
      ?_, fun i' hi' => by rw [h3] at hi'; simp at hi', fun i' hi' => ?_,
      by rw [h1]; exact h.installed, fun i' => ?_⟩
    · rw [h2]
      refine ⟨h.seq.ext.trans hext, hwf', fun k hk1 hk2 => ?_, fun k hk1 hk2 => ?_, hok.2.2⟩
      · change k < q.length + 1 at hk2
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk2 with hk2 | rfl
        · obtain ⟨i', hi', ha', hp', hs'⟩ := h.seq.steps k hk1 hk2
          exact ⟨i', hi', ha', by rw [hext.pivot k hk2]; exact hp',
            by rw [hext.scalar k hk2]; exact hs'⟩
        · exact ⟨i, hi, hia, extendSeq_pivot_last _ _ _ _, by simpa [extendSeq] using hxib⟩
      · change k ≤ q.length + 1 at hk2
        rcases Nat.lt_or_eq_of_le hk2 with hk2 | rfl
        · have hk2' : k ≤ q.length := Nat.lt_succ_iff.mp hk2
          rw [hext.valid _ _ _ hk2']; exact h.seq.valid k hk1 hk2'
        · exact hok.2.1
    · have hne : i' ≠ i := fun he => hi' (he ▸ hi)
      rw [h5 i' hne]; exact h.consumed i' hi'
    · rw [h4']
      by_cases hii : i' = i
      · subst hii
        have e2 : sweepIncrement (sweepTheta P.u m j) ((tileBlock P j T).update s a).2.seq i' =
            sweepIncrement (sweepTheta P.u m j) q i' + Real.sqrt (1 - sweepTheta P.u m j) * ξ := by
          rw [h2]; exact sweepIncrement_extend_self _ _ _ _ _
        rw [e2, Function.update_self, h.added i']
        have hsw : Real.sqrt (1 - sweepTheta P.u m j) * ξ = ζ := by
          have hne : Real.sqrt (1 - sweepTheta P.u m j) ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
          rw [hξ]; unfold sweepW
          field_simp
        rw [hsw]; ring
      · have e2 : sweepIncrement (sweepTheta P.u m j) ((tileBlock P j T).update s a).2.seq i' =
            sweepIncrement (sweepTheta P.u m j) q i' := by
          rw [h2]; exact sweepIncrement_extend_ne _ _ _ _ hii
        rw [e2, Function.update_of_ne hii, h.added i']
  · -- (D) a failed test
    rw [hsc4]
    by_cases hlate : m / 2 < j
    · refine ⟨fun hh => ?_, fun _ => Or.inl ?_⟩
      · simp [failTrial, hlate] at hh
      · simp [failTrial, hlate]
    · have hhalt : sc.halted = false := by rw [hsc3]; exact hrun
      have hnf : ¬ IsFinalSweep m j := by unfold IsFinalSweep; omega
      refine ⟨fun _ => ?_, fun hh => by simp [failTrial, hlate, trialScratch, hhalt] at hh⟩
      by_cases h0 : sc.attempt = 0
      · have hf : failTrial P j T (s.1, sc) =
            (markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1,
              { trialScratch (markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩
                  s.1) sc (sc.attempt + 1) with firstFail := true }) := by
          simp [failTrial, hlate, h0]
        rw [hf]
        exact trialRun_fresh P j T x hwf ht _ _ (by simp [markTile, h.sweep])
          (by simp [markTile, h.endpoint]) (by simp [markTile, h.r])
          (by simp [markTile, h.aborted]) (by simp [markTile, h.terminal])
          (by simp [markTile, h.prefixLength]) (fun hf' => absurd hf' hnf)
          (by simp [trialScratch, markTile, h.sweep]) (by simp [trialScratch])
          (by simp [trialScratch]) (by simp [markTile, h.installed]) (by simp [trialScratch])
      · have hf : failTrial P j T (s.1, sc) =
            (s.1, { trialScratch s.1 sc (sc.attempt + 1) with firstFail := true }) := by
          simp [failTrial, hlate, h0]
        rw [hf]
        exact trialRun_fresh P j T x hwf ht _ _ h.sweep h.endpoint h.r h.aborted h.terminal
          h.prefixLength (fun hf' => absurd hf' hnf) (by simp [trialScratch, h.sweep])
          (by simp [trialScratch]) (by simp [trialScratch]) h.installed (by simp [trialScratch])

end Preserve

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query Answer)

variable {d m : ℕ}

section Keeps
variable {C : ℝ} {P : TilePlan d m} {j : ℕ} {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}
  {done : Finset (Fin (P.cover j).cover.count)} {T : Fin (P.cover j).cover.count}
  {x : RunRecord d m}

theorem TileSweepCore.scale_nonneg (h : TileSweepCore C P j n₀ u E ρ Cb done x) :
    0 ≤ sweepScale P.u m j := h.plan.cover_b.1.le.trans h.plan.cover_b.2

/-- Every reachable state of the block satisfies the reach invariant. -/
theorem reachInv_of_reach (h : TileSweepCore C P j n₀ u E ρ Cb done x) (hT : T ∉ done)
    (hab : x.aborted = false) (hxi : XiBound P j T x) (hw : 0 < sweepW P.u m j)
    (s : RunRecord d m × TileScratch d m)
    (hs : BlockReach (tileBlock P j T) x s) : ReachInv P j T x s := by
  induction hs with
  | enter => exact reachInv_enter P j T x h.wellFormed h.scale_nonneg hab
  | step s a _ hh ih =>
    exact reachInv_update P j T x h.wellFormed h.scale_nonneg hxi
      (fun hf i hi ha => h.final_prefix hf T hT i hi ha) hw s hh (ih.1 hh) a

/-- An aborted record enters a halted block: its only reachable state is the entry. -/
theorem reach_of_aborted (hab : x.aborted = true) (s : RunRecord d m × TileScratch d m)
    (hs : BlockReach (tileBlock P j T) x s) : s = (tileBlock P j T).enter x := by
  induction hs with
  | enter => rfl
  | step s a _ hh ih =>
    rw [ih] at hh
    simp [tileBlock, hab] at hh

/-- **Completeness of an accepted trial** (the isolated hypothesis; INTERFACE-ISSUES 01:05):
an accepted exit has deleted the bit port of every active site of `T`. -/
def TileAcceptComplete (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x y : RunRecord d m) : Prop :=
  y.aborted = false → ∀ i ∈ TS P j T, i ∈ x.endpoint.active →
    ((i, false) : Port d m) ∉ (y.sweep.state y.sweep.length).live

/-- **The exit of an accepted trial keeps the tile-phase invariant, with `T` processed.** -/
theorem sweepCore_commit (h : TileSweepCore C P j n₀ u E ρ Cb done x) (hT : T ∉ done)
    (y : RunRecord d m) (hy : CommitGood P j T x y) (hc : TileAcceptComplete P j T x y) :
    TileSweepCore C P j n₀ u E ρ Cb (insert T done) y := by
  classical
  have hext := hy.seq.ext
  have h0 : y.sweep.state 0 = x.sweep.state 0 := hext.state 0 (Nat.zero_le _)
  have hrr : portR (sweepTheta P.u m j) y.r = portR (sweepTheta P.u m j) x.r := by rw [hy.r]
  have hD : stageD0 P j y = stageD0 P j x := stageD0_congr P j h0 hy.r
  have hwf : y.sweep.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) y.r) := by
    rw [hrr]; exact hy.seq.wf
  -- sites of other tiles are not in `T`
  have hother : ∀ S, S ≠ T → ∀ i ∈ tileSites (P.cover j) S, i ∉ TS P j T := by
    intro S hS i hi hiT
    exact hS (tile_unique (mem_tileSites.mp hi) (mem_tileSites.mp hiT))
  obtain ⟨blocks, hb1, hb2, hb3, hb4, hb5⟩ := h.blocks
  have hbT : blocks T = ∅ := hb4 T hT
  refine
    { hist := by rw [hy.endpoint, hy.r]; exact h.hist
      plan := h.plan
      start := by rw [h0, hy.r, hy.endpoint]; exact h.start
      start_live := by
        rw [h0, h.start_live]; unfold liveStart; rw [hy.endpoint]
      start_lift := by
        rw [h0, h.start_lift]; unfold sweepStartLiveState; rw [hy.endpoint, hy.r]
      physical := physicalIdentity_congr (by simp [hy.endpoint])
        (by funext i; simp only; rw [hy.installed i]; ring) h.physical
      wellFormed := hwf
      valid := ?_
      bit_pivots := ?_
      scalar_bound := ?_
      pivots_some := ?_
      blocks := ?_
      done_deleted := ?_
      undone_nonterminal := ?_
      final_no_pending := ?_
      final_prefix := ?_ }
  · intro k hk
    rcases le_or_gt k x.sweep.length with hkx | hkx
    · rw [hD, hrr, hext.valid _ _ _ hkx]; exact h.valid k hkx
    · rw [hD, hrr]; exact hy.seq.valid k hkx hk
  · intro k hk z hz
    rcases lt_or_ge k x.sweep.length with hkx | hkx
    · rw [hext.pivot k hkx] at hz; exact h.bit_pivots k hkx z hz
    · obtain ⟨i, _, _, hp, _⟩ := hy.seq.steps k hkx hk
      have he := Option.some.inj (hp.symm.trans hz)
      rw [← he]
  · intro k hk
    rcases lt_or_ge k x.sweep.length with hkx | hkx
    · rw [hext.scalar k hkx]; exact h.scalar_bound k hkx
    · obtain ⟨_, _, _, _, hb⟩ := hy.seq.steps k hkx hk
      exact hb
  · intro k hk
    rcases lt_or_ge k x.sweep.length with hkx | hkx
    · rw [hext.pivot k hkx]; exact h.pivots_some k hkx
    · obtain ⟨_, _, _, hp, _⟩ := hy.seq.steps k hkx hk
      rw [hp]; exact Option.some_ne_none _
  · refine ⟨fun S => if S = T then Finset.Ico x.sweep.length y.sweep.length else blocks S,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rcases lt_or_ge k x.sweep.length with hkx | hkx
      · obtain ⟨S, hS, hSu⟩ := hb1 k hkx
        have hST : S ≠ T := by rintro rfl; rw [hbT] at hS; simp at hS
        refine ⟨S, by simp [hST, hS], fun S' hS' => ?_⟩
        by_cases hS'T : S' = T
        · subst hS'T; simp at hS'; omega
        · simp only [hS'T, if_false] at hS'; exact hSu S' hS'
      · refine ⟨T, by simp [hkx, hk], fun S' hS' => ?_⟩
        by_contra hS'T
        simp only [hS'T, if_false] at hS'
        have := Finset.mem_range.mp (hb2 S' hS')
        omega
    · intro S
      by_cases hST : S = T
      · simp only [hST, if_true]
        intro k hk; simp at hk; exact Finset.mem_range.mpr hk.2
      · simp only [hST, if_false]
        exact (hb2 S).trans (Finset.range_subset_range.mpr hext.le)
    · intro k hk z hz S hS
      by_cases hST : S = T
      · subst hST
        simp only [if_true, Finset.mem_Ico] at hS
        obtain ⟨i, hi, -, hp, -⟩ := hy.seq.steps k hS.1 hk
        rw [hp] at hz; cases hz
        exact mem_tileSites.mp hi
      · simp only [hST, if_false] at hS
        have hkx := Finset.mem_range.mp (hb2 S hS)
        rw [hext.pivot k hkx] at hz
        exact hb3 k hkx z hz S hS
    · intro S hS
      have hST : S ≠ T := fun he => hS (he ▸ Finset.mem_insert_self _ _)
      simp only [hST, if_false]
      exact hb4 S (fun h' => hS (Finset.mem_insert_of_mem h'))
    · intro S
      by_cases hST : S = T
      · subst hST; simp only [if_true]; rw [hrr]; exact hy.seq.budget
      · simp only [hST, if_false]
        rw [hrr, hext.Jrecord _ _ (hb2 S), hext.Lrecord _ _ (hb2 S),
          hext.lagRecord _ _ (hb2 S), hext.rowRecord _ _ _ (hb2 S),
          hext.rowRecord _ _ _ (hb2 S)]
        exact hb5 S
  · intro S hS i hi hia
    rw [hy.endpoint] at hia
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact hc hy.aborted i hi hia
    · intro hlive
      have hx := h.done_deleted S hS i hi hia
      apply hx
      have hlive' := (mem_live_iff hwf le_rfl ((i, false) : Port d m)).mp hlive
      rw [← hext.state x.sweep.length le_rfl]
      exact (mem_live_iff hwf hext.le ((i, false) : Port d m)).mpr
        ⟨hlive'.1, fun l hl => hlive'.2 l (lt_of_lt_of_le hl hext.le)⟩
  · intro S hS i hi hia
    rw [hy.endpoint] at hia
    have hST : S ≠ T := fun he => hS (he ▸ Finset.mem_insert_self _ _)
    rw [(hy.outside i (hother S hST i hi)).1]
    exact h.undone_nonterminal S (fun h' => hS (Finset.mem_insert_of_mem h')) i hi hia
  · intro hf S hS i hi hia
    rw [hy.endpoint] at hia
    rw [hy.pending_final hf]
    exact h.final_no_pending hf S (fun h' => hS (Finset.mem_insert_of_mem h')) i hi hia
  · intro hf S hS i hi hia
    rw [hy.endpoint] at hia
    have hST : S ≠ T := fun he => hS (he ▸ Finset.mem_insert_self _ _)
    rw [(hy.outside i (hother S hST i hi)).2]
    exact h.final_prefix hf S (fun h' => hS (Finset.mem_insert_of_mem h')) i hi hia

/-- **(b) Tile blocks keep the tile-phase invariant.** For a record in the invariant with `T`
unprocessed, every halted state reachable by the block of `T` exits into the invariant with
`T` processed, provided the scalar bound `XiBound` (scales) and the completeness of an
accepted trial (`TileAcceptComplete`, the isolated hypothesis). -/
theorem tileBlock_keeps (hx : x ∈ TileSweepInv C P j n₀ u E ρ Cb done) (hT : T ∉ done)
    (hxi : x.aborted = false → XiBound P j T x) (hw : 0 < sweepW P.u m j)
    (s : RunRecord d m × TileScratch d m)
    (hs : BlockReach (tileBlock P j T) x s) (hh : (tileBlock P j T).halted s = true)
    (hc : TileAcceptComplete P j T x s.1) :
    (tileBlock P j T).exit s ∈ TileSweepInv C P j n₀ u E ρ Cb (insert T done) := by
  cases hab : x.aborted
  · have h := hx hab
    have hr := (reachInv_of_reach h hT hab (hxi hab) hw s hs).2 hh
    intro hab'
    rcases hr with hr | hr
    · change s.1.aborted = false at hab'
      rw [hr] at hab'; exact absurd hab' (by simp)
    · exact sweepCore_commit h hT s.1 hr hc
  · rw [reach_of_aborted hab s hs]
    intro hab'
    simp [tileBlock, hab] at hab'

end Keeps

end AndersonAC.AgentS78

/-! ## The scalar bound `|ξ| ≤ 2√t` from the scales (04:36–41, 05:349–359) -/

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem abs_div_sqrt_le {ζ a w t : ℝ} (hw : 0 < w) (ht : 0 ≤ t) (hζ : |ζ| ≤ Real.sqrt a)
    (ha : a ≤ 4 * t * w) : |ζ / Real.sqrt w| ≤ 2 * Real.sqrt t := by
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  rw [abs_div, abs_of_pos hsw, div_le_iff₀ hsw]
  calc |ζ| ≤ Real.sqrt a := hζ
    _ ≤ Real.sqrt (4 * t * w) := Real.sqrt_le_sqrt ha
    _ = 2 * Real.sqrt t * Real.sqrt w := by
      rw [Real.sqrt_mul (by positivity) w, Real.sqrt_mul (by norm_num) t,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The bit-port weight is positive at every sweep. -/
theorem sweepW_pos (u : ℝ) (hu : 0 < u) (m j : ℕ) (hj : 0 < j) (hjm : j ≤ m + 1) :
    0 < sweepW u m j := by
  by_cases hf : IsFinalSweep m j
  · unfold sweepW sweepTheta; rw [if_pos hf]; norm_num
  · have hjm' : j ≤ m := by unfold IsFinalSweep at hf; omega
    have hj1 : j - 1 + 1 = j := by omega
    unfold sweepW sweepTheta stageScale
    rw [if_neg hf]
    have h4 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by rw [← pow_succ', hj1]
    rw [h4]
    have ha : 0 < u / 4 ^ (j - 1) := by positivity
    have hb : 0 < u / 4 ^ m := by positivity
    rw [sub_pos, div_lt_one (by positivity)]
    have : u / (4 * 4 ^ (j - 1)) = u / 4 ^ (j - 1) / 4 := by rw [div_div, mul_comm]
    rw [this]; linarith

/-- **The scalar bound.** -/
theorem xiBound_of_scales (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x : RunRecord d m) (hu : 0 < P.u) (hj : P.n₀ < j) (hjm : j ≤ m + 1) : XiBound P j T x := by
  intro i ζ _ _ hζ hfp
  by_cases hf : IsFinalSweep m j
  · have hjm' : j = m + 1 := by unfold IsFinalSweep at hf; omega
    have hw : sweepW P.u m j = 1 / 2 := by
      unfold sweepW sweepTheta; rw [if_pos hf]; norm_num
    have ht : sweepScale P.u m j = 2 * (P.u / 4 ^ m) := by
      unfold sweepScale stageScale; rw [if_pos hf]; ring
    have hum : 0 < P.u / 4 ^ m := by positivity
    rw [hw, ht]
    rcases hζ with hζ | ⟨-, hζ⟩
    · refine abs_div_sqrt_le (by norm_num) (by positivity) hζ ?_
      rw [show j - 1 = m by omega]
      nlinarith
    · rw [hfp hf] at hζ
      have hc : 0 ≤ couplingOf P.u P.n₀ := Real.sqrt_nonneg _
      rw [abs_of_nonneg hc] at hζ
      have hpos : 0 ≤ couplingOf P.u P.n₀ / 2 ^ (m - P.n₀) := by positivity
      have hζ' : |ζ| ≤ Real.sqrt ((couplingOf P.u P.n₀ / 2 ^ (m - P.n₀)) ^ 2) := by
        rw [Real.sqrt_sq hpos]; exact hζ
      refine abs_div_sqrt_le (by norm_num) (by positivity) hζ' ?_
      · have hn : P.n₀ ≤ m := by omega
        have h4 : (4 : ℝ) ^ m = 4 ^ P.n₀ * (2 ^ (m - P.n₀)) ^ 2 := by
          rw [← pow_mul, show (2 : ℝ) ^ ((m - P.n₀) * 2) = 4 ^ (m - P.n₀) by
            rw [pow_mul']; norm_num, ← pow_add, Nat.add_sub_cancel' hn]
        rw [div_pow, couplingOf, Real.sq_sqrt (by positivity)]
        have h2 : (0 : ℝ) < (2 ^ (m - P.n₀)) ^ 2 := by positivity
        have h4n : (0 : ℝ) < 4 ^ P.n₀ := by positivity
        rw [show P.u / 4 ^ m = P.u / (4 ^ P.n₀ * (2 ^ (m - P.n₀)) ^ 2) by rw [h4]]
        rw [div_div, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
  · have hjm' : j ≤ m := by unfold IsFinalSweep at hf; omega
    rcases hζ with hζ | ⟨hf', -⟩
    swap; · exact absurd hf' hf
    have hj1 : j - 1 + 1 = j := by omega
    have htj : sweepScale P.u m j = P.u / 4 ^ (j - 1) + P.u / 4 ^ m := by
      unfold sweepScale stageScale; rw [if_neg hf]
    have h4 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by rw [← pow_succ', hj1]
    have htpos : 0 < sweepScale P.u m j := by rw [htj]; positivity
    have htw : sweepScale P.u m j * sweepW P.u m j = 3 / 4 * (P.u / 4 ^ (j - 1)) := by
      unfold sweepW sweepTheta
      rw [if_neg hf]
      unfold stageScale
      rw [htj, h4]
      field_simp
      ring
    have hw : 0 < sweepW P.u m j := by
      have : 0 < sweepScale P.u m j * sweepW P.u m j := by rw [htw]; positivity
      exact pos_of_mul_pos_right this htpos.le
    refine abs_div_sqrt_le hw htpos.le hζ ?_
    rw [mul_assoc, htw]
    have : 0 < P.u / 4 ^ (j - 1) := by positivity
    linarith

end AndersonAC.AgentS78
