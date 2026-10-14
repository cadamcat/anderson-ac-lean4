import AndersonAC.AgentS78.Construction.TileBlockFacts
import AndersonAC.AgentS78.Construction.Reached
import AndersonAC.AgentS78.Construction.ResetBlock

/-!
# WP10 construction, C4a: the trial hypotheses `TileGood` and the frozen trial contracts

agent-s78trial (2026-10-14), request of agent-s78con (DISPATCH-REQUESTS 22:42 UTC).
Paper (authoritative): refs/tex/05-local-sweeps.tex, cited as `05:<lines>`.

* `TileGood C P j T` — the deterministic hypotheses on the record entering the tile block of
  tile `T` in the sweep with post-sweep index `j`, under which 05:766–870 (Lemma
  `local-trial`) and 05:872–905 (retries) prove the trial bounds. Every clause is documented
  with its TeX lines. There is no probabilistic content: each clause is a property of the
  committed record, the tile plan and the constant `C`.
* `TileTrialBoundStatement` (frozen analytic core, the one-trial lemma on the frozen tile
  trial) and `TileRetryStatement` (frozen analytic core, the retry estimate on the frozen
  tile block). The block-level bounds `tile_first_trial_bound` and `tile_halting_bound`
  (TileTrialFirst.lean, TileTrialHalt.lean) are proved from them.
* `TileCrossingStatement`, the S45 route to `TileTrialBoundStatement`: a `TrialInputs` on
  `(RandomSources, sourcesLaw)` whose crossing event contains the first-trial failure;
  `tileTrialBound_of_crossing` (TileTrialFirst.lean) applies `S45.one_trial` (Lemma 5.6 with
  Golden–Thompson, both proved).

Scales: `t = sweepScale P.u m j`, `θ = sweepTheta P.u m j` (TileBlock.lean: the digit sweep
into stage `j ≤ m` is the paper's sweep at scale `n = j − 1`; `j = m + 1` is the final
residual sweep, 04:36–41).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw)

section Good
variable {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

/-- The duplicated stage-start state of the sweep on the ports, `s₀` of 05:322–333. -/
def stageStart (x : RunRecord d m) : S45.State (Port d m) :=
  (x.sweep.state 0).ambient (portR (sweepTheta P.u m j) x.r)

/-- **v3 (frozen 2026-10-14, agent-s78con3).** The duplicated stage start on the ports of the
**active** sites, `initialPorts {i // i ∈ x.endpoint.active}` (05:320–333, 04:67–80): the S45
lift `(splitPorts θ).liftState` of the committed endpoint inverse and damping restricted to
the active sites. This is the object of `S45.ordinary_sweep_endpoint` / `prestate_of_prefix`
(after `Fintype.equivFin`), and it does not depend on the sweep record. -/
def stageStartV3 (x : RunRecord d m) :
    S45.State (S45.initialPorts {i // i ∈ x.endpoint.active}) :=
  (S45.splitPorts {i // i ∈ x.endpoint.active} (sweepTheta P.u m j)).liftState
    ⟨fun i k => x.endpoint.g i.1 k.1, fun i => x.r i.1⟩

/-- The torus port of an active-site port. -/
def activePort (x : RunRecord d m) (p : S45.initialPorts {i // i ∈ x.endpoint.active}) :
    Port d m := (p.1.1, p.2)

/-- The included (accepted) sweep prefix is a union of accepted tile records
(05:399–419, 05:538–548): a partition of its steps into tile blocks, each pivot in the tile
of its block, the tile `T` itself not yet used, and the local budgets (05:452–462) of every
accepted endpoint record. -/
def AcceptedTiles (x : RunRecord d m) : Prop :=
  ∃ blocks : Fin (P.cover j).cover.count → Finset ℕ,
    (∀ k < x.sweep.length, ∃! S, k ∈ blocks S) ∧
    (∀ S, blocks S ⊆ Finset.range x.sweep.length) ∧
    (∀ k < x.sweep.length, ∀ y, x.sweep.pivot k = some y → ∀ S, k ∈ blocks S →
      y ∈ (P.cover j).cover.tile S) ∧
    blocks T = ∅ ∧
    (∀ S, S45.localBudget (P.cover j).cover S
      (x.sweep.Jrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (blocks S))
      (x.sweep.Lrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (blocks S))
      (x.sweep.lagRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (blocks S))
      (x.sweep.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        Finset.univ (blocks S))
      (x.sweep.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        S45.reserves (blocks S)))

/-- **The trial hypotheses on a non-aborted entering record** (05:320–337, 338–359,
399–475, 466–475, 538–548, 766–772). With `t = sweepScale P.u m j`,
`θ = sweepTheta P.u m j`, `r = portR θ x.r` (the frozen port damping, 04:73–80),
`s₀ = stageStart P j x`, `D₀ = stageD0 P j x`. -/
structure TileGoodCore (x : RunRecord d m) : Prop where
  /-- Constants: `1 ≤ C`. -/
  one_le : 1 ≤ C
  /-- Local metric input (05:240–256 `eq:local-metric-input`, standing by 05:333–335): the
  tile cover's scale `0 < b ≤ t` and its constant at most `C`. -/
  cover_b : 0 < (P.cover j).b ∧ (P.cover j).b ≤ sweepScale P.u m j
  cover_C : (P.cover j).C ≤ C
  /-- The shell bounds of the cover distance (05:92–100, Lemma `inverse-row`; 05:600–612). -/
  shell : S45.ShellBounds d C (P.cover j).dist
  /-- `M = L_tile^d ≍ t^{-6d}` slots (05:342–343, 05:778–779). -/
  tile_card : ((tileSites (P.cover j) T).card : ℝ) ≤
    C * S45.power (sweepScale P.u m j) (-6 * (d : ℝ))
  /-- The local port space of the tile has at most `C t^{-6d}` ports, `|P₀ ∩ Q_T| ≤ C t^{-6d}`
  (05:860–864, dimension count of the monitored tests). -/
  inner_card : (((P.cover j).cover.inner T).card : ℝ) ≤
    C * S45.power (sweepScale P.u m j) (-6 * (d : ℝ))
  /-- The included prefix is a well-formed sequence of `S45.StepRel` updates with the frozen
  port damping (05:385–398, 04:190–228). -/
  wellFormed : x.sweep.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
  /-- **v3.** The sweep's state 0 is the stage-start lift installed by `sweepStartMap`
  (05:385–392): live ports = both ports of every active site, `g` = the split-port lift of
  `x.endpoint.g` (ResetBlock.sweepStartLiveState). -/
  start_live : x.sweep.state 0 = sweepStartLiveState (sweepTheta P.u m j) x
  /-- **v3.** Duplicated stage start (05:320–333) on the active-site ports `stageStartV3`: the
  complete stage-boundary bounds as the S45 prestate (broad frozen `r, p`, symmetry, Ward, `K`
  cap, invertibility, constant kernel, fourth-power row cap, transformed-lag cap, the
  comparator `X₀ ≤ (1+t^κ) diag(p^{-2}) + C t Λ⁺`, Fourier/dual bounds, volume). -/
  start_prestate : ∃ Λplus Wstar : S45.Form (S45.initialPorts {i // i ∈ x.endpoint.active}),
    S45.Prestate (sweepScale P.u m j) C Λplus Wstar (stageStartV3 P j x) ∧
    (open scoped Matrix.Norms.L2Operator in
      ‖(stageStartV3 P j x).K (sweepScale P.u m j)‖ ≤ 1 / 3) ∧
    (∀ y, S45.neutral y → 0 ≤ Λplus y) ∧
    (∀ y, S45.neutral y → (stageStartV3 P j x).X (sweepScale P.u m j) y ≤
      (1 + S45.power (sweepScale P.u m j) S45.kappa) *
        (∑ i, y i ^ 2 / (stageStartV3 P j x).p i ^ 2) +
        C * sweepScale P.u m j * Λplus y)
  /-- **v3.** `Ũ₀ = 0` (05:327), on the active-site ports. -/
  start_lag : ∀ i, (stageStartV3 P j x).lag (sweepScale P.u m j) i = 0
  /-- **v3.** `D₀ ≍ W` with the cover's local metric (05:328), on the active-site ports. -/
  start_comparison : S45.formComparable (S45.qform ((stageStartV3 P j x).D (sweepScale P.u m j)))
    (S45.spatialEnergy (fun p => (P.cover j).cover.site (activePort x p)) (P.cover j).b
      (P.cover j).cover.energy) C
  /-- **v3.** Full duplicated fourth-power rows at most `.75 H_*` (05:330–331). -/
  start_rows : ∀ i, (stageStartV3 P j x).fourthRow (sweepScale P.u m j) Finset.univ i ≤
    3 / 4 * S45.rowCap (sweepScale P.u m j)
  /-- **v3.** Reserve rows at most `θ² H_*` (Lemma `duplication`, 04; 05:560–564). -/
  start_reserve_rows : ∀ i ∈ (S45.reserves : Finset (S45.initialPorts {i // i ∈ x.endpoint.active})),
    (stageStartV3 P j x).fourthRow (sweepScale P.u m j) S45.reserves i ≤
      sweepTheta P.u m j ^ 2 * S45.rowCap (sweepScale P.u m j)
  /-- **v3.** Stage-boundary decay of the normalized inverse at the duplicated start, in the
  cover distance (05:320; hypotheses of Lemma `local-prospective`, 05:155–170, and Lemma
  `inverse-row`, 05:92–100). -/
  start_decay : ∀ a b, ‖(stageStartV3 P j x).h (sweepScale P.u m j) a b‖ ≤
    C / Real.sqrt (sweepScale P.u m j) *
      Real.exp (-(sweepScale P.u m j) ^ 3 * (P.cover j).dist (activePort x a) (activePort x b) / C)
  start_far_decay : ∀ a b,
    C * S45.power (sweepScale P.u m j) (-2) < (P.cover j).dist (activePort x a) (activePort x b) →
    ‖(stageStartV3 P j x).h (sweepScale P.u m j) a b‖ ≤
      C / Real.sqrt (sweepScale P.u m j) *
        Real.exp (-(sweepScale P.u m j) * (P.cover j).dist (activePort x a) (activePort x b) / C)
  /-- **Prefix-state decay** (amendment 2026-10-14, argon-s78transfer audit (1); Lemma
  `locality` 05:51–90 at every prefix state, Lemma `local-prospective` 05:155–220,
  05:458–466): the `t³` and far `t` decay of the normalized inverse at every valid prefix of
  every well-formed bit-pivot sequence from the stage start. Depends only on the stage start
  and `r`, so tile blocks keep it; the stage-boundary invariant must provide it. -/
  prefix_decay : ∀ (q : S45.Sequence (Port d m)),
    q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) →
    q.state 0 = x.sweep.state 0 →
    (∀ k < q.length, ∀ y, q.pivot k = some y → y.2 = false) →
    ∀ k ≤ q.length,
      q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (stageD0 P j x) k →
      (∀ a b : (q.state k).live,
        ‖((q.state k).state (portR (sweepTheta P.u m j) x.r)).h (sweepScale P.u m j) a b‖ ≤
          C / Real.sqrt (sweepScale P.u m j) *
            Real.exp (-(sweepScale P.u m j) ^ 3 * (P.cover j).dist a.1 b.1 / C)) ∧
      (∀ a b : (q.state k).live,
        C * S45.power (sweepScale P.u m j) (-2) < (P.cover j).dist a.1 b.1 →
        ‖((q.state k).state (portR (sweepTheta P.u m j) x.r)).h (sweepScale P.u m j) a b‖ ≤
          C / Real.sqrt (sweepScale P.u m j) *
            Real.exp (-(sweepScale P.u m j) * (P.cover j).dist a.1 b.1 / C))
  /-- Committed scalars are bounded (amendment 2026-10-14, argon-s78transfer audit (2);
  05:25–36, 05:349–359): `|ξ| ≤ 2√t` for the included steps. -/
  scalar_bound : ∀ k < x.sweep.length, |x.sweep.scalar k| ≤ 2 * Real.sqrt (sweepScale P.u m j)
  /-- Every included update has a valid prestate, and the included prefix is valid
  (05:443–462 `eq:local-validity`, 05:538–548). -/
  valid : ∀ k ≤ x.sweep.length, x.sweep.valid (sweepScale P.u m j)
    (portR (sweepTheta P.u m j) x.r) (stageD0 P j x) k
  /-- Pivots are bit ports (05:340–344: a trial deletes the bit port of a site). -/
  bit_pivots : ∀ k < x.sweep.length, ∀ y, x.sweep.pivot k = some y → y.2 = false
  /-- A physical site is a pivot at most once in the included record (05:415–418). -/
  distinct : ∀ k l, k < x.sweep.length → l < x.sweep.length → ∀ y y',
    x.sweep.pivot k = some y → x.sweep.pivot l = some y' → y.1 = y'.1 → k = l
  /-- The accepted earlier tiles and their local budgets (05:399–419, 05:452–462). -/
  accepted : AcceptedTiles P j T x
  /-- The bit ports of `T` are still live: `T` has not been processed in this sweep
  (05:338–341, tiles processed in a fixed order). **v3.1** (agent-s78tphase 02:19): only for
  the active sites of `T` (inactive sites have no port at the stage start). -/
  tile_live : ∀ i ∈ tileSites (P.cover j) T, i ∈ x.endpoint.active →
    ((i, false) : Port d m) ∈ (x.sweep.state x.sweep.length).live
  /-- The final sweep is entered with no pending site (05:353–355). -/
  final_no_pending : IsFinalSweep m j → ∀ i ∈ tileSites (P.cover j) T,
    i ∈ x.endpoint.active → i ∉ x.pending
  /-- Retained-history invariant at the final sweep: each coupled active site has consumed
  the first `m − n₀` digits, so its remaining suffix has variance `s_m` (05:451–456,
  08:340–353). -/
  final_prefix : IsFinalSweep m j → ∀ i ∈ tileSites (P.cover j) T,
    i ∈ x.endpoint.active → x.prefixLength i = m - P.n₀

/-- **`TileGood C P j T`**: the trial hypotheses on the record entering the tile block. An
aborted record enters a halted block (no query, no failure), so it is always good. -/
def TileGood : Set (RunRecord d m) := {x | x.aborted = false → TileGoodCore C P j T x}

/-- The orders `π_{j,T,a}` permute the `|T|` sites of the tile (05:338–343). -/
def TileOrderSizes (M : ℕ → ℕ) : Prop :=
  ∀ a, M (tileOrderIndex j T a) = (tileSites (P.cover j) T).card

/-- The block of tile `T` has started trial number `K` (`K = 0`: the first trial). -/
def reachedAttempt (M : ℕ → ℕ) (x : RunRecord d m) (K : ℕ) :
    Set (RandomSources (Torus d m) M) :=
  {ω | ∃ k, K ≤ (localState M (tileBlock P j T) x k ω).2.attempt}

end Good

/-! ## Frozen trial contracts (analytic cores) -/

/-- **Frozen contract C4a-core-1 (Lemma `local-trial`, 05:766–870).** For each `C ≥ 1`,
the first trial of the frozen tile block from a non-aborted good record fails with
probability at most `exp(−t^{−c})`, uniformly in the box, the plan, the tile and the record,
once the sweep scale `t` is small. -/
def TileTrialBoundStatement (d : ℕ) (C : ℝ) : Prop :=
  ∃ c > 0, ∃ t0 > 0, ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x → sweepScale P.u m j < t0 →
    sourcesLaw (Torus d m) M (localFirstFail M (tileBlock P j T) x) ≤
      ENNReal.ofReal (Real.exp (-S45.power (sweepScale P.u m j) (-c)))

/-- **The S45 route to C4a-core-1 (05:774–870).** A `TrialInputs` on the source space whose
crossing event contains the first-trial failure; dimension parameter `2d + 1` since the
monitors are padded to one common space of dimension `≲ t^{−6d}`, `≲ t^{−6d}` of them (stopped monitored records of the frozen
trial: S45.ordered_raw_bounds with the uniform order and centred digits, then
S45.ordered_trial_inputs; FAIL ⊆ crossing by S45.local_transfer and
S45.prospective_update). -/
def TileCrossingStatement (d : ℕ) (C : ℝ) : Prop :=
  ∃ C' ≥ 1, ∃ t0 > 0, ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x → sweepScale P.u m j < t0 →
    ∃ (ℱ : Filtration ℕ (inferInstance : MeasurableSpace (RandomSources (Torus d m) M)))
      (s : ℕ) (a : S45.TrialInputs (sourcesLaw (Torus d m) M) ℱ s (2 * d + 1) (sweepScale P.u m j) C'),
      localFirstFail M (tileBlock P j T) x ⊆ a.crossing

/-- **Frozen contract C4a-core-2 (retries, 05:872–905).** For each `C ≥ 1`, at a digit sweep
before the cutoff (`j ≤ ⌊m/2⌋`), the block of a non-aborted good record reaches trial number
`K` with probability at most `p^K`, `p = exp(−t^{−c})`, uniformly, once `t` is small. -/
def TileRetryStatement (d : ℕ) (C : ℝ) : Prop :=
  ∃ c > 0, ∃ t0 > 0, ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m / 2 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x → sweepScale P.u m j < t0 →
    ∀ K : ℕ, sourcesLaw (Torus d m) M (reachedAttempt P j T M x K) ≤
      ENNReal.ofReal (Real.exp (-S45.power (sweepScale P.u m j) (-c)) ^ K)

end AndersonAC.AgentS78
