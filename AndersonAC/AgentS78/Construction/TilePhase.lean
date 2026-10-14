import AndersonAC.AgentS78.Construction.TilePhaseSeq
import AndersonAC.AgentS78.Construction.BoundaryInv
import AndersonAC.AgentS78.Construction.ResetBlock
import AndersonAC.AgentS78.Construction.PhysicalIdentity

/-!
# the tile-phase record invariant (the sweep into stage `j`)

The invariant is described in 04-sweep.tex:60–100 (duplication and swept ports) and
05-local-sweeps.tex:320–560 (stage start, trials, records, and validity).

The sweep into stage `j` processes the tiles of `P.cover j` in anchor order. Between two tile
blocks the committed record satisfies `TileSweepInv … done`, where `done` is the set of tiles
already processed:

* `hist` — the committed endpoint ends a stage history up to stage `j − 1` (BoundaryInv.lean);
  the sweep does not change the endpoint, only `x.sweep`;
* `plan`, `start` — the plan facts and the duplicated stage-start clauses (05:320–337); they
  depend only on `x.sweep.state 0` and `x.r`, which the tile blocks never change;
* `start_live` — **adapter clause (TileGoodCore v3)**: the sweep starts from the ports of the
  active sites, `liveStart x` (`sweepStartLiveState`);
* the committed prefix: well formed, valid at every `k`, bit pivots with `|ξ| ≤ 2√t`;
* `blocks` — the accepted tile records (05:399–419, 452–462) with their local budgets; tiles
  outside `done` own no step;
* `done_deleted` — every active bit port of a processed tile is deleted (completeness of the
  accepted trials, 05:338–344: the order `π` is a permutation of the tile);
* the clauses on unprocessed tiles: no terminal active site, and at the final sweep no pending
  site and consumed prefix `m − n₀` (05:353–355, 08:340–353).

`TileSweepCore … done x` with `T ∉ done` gives every clause of `TileGoodCore` for `T` except
the v3-dependent `start_live`/`tile_live`, which hold through the adapters
`tileGoodCore_of_sweep` (under `x.endpoint.active = univ`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query Answer)

variable {d m : ℕ}

/-! ## Definitions -/

section Defs
variable (C : ℝ) (P : TilePlan d m) (j : ℕ)

/-- The live ports at the start of a sweep: both ports of every active site (
`sweepStartLiveState`; the intended v3 live set). -/
def liveStart (x : RunRecord d m) : Finset (Port d m) :=
  Finset.univ.filter fun p : Port d m => p.1 ∈ x.endpoint.active

/-- The duplicated stage-start state determined by the sweep's state 0 and the damping. -/
def startState (a : S45.LiveState (Port d m)) (r : Torus d m → ℂ) : S45.State (Port d m) :=
  a.ambient (portR (sweepTheta P.u m j) r)

theorem stageStart_eq (x : RunRecord d m) :
    stageStart P j x = startState P j (x.sweep.state 0) x.r := rfl

theorem stageD0_eq (x : RunRecord d m) :
    stageD0 P j x = (startState P j (x.sweep.state 0) x.r).D (sweepScale P.u m j) := rfl

/-- Plan facts of the sweep (05:240–256, 05:342–343, 05:860–864). -/
structure PlanClauses : Prop where
  one_le : 1 ≤ C
  cover_b : 0 < (P.cover j).b ∧ (P.cover j).b ≤ sweepScale P.u m j
  cover_C : (P.cover j).C ≤ C
  shell : S45.ShellBounds d C (P.cover j).dist
  tile_card : ∀ T, ((tileSites (P.cover j) T).card : ℝ) ≤
    C * S45.power (sweepScale P.u m j) (-6 * (d : ℝ))
  inner_card : ∀ T, (((P.cover j).cover.inner T).card : ℝ) ≤
    C * S45.power (sweepScale P.u m j) (-6 * (d : ℝ))

/-- The v3 duplicated stage start on the ports of the active sites, as a function of the
committed endpoint and damping (`stageStartV3 P j x = startV3 P j x.endpoint x.r`). -/
def startV3 (e : Endpoint (Torus d m)) (r : Torus d m → ℂ) :
    S45.State (S45.initialPorts {i // i ∈ e.active}) :=
  (S45.splitPorts {i // i ∈ e.active} (sweepTheta P.u m j)).liftState
    ⟨fun i k => e.g i.1 k.1, fun i => r i.1⟩

theorem stageStartV3_eq (x : RunRecord d m) : stageStartV3 P j x = startV3 P j x.endpoint x.r :=
  rfl

/-- **Duplicated stage-start clauses, TileGoodCore** (05-local-sweeps.tex:320–337):
the `start_*` clauses on the active-site ports `startV3 P j e r` and `prefix_decay` on the
sweeps from the start state `a`. Adapter: only this structure follows later changes of the
v3 start clauses. -/
structure StartClauses (e : Endpoint (Torus d m)) (r : Torus d m → ℂ)
    (a : S45.LiveState (Port d m)) : Prop where
  start_prestate : ∃ Λplus Wstar : S45.Form (S45.initialPorts {i // i ∈ e.active}),
    S45.Prestate (sweepScale P.u m j) C Λplus Wstar (startV3 P j e r) ∧
    (open scoped Matrix.Norms.L2Operator in
      ‖(startV3 P j e r).K (sweepScale P.u m j)‖ ≤ 1 / 3) ∧
    (∀ y, S45.neutral y → 0 ≤ Λplus y) ∧
    (∀ y, S45.neutral y → (startV3 P j e r).X (sweepScale P.u m j) y ≤
      (1 + S45.power (sweepScale P.u m j) S45.kappa) *
        (∑ i, y i ^ 2 / (startV3 P j e r).p i ^ 2) +
        C * sweepScale P.u m j * Λplus y)
  start_lag : ∀ i, (startV3 P j e r).lag (sweepScale P.u m j) i = 0
  start_comparison : S45.formComparable
    (S45.qform ((startV3 P j e r).D (sweepScale P.u m j)))
    (S45.spatialEnergy (fun p => (P.cover j).cover.site ((p.1.1, p.2) : Port d m))
      (P.cover j).b (P.cover j).cover.energy) C
  start_rows : ∀ i, (startV3 P j e r).fourthRow (sweepScale P.u m j) Finset.univ i ≤
    3 / 4 * S45.rowCap (sweepScale P.u m j)
  start_reserve_rows : ∀ i ∈ (S45.reserves : Finset (S45.initialPorts {i // i ∈ e.active})),
    (startV3 P j e r).fourthRow (sweepScale P.u m j) S45.reserves i ≤
      sweepTheta P.u m j ^ 2 * S45.rowCap (sweepScale P.u m j)
  start_decay : ∀ p q, ‖(startV3 P j e r).h (sweepScale P.u m j) p q‖ ≤
    C / Real.sqrt (sweepScale P.u m j) *
      Real.exp (-(sweepScale P.u m j) ^ 3 *
        (P.cover j).dist ((p.1.1, p.2) : Port d m) ((q.1.1, q.2) : Port d m) / C)
  start_far_decay : ∀ p q,
    C * S45.power (sweepScale P.u m j) (-2) <
      (P.cover j).dist ((p.1.1, p.2) : Port d m) ((q.1.1, q.2) : Port d m) →
    ‖(startV3 P j e r).h (sweepScale P.u m j) p q‖ ≤
      C / Real.sqrt (sweepScale P.u m j) *
        Real.exp (-(sweepScale P.u m j) *
          (P.cover j).dist ((p.1.1, p.2) : Port d m) ((q.1.1, q.2) : Port d m) / C)
  prefix_decay : ∀ (q : S45.Sequence (Port d m)),
    q.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) r) →
    q.state 0 = a →
    (∀ k < q.length, ∀ y, q.pivot k = some y → y.2 = false) →
    ∀ k ≤ q.length,
      q.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) r)
        ((startState P j a r).D (sweepScale P.u m j)) k →
      (∀ p q' : (q.state k).live,
        ‖((q.state k).state (portR (sweepTheta P.u m j) r)).h (sweepScale P.u m j) p q'‖ ≤
          C / Real.sqrt (sweepScale P.u m j) *
            Real.exp (-(sweepScale P.u m j) ^ 3 * (P.cover j).dist p.1 q'.1 / C)) ∧
      (∀ p q' : (q.state k).live,
        C * S45.power (sweepScale P.u m j) (-2) < (P.cover j).dist p.1 q'.1 →
        ‖((q.state k).state (portR (sweepTheta P.u m j) r)).h (sweepScale P.u m j) p q'‖ ≤
          C / Real.sqrt (sweepScale P.u m j) *
            Real.exp (-(sweepScale P.u m j) * (P.cover j).dist p.1 q'.1 / C))

/-- The accepted tile records of the committed prefix (05:399–419, 452–462): a partition of the
steps into tile blocks, pivots in their tiles, local budgets, unprocessed tiles empty. -/
def SweepBlocks (done : Finset (Fin (P.cover j).cover.count)) (x : RunRecord d m) : Prop :=
  ∃ blocks : Fin (P.cover j).cover.count → Finset ℕ,
    (∀ k < x.sweep.length, ∃! S, k ∈ blocks S) ∧
    (∀ S, blocks S ⊆ Finset.range x.sweep.length) ∧
    (∀ k < x.sweep.length, ∀ y, x.sweep.pivot k = some y → ∀ S, k ∈ blocks S →
      y ∈ (P.cover j).cover.tile S) ∧
    (∀ S, S ∉ done → blocks S = ∅) ∧
    (∀ S, S45.localBudget (P.cover j).cover S
      (x.sweep.Jrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (blocks S))
      (x.sweep.Lrecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (blocks S))
      (x.sweep.lagRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (blocks S))
      (x.sweep.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        Finset.univ (blocks S))
      (x.sweep.rowRecord (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
        S45.reserves (blocks S)))

/-- **The tile-phase invariant on a non-aborted record** (sweep into stage `j`, tiles of
`done` processed). `n₀ u E ρ Cb` are the stage-history data of BoundaryInv.lean. -/
structure TileSweepCore (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (Cb : ℝ)
    (done : Finset (Fin (P.cover j).cover.count)) (x : RunRecord d m) : Prop where
  hist : BoundaryHist n₀ u E ρ Cb (j - 1) x.endpoint x.r
  plan : PlanClauses C P j
  start : StartClauses C P j x.endpoint x.r (x.sweep.state 0)
  /-- Adapter clause (v3): the sweep starts from the ports of the active sites. -/
  start_live : (x.sweep.state 0).live = liveStart x
  /-- The sweep starts from the duplicated committed endpoint (–80;
  `sweepStartLiveState`), which the tile blocks do not change. -/
  start_lift : x.sweep.state 0 = sweepStartLiveState (sweepTheta P.u m j) x
  wellFormed : x.sweep.wellFormed (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
  valid : ∀ k ≤ x.sweep.length, x.sweep.valid (sweepScale P.u m j)
    (portR (sweepTheta P.u m j) x.r) (stageD0 P j x) k
  bit_pivots : ∀ k < x.sweep.length, ∀ y, x.sweep.pivot k = some y → y.2 = false
  scalar_bound : ∀ k < x.sweep.length,
    |x.sweep.scalar k| ≤ 2 * Real.sqrt (sweepScale P.u m j)
  /-- Every committed step deletes a port (tile blocks append only `some` pivots). -/
  pivots_some : ∀ k < x.sweep.length, x.sweep.pivot k ≠ none
  /-- Physical identity of the sweep-start record (02-state.tex:231–247): the installed values
  minus this sweep's increments match the committed `M` (which records the increments only at
  the sweep end). -/
  physical : PhysicalIdentity E
    { x with installed := fun i => x.installed i - sweepIncrement (sweepTheta P.u m j) x.sweep i }
  blocks : SweepBlocks P j done x
  done_deleted : ∀ S ∈ done, ∀ i ∈ tileSites (P.cover j) S, i ∈ x.endpoint.active →
    ((i, false) : Port d m) ∉ (x.sweep.state x.sweep.length).live
  undone_nonterminal : ∀ S, S ∉ done → ∀ i ∈ tileSites (P.cover j) S,
    i ∈ x.endpoint.active → i ∉ x.terminal
  final_no_pending : IsFinalSweep m j → ∀ S, S ∉ done → ∀ i ∈ tileSites (P.cover j) S,
    i ∈ x.endpoint.active → i ∉ x.pending
  final_prefix : IsFinalSweep m j → ∀ S, S ∉ done → ∀ i ∈ tileSites (P.cover j) S,
    i ∈ x.endpoint.active → x.prefixLength i = m - P.n₀

/-- `PhysicalIdentity` reads only the endpoint and the installed values. -/
theorem physicalIdentity_congr {E : ℝ} {a b : RunRecord d m} (he : a.endpoint = b.endpoint)
    (hi : a.installed = b.installed) (h : PhysicalIdentity E a) : PhysicalIdentity E b := by
  unfold PhysicalIdentity installedShifted at *
  rw [← he, ← hi]; exact h

/-- **The tile-phase invariant**: aborted records are unconstrained (no block acts on them). -/
def TileSweepInv (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (Cb : ℝ)
    (done : Finset (Fin (P.cover j).cover.count)) : Set (RunRecord d m) :=
  {x | x.aborted = false → TileSweepCore C P j n₀ u E ρ Cb done x}

end Defs

/-! ## From the invariant to the trial hypotheses of an unprocessed tile -/

section ToGood
variable {C : ℝ} {P : TilePlan d m} {j : ℕ} {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}
  {done : Finset (Fin (P.cover j).cover.count)} {x : RunRecord d m}

theorem SweepBlocks.accepted {T : Fin (P.cover j).cover.count} (hT : T ∉ done)
    (h : SweepBlocks P j done x) : AcceptedTiles P j T x := by
  obtain ⟨blocks, h1, h2, h3, h4, h5⟩ := h
  exact ⟨blocks, h1, h2, h3, h4 T hT, h5⟩

/-- Pivots lie in processed tiles. -/
theorem SweepBlocks.pivot_done (h : SweepBlocks P j done x) {k : ℕ} (hk : k < x.sweep.length)
    {y : Port d m} (hy : x.sweep.pivot k = some y) :
    ∃ S ∈ done, y ∈ (P.cover j).cover.tile S := by
  obtain ⟨blocks, h1, -, h3, h4, -⟩ := h
  obtain ⟨S, hS, -⟩ := h1 k hk
  refine ⟨S, ?_, h3 k hk y hy S hS⟩
  by_contra hSd
  rw [h4 S hSd] at hS
  exact absurd hS (Finset.notMem_empty k)

/-- The tile of a port is unique (`TileCover.cover`). -/
theorem tile_unique {S S' : Fin (P.cover j).cover.count} {y : Port d m}
    (h : y ∈ (P.cover j).cover.tile S) (h' : y ∈ (P.cover j).cover.tile S') : S = S' :=
  ((P.cover j).cover.cover y).unique h h'

theorem mem_tileSites {S : Fin (P.cover j).cover.count} {i : Torus d m} :
    i ∈ tileSites (P.cover j) S ↔ ((i, false) : Port d m) ∈ (P.cover j).cover.tile S := by
  classical
  unfold tileSites
  simp

/-- The bit ports of the active sites of an unprocessed tile are live (v3 `tile_live`). -/
theorem TileSweepCore.tile_live_v3 (h : TileSweepCore C P j n₀ u E ρ Cb done x)
    {T : Fin (P.cover j).cover.count} (hT : T ∉ done) :
    ∀ i ∈ tileSites (P.cover j) T, i ∈ x.endpoint.active →
      ((i, false) : Port d m) ∈ (x.sweep.state x.sweep.length).live := by
  intro i hi hact
  refine (mem_live_iff h.wellFormed le_rfl ((i, false) : Port d m)).mpr
    ⟨by rw [h.start_live]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩,
      fun l hl hpl => ?_⟩
  obtain ⟨S, hS, hyS⟩ := h.blocks.pivot_done hl hpl
  have := tile_unique hyS (mem_tileSites.mp hi)
  subst this
  exact hT hS

/-- Distinct pivots at distinct sites (the `distinct` clause). -/
theorem TileSweepCore.distinct (h : TileSweepCore C P j n₀ u E ρ Cb done x) :
    ∀ k l, k < x.sweep.length → l < x.sweep.length → ∀ y y',
      x.sweep.pivot k = some y → x.sweep.pivot l = some y' → y.1 = y'.1 → k = l := by
  intro k l hk hl y y' hy hy' h1
  have h2 : y.2 = y'.2 := by rw [h.bit_pivots k hk y hy, h.bit_pivots l hl y' hy']
  have : y = y' := Prod.ext h1 h2
  subst this
  exact pivot_injective h.wellFormed hk hl hy hy'

/-- The invariant gives `TileGoodCore`
for every unprocessed tile. -/
theorem tileGoodCore_of_sweep (h : TileSweepCore C P j n₀ u E ρ Cb done x)
    {T : Fin (P.cover j).cover.count} (hT : T ∉ done) : TileGoodCore C P j T x where
  one_le := h.plan.one_le
  cover_b := h.plan.cover_b
  cover_C := h.plan.cover_C
  shell := h.plan.shell
  tile_card := h.plan.tile_card T
  inner_card := h.plan.inner_card T
  wellFormed := h.wellFormed
  start_live := h.start_lift
  start_prestate := h.start.start_prestate
  start_lag := h.start.start_lag
  start_comparison := h.start.start_comparison
  start_rows := h.start.start_rows
  start_reserve_rows := h.start.start_reserve_rows
  start_decay := h.start.start_decay
  start_far_decay := h.start.start_far_decay
  prefix_decay := h.start.prefix_decay
  scalar_bound := h.scalar_bound
  valid := h.valid
  bit_pivots := h.bit_pivots
  distinct := h.distinct
  accepted := h.blocks.accepted hT
  tile_live := h.tile_live_v3 hT
  final_no_pending := fun hf => h.final_no_pending hf T hT
  final_prefix := fun hf => h.final_prefix hf T hT

end ToGood

end AndersonAC.AgentS78
