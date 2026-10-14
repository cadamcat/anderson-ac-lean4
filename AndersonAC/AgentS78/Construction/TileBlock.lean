import AndersonAC.AgentS78.Construction.SimpleBlocks
import AndersonAC.AgentS78.Construction.Schedule

/-!
# Ordinary tile block
Paper: 05-local-sweeps.tex:338–530 (trials and their records), 04-sweep.tex:36–90 and
190–228 (the duplicated ports and the scalar of one deletion), 08-history.tex:340–368 (the
final residual sweep), 02-state.tex:14–25 (scales).

One block is the whole sequence of trials of one tile `T` in one sweep: the first trial,
then (at stages `j ≤ ⌊m/2⌋`) the auxiliary retries until one is accepted.

## Indexing of the sweeps

* The *digit sweep into stage `j`* (`n₀ < j ≤ m`) is the paper's sweep at scale
  `n = j − 1` (–40): `t = t_{j−1} = stageScale u (j−1) m`,
  `θ = t_j / t_{j−1}`, `w = 1 − θ = 3 s_{j−1} / (4 t_{j−1})`. Its first trial inserts at a
  coupled site the next true digit, of amplitude `√(3 s_{j−1}/4)` (05:349–351,
  02-state.tex:89), i.e. digit number `j − n₀` of the paper, Lean index `prefixLength i`
  (= `j − 1 − n₀` on actual runs, –13).
* The *final residual sweep* (–41, 05:353–359, 08:340–368) is a separate sweep at scale
  `m`: `t = t_m = 2η = stageScale u m m`, `θ = w = 1/2`, and it inserts the whole remaining
  true suffix. In this file it has the post-sweep index `j = m + 1` (any `j > m`).
  The paper has `m − n₀` digit sweeps (into `n₀+1, …, m`) **and** this final sweep, so the
  final sweep is not the sweep into `m`.

## The scalar of one deletion (04:198–228)

Deleting the bit port `x = (i, false)` adds the physical increment `ζ = k_x² ξ₀ = √w ξ₀` to
the partial potential at `i`; the port scalar of the `S45.StepRel` update is
`ξ₀ = ζ / √w`, with the port damping `r_x = k_x² r_i` of `S45.splitPorts θ`
(–80). Here `ζ = √(3 s_{j−1}/4) ε` for a digit (true or auxiliary) and
`ζ = Σ_{k ≥ h} λ 2^{-(k+1)} ε_{i,k}` (Lean digit indices, `λ² = 3u 4^{-n₀}`) for the final
suffix, so `ξ₀ = √2 ζ` there (08:351–353).

## One trial (05:338–420, 466–510)

A trial reveals the uniform order `π_{j,T,a}` of the `M` physical sites of `T` one slot at a
time (`Query.nextOrder`). A slot is skipped when its site is terminal (05:343) or its bit
port is no longer live in the trial's current prefix (never on actual runs, since `π` is a
permutation and every included pivot is used once, 05:398–401). At an active slot the scalar
is queried (`trueDigit` / `trueSuffix` at a coupled site in the first trial, the designated
auxiliary sign `ε^aux_{j,T,0,i}` at a pending site in the first trial, the new family
`ε^aux_{j,T,a,i}` at every active site in retry `a ≥ 1`, 05:349–353), the bit port is
deleted by the `S45.StepRel` update, and the new prefix is tested: the trial continues
precisely when the denominator of the update is nonzero, the whole included prefix is
`S45.Sequence.valid` with `D₀` the duplicated stage-start Laplacian (05:466–480), and the
trial's own records satisfy `S45.localBudget` for the stage's tile cover (05:482–499).
It stops and fails at the first violation, retaining the violating update in the history
(05:501–504). After all `M` slots it is accepted.

The provisional prefix lives in the scratch (`TileScratch.seq`); the committed record is not
changed during a trial, so the rollback of 05:507–509 is: drop the scratch. The retained
history (all queries and answers) is kept by the S2 run itself.

* Failure of the first trial: mark every active site of `T` pending with the label
  `⟨j, tile, anchor⟩` (05:512–514, –47, anchor = designated site), set
  `firstFail`. Then abort if `j > ⌊m/2⌋` (late stage or final sweep: 05:519–521,
  08:313–318, 05:353–359), else retry.
* Failure of a retry: no new label; retry again with the next family and order
  (05:515–518).
* Acceptance: commit the prefix as `record.sweep`, add the increments to `installed`
  (the real partial potential, –55, 202), and advance `prefixLength` at the coupled
  sites whose true digit was consumed (05:526–528).

Defensive guards (never active on actual runs, documented at their definitions): an order
query is issued only while fewer than `M` entries of that order were revealed; an auxiliary
sign is queried only if this block has not queried it before; a slot whose bit port is not
live is skipped; a zero update denominator counts as a failure (the paper excludes it by
Lemma `local-prospective`, 05:503–506).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer signValue binarySuffix)

/-! ## Stage parameters -/

/-- The duplicated port space of a sweep (`S45.initialPorts`): `(i, false)` is the bit port,
`(i, true)` the reserve port of site `i` (–71). -/
abbrev Port (d m : ℕ) := S45.initialPorts (Torus d m)

/-- The final residual sweep has post-sweep index `m + 1` (any `j > m`). -/
def IsFinalSweep (m j : ℕ) : Prop := m < j

instance (m j : ℕ) : Decidable (IsFinalSweep m j) := inferInstanceAs (Decidable (m < j))

/-- Scale of the sweep with post-sweep index `j` (–41). -/
def sweepScale (u : ℝ) (m j : ℕ) : ℝ :=
  if IsFinalSweep m j then stageScale u m m else stageScale u (j - 1) m

/-- `θ` of the sweep with post-sweep index `j` (–41). -/
def sweepTheta (u : ℝ) (m j : ℕ) : ℝ :=
  if IsFinalSweep m j then 1 / 2 else stageScale u j m / stageScale u (j - 1) m

/-- `w = 1 − θ`, the bit-port weight `k_bit⁴` (67–69). -/
def sweepW (u : ℝ) (m j : ℕ) : ℝ := 1 - sweepTheta u m j

/-- The coupling `λ` of a box: `u = (λ²/3) 4^{n₀}` (02-state.tex:19–24). -/
def couplingOf (u : ℝ) (n₀ : ℕ) : ℝ := Real.sqrt (3 * u / 4 ^ n₀)

/-- Digit amplitude `√(3 s_n / 4)`, `s_n = u 4^{-n}` (02-state.tex:24, 89; 05:349). -/
def digitAmp (u : ℝ) (n : ℕ) : ℝ := Real.sqrt (3 * (u / 4 ^ n) / 4)

/-- Port damping `r_x = k_x² r_i` of the duplicated state (–80); the same expression as
`((S45.splitPorts _ θ).liftState old).r` in `S45.ordinary_sweep_endpoint`. -/
def portR {d m : ℕ} (θ : ℝ) (r : Torus d m → ℂ) : Port d m → ℂ :=
  ((S45.splitPorts (Torus d m) θ).liftState ⟨0, r⟩).r

/-- The tile cover of one sweep, at that sweep's scale `t`. -/
structure StageCover (d m : ℕ) (t : ℝ) where
  b : ℝ
  C : ℝ
  dist : Port d m → Port d m → ℝ
  cover : S45.TileCover (P := Port d m) (I := Torus d m) d t b C dist

/-- Deterministic data of all ordinary sweeps of one box: `n₀`, `u` and one tile cover per
sweep (a deterministic choice per stage, supplied by the run designer). -/
structure TilePlan (d m : ℕ) where
  n₀ : ℕ
  u : ℝ
  cover : (j : ℕ) → StageCover d m (sweepScale u m j)

/-! ## Tiles, anchors and source indices -/

/-- The physical sites of tile `T`: the sites whose bit port lies in the cover's tile. -/
def tileSites {d m : ℕ} {t : ℝ} (C : StageCover d m t) (T : Fin C.cover.count) :
    Finset (Torus d m) := by
  classical
  exact Finset.univ.filter fun i => ((i, false) : Port d m) ∈ C.cover.tile T

/-- The `v`-th site of a finite set of sites in the fixed site order (`none` if `v ≥ card`). -/
def siteAt {d m : ℕ} (S : Finset (Torus d m)) (v : ℕ) : Option (Torus d m) :=
  ((S.map (siteRank d m).toEmbedding).sort (· ≤ ·))[v]?.map (siteRank d m).symm

/-- A fixed site. -/
def site₀ (d m : ℕ) : Torus d m := (siteRank d m).symm ⟨0, siteCount_pos d m⟩

/-- The designated site (label anchor) of a tile: its least site. -/
def tileAnchor {d m : ℕ} {t : ℝ} (C : StageCover d m t) (T : Fin C.cover.count) : Torus d m :=
  (siteAt (tileSites C T) 0).getD (site₀ d m)

/-- Order index of `π_{j,T,a}` (tag `0` = tile blocks). -/
def tileOrderIndex (j T a : ℕ) : ℕ := Nat.pair 0 (Nat.pair (Nat.pair j T) a)

/-- Auxiliary sign index of `ε^aux_{j,T,a,i}` (tag `0` = tile blocks). Family `a = 0` is the
designated first-trial family of pending sites; retry `a ≥ 1` uses family `a`. -/
def tileAuxIndex {d m : ℕ} (j T a : ℕ) (i : Torus d m) : ℕ :=
  Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair j T) a) (siteRank d m i))

/-- Orders used by the block of tile `T` of sweep `j`. -/
def tileOrderSet (j T : ℕ) : Set ℕ := {o | ∃ a, o = tileOrderIndex j T a}

/-- Auxiliary signs used by the block of tile `T` of sweep `j`. -/
def tileAuxSet (d m j T : ℕ) : Set ℕ := {k | ∃ a, ∃ i : Torus d m, k = tileAuxIndex j T a i}

/-! ## Scratch state and the record operations -/

/-- Internal data of a running tile block. -/
structure TileScratch (d m : ℕ) where
  /-- trial number `a` (`0` = first trial) -/
  attempt : ℕ
  /-- the included sweep prefix: committed prefix followed by this trial's steps -/
  seq : S45.Sequence (Port d m)
  /-- the site exposed at the current slot, waiting for its scalar -/
  site : Option (Torus d m)
  /-- physical increments inserted by this trial -/
  added : Torus d m → ℝ
  /-- sites whose next true digit this trial consumed -/
  consumed : Torus d m → Bool
  halted : Bool
  /-- latched: the first trial has failed -/
  firstFail : Bool
  /-- number of entries of each order revealed by this block -/
  orderCount : ℕ → ℕ
  /-- auxiliary signs queried by this block -/
  auxUsed : ℕ → Bool

section Ops
variable {d m : ℕ}

/-- The `S45.StepRel` update: delete the pivot `x` with scalar `ξ` (S45.StepRel.update). -/
def stepLive (t : ℝ) (r : Port d m → ℂ) (a : S45.LiveState (Port d m)) (x : Port d m)
    (ξ : ℝ) : S45.LiveState (Port d m) where
  live := a.live.erase x
  g := S45.mask (a.live.erase x) (fun i j => a.g i j -
    ((ξ : ℂ) + t * r x) * a.g i x * a.g x j / (1 + ((ξ : ℂ) + t * r x) * a.g x x))

/-- Denominator of the update (S45.StepRel.denominator). -/
def stepDen (t : ℝ) (r : Port d m → ℂ) (a : S45.LiveState (Port d m)) (x : Port d m)
    (ξ : ℝ) : ℂ := 1 + ((ξ : ℂ) + t * r x) * a.g x x

/-- Append one step to a sequence. -/
def extendSeq (q : S45.Sequence (Port d m)) (b : S45.LiveState (Port d m)) (x : Port d m)
    (ξ : ℝ) : S45.Sequence (Port d m) where
  length := q.length + 1
  state k := if k = q.length + 1 then b else q.state k
  pivot k := if k = q.length then some x else q.pivot k
  scalar k := if k = q.length then ξ else q.scalar k

/-- The fresh scratch of a trial (the committed prefix, nothing inserted). -/
def trialScratch (x : RunRecord d m) (sc : TileScratch d m) (a : ℕ) : TileScratch d m :=
  { sc with
    attempt := a
    seq := x.sweep
    site := none
    added := fun _ => 0
    consumed := fun _ => false }

/-- The scratch at block entry. -/
def initScratch (x : RunRecord d m) : TileScratch d m where
  attempt := 0
  seq := x.sweep
  site := none
  added := fun _ => 0
  consumed := fun _ => false
  halted := false
  firstFail := false
  orderCount := fun _ => 0
  auxUsed := fun _ => false

/-- Commit an accepted trial (05:505–506, 526–528). -/
def commitTrial (x : RunRecord d m) (sc : TileScratch d m) (finalSweep : Bool) : RunRecord d m :=
  { x with sweep := sc.seq
           installed := fun i => x.installed i + sc.added i
           terminal := if finalSweep then
             x.terminal ∪ Finset.univ.filter (fun i => sc.consumed i = true) else x.terminal
           prefixLength := fun i => x.prefixLength i +
             if sc.consumed i = true && !finalSweep then 1 else 0 }

open Classical in
/-- Whole-tile marking of a first-trial failure (05:512–514, –47). -/
def markTile (S : Finset (Torus d m)) (label : BirthLabel (Torus d m)) (x : RunRecord d m) :
    RunRecord d m :=
  { x with pending := x.pending ∪ (S ∩ x.endpoint.active)
           latest := fun i => if i ∈ S ∧ i ∈ x.endpoint.active then label else x.latest i }

/-- Record the issued query in the block's own query counts. -/
def logQuery (q : Query (Torus d m)) (sc : TileScratch d m) : TileScratch d m :=
  { sc with orderCount := fun o => sc.orderCount o + if q = Query.nextOrder o then 1 else 0
            auxUsed := fun k => sc.auxUsed k || decide (q = Query.auxiliary k) }

end Ops

/-! ## The block -/

section Block
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

/-- Sites of the tile. -/
abbrev TS : Finset (Torus d m) := tileSites (P.cover j) T

/-- The stage-start duplicated Laplacian `D₀` (05:327–331), read off the sweep's state 0. -/
def stageD0 (x : RunRecord d m) : S45.RMat (Port d m) :=
  ((x.sweep.state 0).ambient (portR (sweepTheta P.u m j) x.r)).D (sweepScale P.u m j)

/-- The continuation test after an active slot (05:466–504): nonzero denominator, validity
of the whole included prefix, local budgets of this trial's records. `x` is the committed
record (unchanged during a trial), so the trial's steps are `[x.sweep.length, q.length)`. -/
def trialOk (x : RunRecord d m) (q : S45.Sequence (Port d m)) (den : ℂ) : Prop :=
  let t := sweepScale P.u m j
  let r := portR (sweepTheta P.u m j) x.r
  let K := Finset.Ico x.sweep.length q.length
  den ≠ 0 ∧ q.valid t r (stageD0 P j x) q.length ∧
    S45.localBudget (P.cover j).cover T (q.Jrecord t r K) (q.Lrecord t r K)
      (q.lagRecord t r K) (q.rowRecord t r Finset.univ K)
      (q.rowRecord t r S45.reserves K)

/-- Is the site an active (non-terminal) site of the tile? -/
def activeIn (x : RunRecord d m) (i : Torus d m) : Prop :=
  i ∈ TS P j T ∧ i ∈ x.endpoint.active ∧ i ∉ x.terminal

/-- Does the current slot at site `i` use the true input? (first trial, coupled site) -/
def usesTrue (s : RunRecord d m × TileScratch d m) (i : Torus d m) : Prop :=
  s.2.attempt = 0 ∧ i ∉ s.1.pending

open Classical in
/-- The query the running block wants to issue next (05:338–359). -/
def tileQuery (s : RunRecord d m × TileScratch d m) : Query (Torus d m) :=
  match s.2.site with
  | none =>
    -- next slot of `π_{j,T,a}`, or acceptance after all `M` slots
    if s.2.orderCount (tileOrderIndex j T s.2.attempt) < (TS P j T).card then
      Query.nextOrder (tileOrderIndex j T s.2.attempt)
    else Query.decision
  | some i =>
    if activeIn P j T s.1 i then
      if usesTrue s i then
        (if IsFinalSweep m j then Query.trueSuffix i (s.1.prefixLength i)
          else Query.trueDigit i (s.1.prefixLength i))
      else
        (if s.2.auxUsed (tileAuxIndex j T s.2.attempt i) then Query.decision
          else Query.auxiliary (tileAuxIndex j T s.2.attempt i))
    else Query.decision

/-- The answered sign of a coordinate (`false` if absent, never on a valid answer). -/
def answeredSign {ι : Type} [Fintype ι] [DecidableEq ι] (a : Answer ι)
    (z : AndersonAC.S2.SignIndex ι) : Bool := (a.1 z).getD false

/-- The physical increment `ζ` read from the answer to a scalar query at site `i`
(05:349–353, 08:340–353). -/
def tileIncrement (q : Query (Torus d m)) (a : Answer (Torus d m)) : ℝ :=
  match q with
  | Query.trueDigit i h => digitAmp P.u (j - 1) * signValue (answeredSign a (Sum.inl (i, h)))
  | Query.auxiliary k => digitAmp P.u (j - 1) * signValue (answeredSign a (Sum.inr k))
  | Query.trueSuffix i h =>
      binarySuffix (couplingOf P.u P.n₀) h (fun k => answeredSign a (Sum.inl (i, k)))
  | _ => 0

open Classical in
/-- A failed trial (05:501–521). -/
def failTrial (s : RunRecord d m × TileScratch d m) : RunRecord d m × TileScratch d m :=
  let x' := if s.2.attempt = 0 then
    markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1 else s.1
  if m / 2 < j then
    ({ x' with aborted := true }, { s.2 with firstFail := true, halted := true, site := none })
  else
    (x', { trialScratch x' s.2 (s.2.attempt + 1) with firstFail := true })

open Classical in
/-- One active slot at site `i` with physical increment `ζ`: delete the bit port, test. -/
def scalarStep (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ) :
    RunRecord d m × TileScratch d m :=
  let t := sweepScale P.u m j
  let r := portR (sweepTheta P.u m j) s.1.r
  let x : Port d m := (i, false)
  let ξ := ζ / Real.sqrt (sweepW P.u m j)
  let a := s.2.seq.state s.2.seq.length
  let q' := extendSeq s.2.seq (stepLive t r a x ξ) x ξ
  if trialOk P j T s.1 q' (stepDen t r a x ξ) then
    (s.1, { s.2 with
      seq := q'
      site := none
      added := Function.update s.2.added i (s.2.added i + ζ)
      consumed := Function.update s.2.consumed i
        (decide (usesTrue s i)) })
  else failTrial P j T s

open Classical in
/-- The site exposed by an order answer, if its slot is active (05:343). -/
def exposedSite (s : RunRecord d m × TileScratch d m) (v : Option ℕ) : Option (Torus d m) :=
  match v with
  | none => none
  | some v =>
    match siteAt (TS P j T) v with
    | none => none
    | some i =>
      if i ∈ s.1.endpoint.active ∧ ((i, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live
      then some i else none

/-- One operation of the running block, after the query `q = tileQuery s` was answered. -/
def tileStep (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (a : Answer (Torus d m)) : RunRecord d m × TileScratch d m :=
  match q with
  | Query.nextOrder _ => (s.1, { s.2 with site := exposedSite P j T s a.2 })
  | Query.decision =>
    match s.2.site with
    | none => (commitTrial s.1 s.2 (decide (IsFinalSweep m j)), { s.2 with halted := true })
    | some _ => (s.1, { s.2 with site := none })
  | _ =>
    match s.2.site with
    | none => s
    | some i => scalarStep P j T s i (tileIncrement P j q a)

/-- **The ordinary tile block** of tile `T` in the sweep with post-sweep index `j`. -/
def tileBlock : Block (Torus d m) (RunRecord d m) (RunRecord d m × TileScratch d m) where
  enter x := if x.aborted then (x, { initScratch x with halted := true }) else (x, initScratch x)
  next s := if s.2.halted then Query.decision else tileQuery P j T s
  update s a := if s.2.halted then s else
    tileStep P j T (s.1, logQuery (tileQuery P j T s) s.2) (tileQuery P j T s) a
  halted s := s.2.halted
  exit s := s.1
  firstFail s := s.2.firstFail

/-- The fresh pattern of the first trial: the coupled active sites of `T` from their prefix
lengths, the designated first-family auxiliary signs of its pending active sites, and the
first order `π_{j,T,0}` (05:512–528). -/
def tilePattern (x : RunRecord d m) : FreshPattern (Torus d m) := by
  classical
  if x.aborted then
    exact { sites := ∅, height := x.prefixLength, aux := ∅,
            orders := {tileOrderIndex j T 0} }
  else
    exact { sites := ((TS P j T ∩ x.endpoint.active) \ x.pending) \ x.terminal
            height := x.prefixLength
            aux := (((TS P j T ∩ x.endpoint.active) ∩ x.pending) \ x.terminal).image
              (tileAuxIndex j T 0)
            orders := {tileOrderIndex j T 0} }

end Block

end AndersonAC.AgentS78
