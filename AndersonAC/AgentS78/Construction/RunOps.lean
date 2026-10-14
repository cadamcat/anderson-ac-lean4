import AndersonAC.AgentS78.Construction.TileBlockFacts
import AndersonAC.AgentS78.Construction.TileBlockMeasurable
import AndersonAC.AgentS78.Construction.ResetBlock
import AndersonAC.AgentS78.Construction.BlockEmbed
import AndersonAC.AgentS78.Construction.ScheduleBlocks
import AndersonAC.AgentS78.Construction.OrderSizes
import AndersonAC.AgentS78.Construction.SimpleDisciplines
import AndersonAC.AgentS78.Construction.ResetAMeas

/-!
# WP10 construction: the operations of the schedule

The operation `(j, k, y)` of a box (Schedule.lean; NOTES.md "Schedule semantics"), for the
stages `n₀ < j ≤ m + 1` (`j = m + 1`: the final residual sweep), on the common internal
state `RunRecord × (TileScratch × ClSc)`:

* `k = 0`: the tile block of the tile anchored at `y` (`tileAt`), if any;
* `k = 1` (at the least site `site₀` only): the sweep end `sweepEndMapTheta θ_j` (θ of TileBlock.lean, `1/2` for the final
  sweep), followed by the snapshot `snapshotMap j` at a clearing stage `j ≤ ⌊m/2⌋`;
* `k = 2`: at a clearing stage, the clearing attempt `clr j y` (muse-s78clear's block,
  a parameter here);
* `k = 3` (at `site₀` only): for `j ≤ m`, the diagonal reset at `t_j`, the cutoff at `j = ⌊m/2⌋`, and the
  stage-start lift `sweepStartMap` for the next sweep.

Query-free operations act only on non-aborted records (`guardMap`); every other index is an
empty block. Proved here: measurability of every operation, and the order/auxiliary index
sets with their disjointness.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query)

variable {d m : ℕ}

theorem measurable_aborted : Measurable (fun x : RunRecord d m => x.aborted) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (RunRecord.measurable_code d m))))))

/-- Apply `f` unless the record is aborted (no operation follows an abort). -/
def guardMap (f : RunRecord d m → RunRecord d m) (x : RunRecord d m) : RunRecord d m :=
  if x.aborted = true then x else f x

theorem guardMap_measurable {f : RunRecord d m → RunRecord d m} (hf : Measurable f) :
    Measurable (guardMap f) :=
  Measurable.ite (measurable_aborted (measurableSet_singleton true)) measurable_id hf

open Classical in
/-- The tile of sweep `j` anchored at `y` (a tile with at least one site). -/
def tileAt (P : TilePlan d m) (j : ℕ) (y : Torus d m) : Option (Fin (P.cover j).cover.count) :=
  if h : ∃ T, (tileSites (P.cover j) T).Nonempty ∧ tileAnchor (P.cover j) T = y then
    some (Classical.choose h) else none

theorem tileAt_anchor (P : TilePlan d m) (j : ℕ) (y : Torus d m) (T : Fin (P.cover j).cover.count)
    (h : tileAt P j y = some T) : tileAnchor (P.cover j) T = y := by
  classical
  unfold tileAt at h
  split_ifs at h with hex
  · cases h; exact (Classical.choose_spec hex).2

/-- The sweep end of stage `j`, with the snapshot at a clearing stage. -/
def endMap (P : TilePlan d m) (j : ℕ) : RunRecord d m → RunRecord d m :=
  (if j ≤ m / 2 then snapshotMap j else id) ∘ sweepEndMapTheta (sweepTheta P.u m j)

/-- Reset of stage `j`, cutoff at `⌊m/2⌋`, and the lift for the next sweep. Since 2026-10-14
(agent-s78con3): the **active-block** reset `resetMapA` of agent-s78phase (the whole-torus
`resetMap` is not damped on proper active sets, `resetMap_not_damped`); so
`stageMap = stageMapA` (StagePhaseOp.lean) by `rfl`. -/
def stageMap (P : TilePlan d m) (j : ℕ) : RunRecord d m → RunRecord d m :=
  sweepStartMap (sweepTheta P.u m (j + 1)) (sweepScale P.u m (j + 1)) ∘
    (if j = m / 2 then cutoffMap else id) ∘ resetMapA (stageScale P.u j m)

theorem endMap_measurable (P : TilePlan d m) (j : ℕ) : Measurable (endMap P j) := by
  unfold endMap
  refine Measurable.comp ?_ (sweepEndMapTheta_measurable _)
  split_ifs
  · exact snapshotMap_measurable j
  · exact measurable_id

theorem stageMap_measurable (P : TilePlan d m) (j : ℕ) : Measurable (stageMap P j) := by
  unfold stageMap
  refine (sweepStartMap_measurable _ _).comp (Measurable.comp ?_ (resetMapA_measurable _))
  split_ifs
  · exact cutoffMap_measurable
  · exact measurable_id

section Ops
variable {ClSc : Type} [MeasurableSpace ClSc]

/-- Tile states inside the common state. -/
def tileEmbed (cl₀ : ClSc) (s : RunRecord d m × TileScratch d m) :
    RunRecord d m × (TileScratch d m × ClSc) := (s.1, s.2, cl₀)

def tileProj (s : RunRecord d m × (TileScratch d m × ClSc)) : RunRecord d m × TileScratch d m :=
  (s.1, s.2.1)

/-- Clearing states inside the common state. -/
def clearEmbed (ts₀ : TileScratch d m) (s : RunRecord d m × ClSc) :
    RunRecord d m × (TileScratch d m × ClSc) := (s.1, ts₀, s.2)

def clearProj (s : RunRecord d m × (TileScratch d m × ClSc)) : RunRecord d m × ClSc :=
  (s.1, s.2.2)

/-- **The operation `(j, k, y)` of the schedule.** -/
def runOp (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (j k : ℕ) (y : Torus d m) :
    Block (Torus d m) (RunRecord d m) (RunRecord d m × (TileScratch d m × ClSc)) :=
  if P.n₀ < j ∧ j ≤ m + 1 then
    if k = 0 then
      match tileAt P j y with
      | some T => (tileBlock P j T).embed (tileEmbed cl₀) tileProj
      | none => simpleBlock (ts₀, cl₀) id
    else if k = 1 then
      (if y = site₀ d m then simpleBlock (ts₀, cl₀) (guardMap (endMap P j))
        else simpleBlock (ts₀, cl₀) id)
    else if k = 2 then
      (if j ≤ m / 2 then (clr j y).embed (clearEmbed ts₀) clearProj
        else simpleBlock (ts₀, cl₀) id)
    else if j ≤ m ∧ y = site₀ d m then simpleBlock (ts₀, cl₀) (guardMap (stageMap P j))
    else simpleBlock (ts₀, cl₀) id
  else simpleBlock (ts₀, cl₀) id

theorem runOp_measurable (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (hclr : ∀ j y, (clr j y).IsMeasurable) (j k : ℕ) (y : Torus d m) :
    (runOp P ts₀ cl₀ clr j k y).IsMeasurable := by
  have hte : Measurable (tileEmbed (d := d) (m := m) cl₀) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have htp : Measurable (tileProj (d := d) (m := m) (ClSc := ClSc)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hce : Measurable (clearEmbed (d := d) (m := m) (ClSc := ClSc) ts₀) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hcp : Measurable (clearProj (d := d) (m := m) (ClSc := ClSc)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  unfold runOp
  split_ifs
  · cases tileAt P j y with
    | some T => exact (tileBlock_measurable P j T).embed hte htp
    | none => exact simpleBlock_measurable _ _ measurable_id
  · exact simpleBlock_measurable _ _ (guardMap_measurable (endMap_measurable P j))
  · exact simpleBlock_measurable _ _ measurable_id
  · exact (hclr j y).embed hce hcp
  · exact simpleBlock_measurable _ _ measurable_id
  · exact simpleBlock_measurable _ _ (guardMap_measurable (stageMap_measurable P j))
  · exact simpleBlock_measurable _ _ measurable_id
  · exact simpleBlock_measurable _ _ measurable_id

/-- Order indices of operation `(j, k, y)`. -/
def runOrderSet (P : TilePlan d m) (j k : ℕ) (y : Torus d m) : Set ℕ :=
  if P.n₀ < j ∧ j ≤ m + 1 ∧ k = 0 then
    match tileAt P j y with
    | some T => tileOrderSet j T
    | none => ∅
  else ∅

/-- Auxiliary indices of operation `(j, k, y)`. -/
def runAuxSet (P : TilePlan d m) (j k : ℕ) (y : Torus d m) : Set ℕ :=
  if P.n₀ < j ∧ j ≤ m + 1 ∧ k = 0 then
    match tileAt P j y with
    | some T => tileAuxSet d m j T
    | none => ∅
  else ∅

theorem tileAt_ne (P : TilePlan d m) {j j' : ℕ} {y y' : Torus d m}
    {T : Fin (P.cover j).cover.count} {T' : Fin (P.cover j').cover.count}
    (h : tileAt P j y = some T) (h' : tileAt P j' y' = some T') (hne : (j, y) ≠ (j', y')) :
    (j, (T : ℕ)) ≠ (j', (T' : ℕ)) := by
  intro heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, hT⟩ := heq
  have hTT : T = T' := Fin.ext hT
  subst hTT
  apply hne
  rw [← tileAt_anchor P j y T h, ← tileAt_anchor P j y' T h']

theorem runOrderSet_disjoint (P : TilePlan d m) :
    Pairwise fun n n' => Disjoint (scheduleSets (d := d) (m := m) (runOrderSet P) n)
      (scheduleSets (runOrderSet P) n') := by
  apply pairwise_disjoint_of_ops
  intro j k y j' k' y' _ _ hne
  unfold runOrderSet
  split_ifs with h1 h2
  · obtain ⟨-, -, rfl⟩ := h1
    obtain ⟨-, -, rfl⟩ := h2
    have hjy : (j, y) ≠ (j', y') := by
      intro h; apply hne; rw [Prod.mk.injEq] at h; rw [h.1, h.2]
    cases hT : tileAt P j y with
    | none => exact Set.empty_disjoint _
    | some T =>
      cases hT' : tileAt P j' y' with
      | none => exact Set.disjoint_empty _
      | some T' => exact tileOrderSet_disjoint (tileAt_ne P hT hT' hjy)
  · exact Set.disjoint_empty _
  · exact Set.empty_disjoint _
  · exact Set.empty_disjoint _

theorem runAuxSet_disjoint (P : TilePlan d m) :
    Pairwise fun n n' => Disjoint (scheduleSets (d := d) (m := m) (runAuxSet P) n)
      (scheduleSets (runAuxSet P) n') := by
  apply pairwise_disjoint_of_ops
  intro j k y j' k' y' _ _ hne
  unfold runAuxSet
  split_ifs with h1 h2
  · obtain ⟨-, -, rfl⟩ := h1
    obtain ⟨-, -, rfl⟩ := h2
    have hjy : (j, y) ≠ (j', y') := by
      intro h; apply hne; rw [Prod.mk.injEq] at h; rw [h.1, h.2]
    cases hT : tileAt P j y with
    | none => exact Set.empty_disjoint _
    | some T =>
      cases hT' : tileAt P j' y' with
      | none => exact Set.disjoint_empty _
      | some T' => exact tileAuxSet_disjoint d m (tileAt_ne P hT hT' hjy)
  · exact Set.disjoint_empty _
  · exact Set.empty_disjoint _
  · exact Set.empty_disjoint _

end Ops

end AndersonAC.AgentS78
