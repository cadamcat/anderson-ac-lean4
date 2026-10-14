import AndersonAC.AgentS78.Construction.TilePhaseComplete
import AndersonAC.AgentS78.Construction.StagePhaseStart
import AndersonAC.AgentS78.Construction.FinalRecord
import AndersonAC.AgentS78.Construction.TilePhasePhysical

/-!
# The sweep end transfers the tile invariant to the clearing phase

After the last tile of a sweep into a digit stage `j ≤ m`, the record satisfies
`TileSweepInv … Finset.univ` (`doneUpTo_all`). The sweep-end operation
`(j, 1, site₀)` is `guardMap (endMap P j)`, applying `sweepEndMapTheta θ_j` and,
at a clearing stage, the snapshot that changes only the components. Its exit carries
`ClearPhase` via `ClearPhaseData.ofSweep'` when the post-sweep endpoint satisfies:

* `SweepEndStatement` (contract): from `TileSweepCore … univ` the hypotheses `sweep`,
  `physical`, `resolventDecay`, `initialComparison`, `initialRows`, `initialLag` of
  `ClearPhaseData.ofSweep'` for `old = x.endpoint`, `sw = (sweepEndMapTheta θ_j x).endpoint`,
  `rOld = x.r` (05:338–560, 04:190–228, Proposition 4.9 = `ordinary_sweep_endpoint`).
  `physical` (the damped identity of `sw`) requires the swept increments to be
  recorded in `endpoint.M`, so the contract states the identity explicitly.
* `sweepEnd_keeps` (proved): the structural reduction to it.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

/-! ## The physical identity after the sweep end -/
theorem TileSweepCore.sweepEndActive_eq {C Cb : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ}
    {ρ : ℂ} {x : RunRecord d m} (h : TileSweepCore C P j n₀ u E ρ Cb Finset.univ x) :
    sweepEndActive x = x.endpoint.active := by
  classical
  ext i
  unfold sweepEndActive
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (h.live_end ((i, true) : Port d m)).trans (by simp)

theorem TileSweepCore.sweepIncrement_inactive {C Cb : ℝ} {P : TilePlan d m} {j n₀ : ℕ}
    {u E : ℝ} {ρ : ℂ} {done : Finset (Fin (P.cover j).cover.count)} {x : RunRecord d m}
    (h : TileSweepCore C P j n₀ u E ρ Cb done x) (θ : ℝ) (i : Torus d m)
    (hi : i ∉ x.endpoint.active) : sweepIncrement θ x.sweep i = 0 := by
  unfold sweepIncrement
  rw [Finset.sum_eq_zero, mul_zero]
  intro k hk
  rw [if_neg]
  intro hp
  have hk' := Finset.mem_range.mp hk
  have hl := (pivot_live h.wellFormed hk' hp).1
  have h0 := ((mem_live_iff h.wellFormed hk'.le ((i, false) : Port d m)).mp hl).1
  rw [h.start_live] at h0
  exact hi (Finset.mem_filter.mp h0).2

/-- **The physical identity after the sweep end** (02-state.tex:231–247): the committed `M`
records the swept increments and `installed` carries them. -/
theorem TileSweepCore.physical_end {C Cb : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ}
    {ρ : ℂ} {x : RunRecord d m} (h : TileSweepCore C P j n₀ u E ρ Cb Finset.univ x) :
    PhysicalIdentity E (sweepEndMapTheta (sweepTheta P.u m j) x) := by
  refine physicalIdentity_add E
    { x with installed := fun i => x.installed i - sweepIncrement (sweepTheta P.u m j) x.sweep i }
    (sweepEndMapTheta (sweepTheta P.u m j) x) (sweepIncrement (sweepTheta P.u m j) x.sweep)
    h.physical ?_ (sweepEndMapTheta_M _ x) ?_ ?_
  · show sweepEndActive x = x.endpoint.active
    exact h.sweepEndActive_eq
  · funext i; simp [sweepEndMapTheta]
  · exact fun i hi => h.sweepIncrement_inactive _ i hi

/-- The analytic sweep-end statement assumes stage bounds for the old endpoint,
the physical identity of the post-sweep record, and a pivot at every committed
step. The physical identity makes the Combes–Thomas estimate applicable. -/
def SweepEndStatement (d : ℕ) (C Cb CA cA cP CP cL CL C₀ : ℝ) : Prop :=
  ∃ t0 > 0, ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    PhysicalIdentity E (sweepEndMapTheta (sweepTheta P.u m j) x) →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    let sw := (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint
    SweepFacts Cb (stageScale u (j - 1) m) (stageScale u j m) x.endpoint sw x.r ∧
    IsDampedEndpoint sw x.r (stageScale u j m) ∧
    (∀ i i', ‖normalizedInverse sw (stageScale u j m) i i'‖ ≤
      CA / Real.sqrt (stageScale u j m) * Real.exp (-cA * stageScale u j m *
        max (physicalDistance d m i i' / 2 - stageScale u j m ^ (-1.03 : ℝ)) 0)) ∧
    (∀ f, cA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f ≤
        endpointEnergy sw x.r (stageScale u j m) f ∧
      endpointEnergy sw x.r (stageScale u j m) f ≤
        CA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f) ∧
    (∀ i, rowFour (normalizedInverse sw (stageScale u j m)) i ≤
      0.7 * stageScale u j m ^ (1 + delta)) ∧
    (∀ i ∈ sw.active, ‖sw.g i i - x.r i‖ ≤ CA * stageScale u j m ^ (0.42 * delta))

theorem endMap_endpoint (P : TilePlan d m) (j : ℕ) (x : RunRecord d m) :
    (endMap P j x).endpoint = (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint ∧
      (endMap P j x).r = x.r ∧ (endMap P j x).aborted = x.aborted := by
  unfold endMap
  split_ifs <;> simp [snapshotMap, sweepEndMapTheta]

/-- **(c) The sweep end hands the tile-phase invariant over to the clearing phase.** -/
theorem sweepEnd_keeps {C Cb CA cA cP CP cL CL C₀ : ℝ}
    (hend : SweepEndStatement d C Cb CA cA cP CP cL CL C₀) :
    ∃ t0 > 0, ∀ {m : ℕ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {PA : ℝ},
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → 1 ≤ n₀ → n₀ < j → j ≤ m → 2 ≤ m →
    1 ≤ CA → 0 < cA → 0 ≤ PA → sweepScale u m j < t0 →
    ∀ x : RunRecord d m, x ∈ TileSweepInv C P j n₀ u E ρ Cb Finset.univ →
    (x.aborted = false → ∀ i, cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA ∧ ‖x.r i‖ ≤ CA) →
    (x.aborted = false → StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r) →
    ClearPhase n₀ u E ρ Cb CA cA PA j (guardMap (endMap P j) x) := by
  obtain ⟨t0, ht0, hend⟩ := hend
  refine ⟨t0, ht0, ?_⟩
  intro m P j n₀ u E ρ PA hn hu' hu hn₀ hnj hj hm hCA hcA hPA hsmall x hx hdamp hSB hab
  have hab' : x.aborted = false := by
    unfold guardMap at hab; split_ifs at hab with h
    · exact absurd hab (by simp [h])
    · simpa [Bool.not_eq_true] using h
  have hg : guardMap (endMap P j) x = endMap P j x := by simp [guardMap, hab']
  have h := hx hab'
  obtain ⟨hsw, hdmp, hdec, hcmp, hrow, hlag⟩ :=
    hend m n₀ u E ρ P j x hn hu' hu hnj hj hsmall (hSB hab') h.physical_end h
  obtain ⟨he, hr, -⟩ := endMap_endpoint P j x
  refine ⟨ClearPhaseData.ofSweep' hu hn₀ hnj hj hm hCA hcA hPA x.endpoint _ x.r h.hist hsw
    (hdamp hab') hdmp hdec hcmp hrow hlag _ ?_ ?_⟩
  · rw [hg, he]
  · rw [hg, hr]

end AndersonAC.AgentS78

/-! ## The final residual sweep (`j = m + 1`): the final record -/

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The analytic end of the final residual sweep. After the last tile of the
final sweep (θ = 1/2, `t = t_m`, –41, 08:340–368), the committed endpoint after the sweep
end is a damped endpoint at `η = s_m` with the final-record bounds, and the physical identity
holds when it held for the input record and the run records the swept increments in
`endpoint.M`. -/
def FinalSweepStatement (d : ℕ) (C Cb Cr cp cg : ℝ) : Prop :=
  ∃ t0 > 0, ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ ≤ m →
    sweepScale u m (m + 1) < t0 →
    TileSweepCore C P (m + 1) n₀ u E ρ Cb Finset.univ x →
    let y := sweepEndMapTheta (sweepTheta P.u m (m + 1)) x
    IsDampedEndpoint y.endpoint y.r (OAI.Anderson.scaleHeight m u) ∧
    Fintype.card (Torus d m) ≤ 2 * y.endpoint.active.card ∧
    (∀ i ∈ y.endpoint.active, ‖y.r i‖ ≤ Cr ∧ cp ≤ (y.r i).im) ∧
    (∀ i ∈ y.endpoint.active, ‖y.endpoint.g i i - y.r i‖ ≤ cp - cg)

theorem endMap_final (P : TilePlan d m) (x : RunRecord d m) :
    endMap P (m + 1) x = sweepEndMapTheta (sweepTheta P.u m (m + 1)) x := by
  unfold endMap
  rw [if_neg (by omega)]
  rfl

/-- **The final record from the tile-phase invariant of the final sweep** (the physical
identity is proved here, `TileSweepCore.physical_end`; the rest is the contract). -/
theorem finalSweep_good {C Cb Cr cp cg : ℝ} (hfin : FinalSweepStatement d C Cb Cr cp cg) :
    ∃ t0 > 0, ∀ {m : ℕ} {P : TilePlan d m} {n₀ : ℕ} {u E : ℝ} {ρ : ℂ},
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ ≤ m →
    sweepScale u m (m + 1) < t0 →
    ∀ x : RunRecord d m, x ∈ TileSweepInv C P (m + 1) n₀ u E ρ Cb Finset.univ →
    (guardMap (endMap P (m + 1)) x).aborted = false →
    guardMap (endMap P (m + 1)) x ∈ FinalGood (d := d) (m := m) u E Cr cp cg := by
  obtain ⟨t0, ht0, hfin⟩ := hfin
  refine ⟨t0, ht0, ?_⟩
  intro m P n₀ u E ρ hn hu' hu hnm hsmall x hx hab
  have hab' : x.aborted = false := by
    unfold guardMap at hab; split_ifs at hab with h
    · exact absurd hab (by simp [h])
    · simpa [Bool.not_eq_true] using h
  have hg : guardMap (endMap P (m + 1)) x = endMap P (m + 1) x := by simp [guardMap, hab']
  rw [hg, endMap_final]
  obtain ⟨h1, h2, h3, h4⟩ := hfin m n₀ u E ρ P x hn hu' hu hnm hsmall (hx hab')
  exact ⟨(hx hab').physical_end, h1, h2, h3, h4⟩

end AndersonAC.AgentS78
