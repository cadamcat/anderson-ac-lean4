import AndersonAC.AgentS78.Construction.TilePhaseTrial
import AndersonAC.AgentS78.Construction.ResetBlock

/-!
# WP10 construction, tile phase (a): the invariant at the start of a sweep

agent-s78tphase (2026-10-14). The record entering the first tile block of the sweep into
stage `j` is `y = sweepStartMap θ_j t_j z` (inside `guardMap (stageMap P (j−1))`): the sweep
has length `0` and starts from the duplicated physical endpoint on the ports of the active
sites (04:67–80). `tileSweepInv_start` gives `TileSweepInv … ∅` for it from

* the stage history `BoundaryHist … (j − 1)` of `z` (handed over by the clearing phase /
  stage operation, agent-s78phase);
* `StageStartInputs`: the plan facts and the analytic duplicated stage-start clauses
  (04:73–88 Lemma `duplication`, 05:320–337) together with validity at `k = 0` — the
  analytic contract of part (a), stated separately (`TileStartStatement`);
* three run-level facts on unprocessed tiles (no terminal active site; at the final sweep no
  pending active site and consumed prefix `m − n₀`).

The structural clauses (length `0`, live set, well-formedness from the endpoint's support,
empty records) are proved here.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

section Start
variable (C : ℝ) (P : TilePlan d m) (j : ℕ)

/-- **Analytic stage-start inputs** of the sweep into stage `j` on its entering record. -/
structure StageStartInputs (y : RunRecord d m) : Prop where
  plan : PlanClauses C P j
  start : StartClauses C P j y.endpoint y.r (y.sweep.state 0)
  valid0 : y.sweep.valid (sweepScale P.u m j) (portR (sweepTheta P.u m j) y.r) (stageD0 P j y) 0

/-- The start lift is masked on its live set when the endpoint inverse vanishes off the active
set (`IsDampedEndpoint`, second clause). -/
theorem sweepStartLiveState_masked (θ : ℝ) (z : RunRecord d m)
    (hg : ∀ i k, i ∉ z.endpoint.active ∨ k ∉ z.endpoint.active → z.endpoint.g i k = 0) :
    (sweepStartLiveState θ z).g =
      S45.mask (sweepStartLiveState θ z).live (sweepStartLiveState θ z).g := by
  classical
  funext p q
  simp only [S45.mask, S45.pad, S45.restrict, Matrix.submatrix_apply]
  by_cases hp : p ∈ (sweepStartLiveState θ z).live <;>
    by_cases hq : q ∈ (sweepStartLiveState θ z).live
  · simp [hp, hq]
  · simp only [hp, hq, dite_true, dite_false]
    have hq' : q.1 ∉ z.endpoint.active := by
      simpa [sweepStartLiveState] using hq
    simp [sweepStartLiveState, S45.PortMap.liftState]
    exact Or.inr (hg _ _ (Or.inr hq'))
  · simp only [hp, dite_false]
    have hp' : p.1 ∉ z.endpoint.active := by
      simpa [sweepStartLiveState] using hp
    simp [sweepStartLiveState, S45.PortMap.liftState]
    exact Or.inr (hg _ _ (Or.inl hp'))
  · simp only [hp, dite_false]
    have hp' : p.1 ∉ z.endpoint.active := by
      simpa [sweepStartLiveState] using hp
    simp [sweepStartLiveState, S45.PortMap.liftState]
    exact Or.inr (hg _ _ (Or.inl hp'))

/-- **(a) The tile-phase invariant at the start of the sweep into stage `j`.** -/
theorem tileSweepInv_start {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ} (t : ℝ) (z : RunRecord d m)
    (hab : z.aborted = false)
    (hist : BoundaryHist n₀ u E ρ Cb (j - 1) z.endpoint z.r)
    (hg : ∀ i k, i ∉ z.endpoint.active ∨ k ∉ z.endpoint.active → z.endpoint.g i k = 0)
    (hin : StageStartInputs C P j (sweepStartMap (sweepTheta P.u m j) t z))
    (hphys : PhysicalIdentity E z)
    (hterm : ∀ i ∈ z.endpoint.active, i ∉ z.terminal)
    (hpend : IsFinalSweep m j → ∀ i ∈ z.endpoint.active, i ∉ z.pending)
    (hpref : IsFinalSweep m j → ∀ i ∈ z.endpoint.active, z.prefixLength i = m - P.n₀) :
    TileSweepCore C P j n₀ u E ρ Cb ∅ (sweepStartMap (sweepTheta P.u m j) t z) := by
  classical
  have hlen : (sweepStartMap (sweepTheta P.u m j) t z).sweep.length = 0 := rfl
  refine
    { hist := hist
      plan := hin.plan
      start := hin.start
      start_live := rfl
      start_lift := rfl
      wellFormed := ⟨fun k _ => sweepStartLiveState_masked _ z hg, fun k hk => absurd hk (by
        rw [hlen]; exact Nat.not_lt_zero k)⟩
      valid := fun k hk => by
        rw [hlen] at hk
        rw [Nat.le_zero.mp hk]; exact hin.valid0
      bit_pivots := fun k hk => absurd hk (by rw [hlen]; exact Nat.not_lt_zero k)
      scalar_bound := fun k hk => absurd hk (by rw [hlen]; exact Nat.not_lt_zero k)
      pivots_some := fun k hk => absurd hk (by rw [hlen]; exact Nat.not_lt_zero k)
      physical := physicalIdentity_congr (a := z) rfl
        (by funext i; simp only [sweepStartMap]; rw [sweepIncrement_of_length_zero _ _ rfl, sub_zero])
        hphys
      blocks := ?_
      done_deleted := fun S hS => absurd hS (Finset.notMem_empty S)
      undone_nonterminal := fun S _ i _ hi => hterm i hi
      final_no_pending := fun hf S _ i _ hi => hpend hf i hi
      final_prefix := fun hf S _ i _ hi => hpref hf i hi }
  refine ⟨fun _ => ∅, fun k hk => absurd hk (by rw [hlen]; exact Nat.not_lt_zero k),
    fun _ => Finset.empty_subset _, fun k hk => absurd hk (by rw [hlen]; exact Nat.not_lt_zero k),
    fun _ _ => rfl, fun S => ?_⟩
  simp only [S45.Sequence.Jrecord, S45.Sequence.Lrecord, S45.Sequence.lagRecord,
    S45.Sequence.rowRecord, Finset.sum_empty]
  exact localBudget_zero _ S (hin.plan.cover_b.1.le.trans hin.plan.cover_b.2)

end Start

end AndersonAC.AgentS78

/-! ## (c), structural part: after the last tile only the reserve ports of active sites live -/

namespace AndersonAC.AgentS78

variable {d m : ℕ}

/-- **Sweep end, live set.** When every tile is processed, the final live set of the
committed prefix is the set of reserve ports of the active sites (the hypothesis
`(q.state q.length).live = reserves` of `ordinary_sweep_endpoint`, before the transport to the
active sites). -/
theorem TileSweepCore.live_end {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ}
    {Cb : ℝ} {x : RunRecord d m} (h : TileSweepCore C P j n₀ u E ρ Cb Finset.univ x)
    (p : Port d m) :
    p ∈ (x.sweep.state x.sweep.length).live ↔ p.1 ∈ x.endpoint.active ∧ p.2 = true := by
  classical
  have hst : p ∈ (x.sweep.state 0).live ↔ p.1 ∈ x.endpoint.active := by
    rw [h.start_live]; simp [liveStart]
  by_cases hb : p.2 = true
  · rw [mem_live_iff h.wellFormed le_rfl p, hst]
    refine ⟨fun h' => ⟨h'.1, hb⟩, fun h' => ⟨h'.1, fun l hl hp => ?_⟩⟩
    have := h.bit_pivots l hl p hp
    rw [hb] at this; exact Bool.noConfusion this
  · have hb' : p.2 = false := by simpa using hb
    refine ⟨fun hlive => ?_, fun h' => absurd h'.2 hb⟩
    exfalso
    have hi : p.1 ∈ x.endpoint.active := hst.mp ((mem_live_iff h.wellFormed le_rfl p).mp hlive).1
    obtain ⟨S, hS, -⟩ := (P.cover j).cover.cover ((p.1, false) : Port d m)
    have hpe : ((p.1, false) : Port d m) = p := Prod.ext rfl hb'.symm
    exact h.done_deleted S (Finset.mem_univ S) p.1 (mem_tileSites.mpr hS) hi (hpe ▸ hlive)

end AndersonAC.AgentS78

