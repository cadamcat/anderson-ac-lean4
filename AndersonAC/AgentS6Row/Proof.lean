import AndersonAC.AgentS6Row.Bias
import AndersonAC.S6.Statements

noncomputable section
open Filter MeasureTheory Topology

namespace AndersonAC.S6

open AndersonAC.AgentS6Row

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The single-row conditional bias and pathwise jump bounds of 06-clearing.tex:996–1018. -/
theorem leverage_one_row_estimates (d : ℕ) (c K Cloc : ℝ) (hc : 0 < c) (hK : 1 ≤ K)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Planned.leverage_one_row_estimates d c K Cloc hc hK μ := by
  have hK0 : 0 ≤ K := by linarith
  let LB := rowBiasConstant K c
  let LJ := jumpConstant K c
  let L := LB + LJ + 1
  have hLB : 0 < LB := rowBiasConstant_pos hK0 hc
  have hLJ : 0 ≤ LJ := jumpConstant_nonneg hK0 hc
  have hL : 0 < L := by dsimp [L]; linarith
  have hLBle : LB ≤ L := by dsimp [L]; linarith
  have hLJle : LJ ≤ L := by dsimp [L]; linarith
  obtain ⟨t0, ht0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (row_scales_small d K c hK0 hc)
  refine ⟨L, t0, hL, ht0, ?_⟩
  intro n core t r g0 order q dist collapsed ell ht htt hcard hr hlocal hloc hpre k i
  obtain ⟨hs, hvl, hfourth, hsθ, hvnsmall, hfrosmall⟩ := hsub ⟨ht, htt⟩
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hε : 0 ≤ epsilonScale d t := by unfold epsilonScale coreCap; positivity
  have hbias := recorded_bias_bound q μ d K c Cloc hK0 hc hs hsθ hvnsmall hfrosmall hcard
    dist collapsed ell hlocal hr hloc hpre k i
  refine ⟨?_, ?_⟩
  · filter_upwards [hbias] with ω hb hk
    refine (hb hk).trans ?_
    unfold oneRowBias
    have hterms : 0 ≤ Real.sqrt t * t ^ betaW * ‖heatV q k ω i‖ + ‖heatV q k ω i‖ ^ 2 +
        leverageScale t * epsilonScale d t + leverageScale t * ‖heatV q k ω i‖ / Real.sqrt t +
          (leverageScale t) ^ 2 / t := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLBle hl.le) hterms
  · intro ω hk
    have hξ := hlocal.residual_bound k ω hk (hloc k ω hk)
    have hjump := recorded_jump_bound q d K c hK0 hc hs hvl hfourth hvnsmall hfrosmall hcard
      k ω i hk (hr ω) (hpre k ω hk) hξ
    refine hjump.trans ?_
    unfold oneRowJump
    have hterms : 0 ≤ ‖heatV q k ω i‖ + leverageScale t / Real.sqrt t := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLJle hl.le) hterms

end AndersonAC.S6
