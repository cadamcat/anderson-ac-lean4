import AndersonAC.S6.UniformStatements
import AndersonAC.AgentS6Row.Bias

noncomputable section
open Filter MeasureTheory ProbabilityTheory Topology Set

namespace AndersonAC.S6

open AndersonAC.AgentS6Row

/-- The constants in the single-row leverage estimate are independent of the probability space. -/
theorem leverageOneRowUniform_proof (d : ℕ) (c K Cloc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) : UniformLeverageOneRowStatement d c K Cloc := by
  have hK0 : 0 ≤ K := by linarith
  let LB := rowBiasConstant K c
  let LJ := jumpConstant K c
  let L := LB + LJ + 1
  have hLB : 0 < LB := rowBiasConstant_pos hK0 hc
  have hLJ : 0 ≤ LJ := jumpConstant_nonneg hK0 hc
  have hL : 0 < L := by dsimp [L]; linarith
  have hLBle : LB ≤ L := by dsimp [L]; linarith
  have hLJle : LJ ≤ L := by dsimp [L]; linarith
  obtain ⟨t0, ht0, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (row_scales_small d K c hK0 hc)
  refine ⟨L, t0, hL, ht0, ?_⟩
  intro Ω _ μ _ n core t r g0 order q dist collapsed ell ht htt hcard hr hlocal hloc hpre
    k i
  obtain ⟨hs, hvl, hfourth, hsθ, hvnsmall, hfrosmall⟩ := hsub ⟨ht, htt⟩
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hε : 0 ≤ epsilonScale d t := by unfold epsilonScale coreCap; positivity
  have hbias := recorded_bias_bound q μ d K c Cloc hK0 hc hs hsθ hvnsmall hfrosmall hcard
    dist collapsed ell hlocal hr hloc hpre k i
  refine ⟨?_, ?_⟩
  · filter_upwards [hbias] with ω hb hk
    refine (hb hk).trans ?_
    unfold oneRowBias
    have hterms : 0 ≤ Real.sqrt t * t ^ betaW * ‖heatV q k ω i‖ +
        ‖heatV q k ω i‖ ^ 2 + leverageScale t * epsilonScale d t +
        leverageScale t * ‖heatV q k ω i‖ / Real.sqrt t + (leverageScale t) ^ 2 / t := by
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLBle hl.le) hterms
  · intro ω hk
    have hξ := hlocal.residual_bound k ω hk (hloc k ω hk)
    have hjump := recorded_jump_bound q d K c hK0 hc hs hvl hfourth hvnsmall hfrosmall hcard
      k ω i hk (hr ω) (hpre k ω hk) hξ
    refine hjump.trans ?_
    unfold oneRowJump
    have hterms : 0 ≤ ‖heatV q k ω i‖ + leverageScale t / Real.sqrt t := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLJle hl.le) hterms

/-- The heat-limit tail has a threshold shared by all probability spaces. -/
theorem countTailUniform_of_heatCount
    (hHC : AndersonAC.SolS6.HeatCountStatement.{0})
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ) (qlag ε : ℝ → ℝ)
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    UniformModeTailStatement d c K Cloc cConc qlag ε
      (fun {Ω} [_] => AndersonAC.AgentS6.countMode (Ω := Ω)) := by
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ε t ≤ 1 / 20 ∧ (1 ≤ heatLimit t ∧
        2 * Real.exp (-Real.log 2 * (heatLimit t : ℝ) /
          (⌈10 * coreCap d t / leverageScale t⌉₊ : ℝ)) ≤
            (1 / 3) * Real.exp (-t ^ (-clearingExponent d))) := by
    filter_upwards [hε.eventually
        (Iic_mem_nhds (show (0 : ℝ) < 1 / 20 by norm_num)),
      AndersonAC.AgentS6.count_scalar d hd] with t h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨t0, ht0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  intro _
  refine ⟨t0, ht0, ?_⟩
  intro Ω _ μ _
  unfold ModeTailBelow
  intro n core t r g0 order q dist collapsed ell htt hyp
  obtain ⟨hεt, hN1, hscal⟩ := hsub ⟨hyp.t_pos, htt⟩
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos hyp.t_pos _
  have hrr : 0 < coreCap d t := Real.rpow_pos_of_pos hyp.t_pos _
  have hinput := AndersonAC.AgentS6.stoppedPotential q hyp (hεpos t) hεt
  have hσ : IsStoppingTime q.history
      (fun ω => (((fun _ : Ω => (0 : ℕ)) ω : ℕ) : WithTop ℕ)) :=
    isStoppingTime_const q.history 0
  have hcount := hHC Ω μ q.history (leverageScale t) (coreCap d t) (heatLimit t)
    q.stop (fun _ => 0) (AndersonAC.AgentS6.phi q (leverageScale t)) hl hrr hinput hσ
  have htail := hcount.2 (heatLimit t) hN1
  have hms : hσ.measurableSpace = q.history 0 := IsStoppingTime.measurableSpace_const _ _
  refine ⟨{ω | heatLimit t ≤ q.stop ω}, ?_, fun ω h => le_of_eq h.symm, ?_⟩
  · have hm := q.history.le (heatLimit t - 1) _ (q.stopping (heatLimit t - 1)).compl
    convert hm using 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro h h'
      have := (WithTop.coe_le_coe.mp h' : q.stop ω ≤ heatLimit t - 1)
      omega
    · intro h
      by_contra h''
      exact h (WithTop.coe_le_coe.mpr (show q.stop ω ≤ heatLimit t - 1 by omega))
  · rw [hms] at htail
    filter_upwards [htail] with ω hω
    simp only [Nat.sub_zero] at hω
    exact hω.trans hscal

/-- The heat-limit tail with the proved Lemma 6.5. -/
theorem countTailUniform_proof
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ) (qlag ε : ℝ → ℝ)
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    UniformModeTailStatement d c K Cloc cConc qlag ε
      (fun {Ω} [_] => AndersonAC.AgentS6.countMode (Ω := Ω)) :=
  countTailUniform_of_heatCount AndersonAC.SolS6.heatCount_proof d hd c K Cloc cConc qlag ε
    hε hεpos

end AndersonAC.S6
