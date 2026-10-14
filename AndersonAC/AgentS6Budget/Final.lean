import AndersonAC.AgentS6Budget.Compressed
import AndersonAC.AgentS6Budget.ExteriorSmall
import AndersonAC.AgentS6Budget.UnionSmall
import AndersonAC.AgentS6.Frozen

noncomputable section
open scoped BigOperators
open Filter Topology MeasureTheory

namespace AndersonAC.AgentS6
open AndersonAC.S6 AndersonAC.AgentS6Budget

set_option maxHeartbeats 2000000 in
theorem budgetTail_proof : BudgetTailStatement := by
  intro Ω _ d hd c K Cloc cConc hc hK hCloc hConc μ _ qlag ε hqlag _ _
  intro hWard
  let C := 3 * K + 1
  let L := 4 * C
  let W := C / c
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 < C := by linarith
  have hKC : K ≤ C := by dsimp [C]; linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  obtain ⟨b, hb, hcompressed⟩ := compressed_budget_event C c cConc hC hc hConc
  obtain ⟨tp, htp, hpre⟩ := trial_running_prestate K hK c qlag hqlag
  obtain ⟨tl, htl, hlocated⟩ := trial_pivots_located hWard d c K Cloc hc
  obtain ⟨Cf, cf, tf, hCf, hcf, htf, hfar⟩ := heatColumn_far_mass d c K hc hK
  have hbias := budget_bias_quarters C W
  have hexterior := exterior_numeric_small d K L W Cf cf (by linarith) hL.le hW.le hCf.le hcf
  have hunion := compressed_union_small d hd K Cloc (cConc * b) hK hCloc (mul_pos hConc hb)
  have hsmallC : 0 < 1 / (16 * C ^ 4) := by positivity
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t < tp ∧ t < tl ∧ t < tf ∧ t < 1 / 4 ∧ t < 1 / (16 * C ^ 4) ∧
      (80 * C ^ 5 * t ^ ((21 / 100) * delta) ≤ 1 / 4 ∧
        40 * C ^ 5 * Real.sqrt W * t ^ ((14 / 100) * delta) ≤ 1 / 4 ∧
        20 * C ^ 5 * W * t ^ ((135 / 1000) * delta) ≤ 1 / 4) ∧
      (heatLimit t : ℝ) * L * Real.sqrt
        (2 * (Cf * K ^ 3 / t * t ^ (-(d : ℝ)) * Real.exp (-cf * t ^ (-4 : ℤ))) * W) ≤
          Real.sqrt t * entryBudget t / 2 ∧
      (∀ q : ℝ, 0 ≤ q → q ≤ K * 5 ^ d * t ^ (-(d : ℝ) * (Cloc + 5)) →
        (8 * q ^ 2 + 2 * q + 2) * Real.exp (-(cConc * b) * t ^ (-budgetConcentrationExponent)) ≤
          (1 / 3) * Real.exp (-t ^ (-clearingExponent d))) := by
    have hlt : ∀ a : ℝ, 0 < a → ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a := fun a ha =>
      nhdsWithin_le_nhds (Iio_mem_nhds ha)
    filter_upwards [hlt tp htp, hlt tl htl,
      hlt tf htf, hlt (1 / 4) (by norm_num),
      hlt (1 / (16 * C ^ 4)) hsmallC, hbias, hexterior, hunion]
      with t hp hl hf ht4 hs hb he hu
    exact ⟨hp, hl, hf, ht4, hs, hb, he, hu⟩
  obtain ⟨t0, ht0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨t0, ht0, ?_⟩
  intro n core t r g0 order q dist collapsed ell htt hyp
  have ht := hyp.t_pos
  obtain ⟨httP, httL, httF, ht4, htC, ⟨hbe, hbr, hbf⟩, hext, huni⟩ := hsub ⟨ht, htt⟩
  have ht1 : t ≤ 1 := by linarith
  have hN : 1 ≤ heatLimit t := heatLimit_one_le ht (by linarith)
  have hsmall := small_of_t_le ht ht1 hC htC.le
  have hcore : core.Nonempty := Finset.card_pos.mp (Nat.zero_lt_one.trans_le hyp.core_one)
  have hr : ∀ ω i, c ≤ (r ω i).im := fun ω i => ((hyp.broad ω).2 i).2.1
  have hprestate := hpre n core t r g0 order q ht httP hyp.broad hyp.start_fourth hyp.start_lag
  have hpiv := hlocated μ n core t r g0 order q dist collapsed ell ht httL hyp.broad hyp.local_input
  let Q := monitoringRegion dist core t ell
  obtain ⟨G, hG, htests, hprob⟩ := hcompressed μ n core t r g0 order q d K Cloc dist collapsed ell Q
    ht ht1 hN hKC hsmall hr hyp.start_fourth hprestate hyp.local_input hpiv hyp.concentration hbe hbr hbf
  have hcoef := runningCoefficient_bounds μ q d c K Cloc C dist collapsed ell hyp.local_input
    hC hKC hsmall hprestate hpiv
  have hmass := heatColumn_square_sum_le q ht c C hc hC0.le hr hprestate
  have hfarall := hfar n core t r g0 order q μ Cloc dist collapsed ell ht ht4.le httF hcore hyp.local_input hpiv
  have htail : ∀ ω, ‖frobVector (scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) -
      compressMatrix Q (scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω)))‖ ≤
        Real.sqrt t * entryBudget t / 2 := by
    intro ω
    exact (cumulative_exterior_bound q ht ω (fun i => hc.trans_le (hr ω i)) Q L
      (Cf * K ^ 3 / t * t ^ (-(d : ℝ)) * Real.exp (-cf * t ^ (-4 : ℤ))) W
      hL.le (by positivity) hW.le (fun k => hcoef.1 k ω) (fun k => hmass k ω)
        (fun k => hfarall k ω)).trans hext
  have her := scaled_entry_le_row_threshold ht ht1
  have hrf := row_le_frobenius_threshold ht ht1 hN
  have hell : 0 ≤ ell := (by positivity : 0 ≤ (1 / 256 : ℝ) * t ^ (-4 : ℤ)).trans hyp.local_input.ell_lower
  have hcard : (Q.card : ℝ) ≤ K * 5 ^ d * t ^ (-(d : ℝ) * (Cloc + 5)) := by
    apply monitoring_card_polynomial d K Cloc (by linarith) hCloc ht ht1 hell hyp.local_input.ell_upper
    exact monitored_card hyp.local_input (ell / 2 + t ^ (-5 : ℤ) + 1) (by positivity) hcore
  refine ⟨G, hG, ?_, ?_⟩
  · intro ω hfail
    by_contra hnot
    obtain ⟨he, hr, hf⟩ := htests ω hnot
    exact hfail (budgetsHold_of_compression t ht (g0 ω) (q.state (q.stop ω) ω).hatG Q
      (Real.sqrt t * entryBudget t / 2) he hr hf (htail ω) le_rfl
      (div_le_div_of_nonneg_right her (by norm_num))
      (div_le_div_of_nonneg_right (her.trans hrf) (by norm_num)))
  · filter_upwards [hprob] with ω hω
    exact hω.trans (by
      simpa only [neg_mul, mul_assoc] using huni Q.card (Nat.cast_nonneg _) hcard)

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.budgetTail_proof
