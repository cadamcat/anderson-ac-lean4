import AndersonAC.S6.UniformTails

/-! Uniform-in-`(Ω, μ)` forms of the distortion-budget and leverage-cap tails. The bodies are
those of `AgentS6.budgetTail_proof` (AgentS6Budget/Final.lean) and `AgentS6.capTail_proof`
(AgentS6Cap/CapTail.lean): every threshold there comes from a lemma whose threshold is already
chosen before the space and measure, so only the binder order changes. -/

noncomputable section
open scoped BigOperators
open Filter Topology MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6
open AndersonAC.S6 AndersonAC.AgentS6Budget

set_option maxHeartbeats 2000000 in
/-- `budgetTail_proof` with the threshold chosen before the space and the measure: the same
proof, whose threshold selection never used them. -/
theorem budgetTailUniform_proof (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc) (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)) :
    UniformModeTailStatement d c K Cloc cConc qlag ε (fun {Ω} [_] => budgetMode (Ω := Ω)) := by
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
  intro Ω _ μ _ n core t r g0 order q dist collapsed ell htt hyp
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

/-- `capTail_proof` with the threshold chosen before the space and the measure; the single-row
constants come from `S6.leverageOneRowUniform_proof`. -/
theorem capTailUniform_proof (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc) (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)) :
    UniformModeTailStatement d c K Cloc cConc qlag ε (fun {Ω} [_] => capMode (Ω := Ω)) := by
  intro hWard
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKc : 0 < K / c := div_pos hKpos hc
  -- Widened damping constant for the running prestate (`3K+1`).
  let K2 : ℝ := 3 * K + 1
  have hK2 : 1 ≤ K2 := by dsimp [K2]; linarith
  have hKle : K ≤ K2 := by dsimp [K2]; linarith
  have hK2pos : 0 < K2 := lt_of_lt_of_le zero_lt_one hK2
  have hK2c : 0 < K2 / c := div_pos hK2pos hc
  obtain ⟨L2, t_row, hL2, ht_row, hrow2⟩ :=
    AndersonAC.S6.leverageOneRowUniform_proof d c K2 Cloc hc hK2
  obtain ⟨t_cap, ht_cap, hcap⟩ := capMode_rows hWard d c K Cloc hc
  obtain ⟨t_loc, ht_loc, hloc⟩ := trial_pivots_located hWard d c K Cloc hc
  obtain ⟨t_pre, ht_pre, hpre⟩ := trial_running_prestate K hK c qlag hqlag
  have hA0 : 0 ≤ (4 : ℝ) * (K2 / c) := by positivity
  have hbias_ev := row_bias_sum d hd L2 (4 * (K2 / c)) hL2.le hA0
  obtain ⟨-, hmargin_ev⟩ := leverage_bias_margins d hd
  let a_exp : ℝ := (27 / 100) * delta
  let kap : ℝ := clearingExponent d
  have hkap_pos : 0 < kap := clearingExponent_pos d hd
  have hkap_lt : kap < a_exp := by
    unfold kap clearingExponent a_exp eh e0 nu delta
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hnu_nn : 0 ≤ (1 / 100000 : ℝ) * (1 / 100) / (d : ℝ) := by positivity
    have hnu_le : (1 / 100000 : ℝ) * (1 / 100) / (d : ℝ) ≤ 1 / 30000000 := by
      rw [div_le_iff₀ (by positivity : 0 < (d : ℝ))]
      nlinarith
    linarith
  let c_per : ℝ := cConc * min (1 / (128 * L2 ^ 2 * (2 * (2 * (K2 / c)) + 1)))
    (1 / (8 * L2 * (2 * Real.sqrt (K2 / c) + 1)))
  have hc_per : 0 < c_per := by
    dsimp [c_per]
    apply mul_pos hConc
    apply lt_min
    · positivity
    · positivity
  let p_exp : ℝ := (d : ℝ) * max Cloc 4
  let A_union : ℝ := 4 * (K2 * (3 : ℝ) ^ d)
  have hA_union_nonneg : 0 ≤ A_union := by dsimp [A_union]; positivity
  have hpoly_ev := poly_stretched_small A_union p_exp c_per a_exp kap hc_per hkap_pos hkap_lt
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t < t_cap ∧ t < t_loc ∧ t < t_pre ∧ t < t_row ∧ t < 1 ∧
      (∀ (s : Finset ℕ) (v : ℕ → ℝ), (∀ k, 0 ≤ v k) →
        (s.card : ℝ) ≤ heatLimit t →
        ∑ k ∈ s, v k ^ 2 ≤ (4 * (K2 / c)) * t ^ a_exp →
        ∑ k ∈ s, oneRowBias d t L2 (v k) ≤ leverageScale t / 4) ∧
      ((heatLimit t : ℝ) * (leverageScale t) ^ 2 / t ≤ t ^ a_exp) ∧
      (A_union * t ^ (-p_exp) * Real.exp (-c_per * t ^ (-a_exp)) ≤
        (1 / 3) * Real.exp (-t ^ (-kap))) := by
    have hlt : ∀ a : ℝ, 0 < a → ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a := fun a ha =>
      nhdsWithin_le_nhds (Iio_mem_nhds ha)
    filter_upwards [hlt t_cap ht_cap, hlt t_loc ht_loc, hlt t_pre ht_pre,
      hlt t_row ht_row, hlt 1 one_pos, hbias_ev, hmargin_ev, hpoly_ev]
      with t h1 h2 h3 h4 h5 hb hm hp
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
    · intro s v hv hcard hS2
      simpa [a_exp] using hb s v hv hcard (by simpa [a_exp] using hS2)
    · simpa [a_exp] using hm
    · simpa [A_union, p_exp, c_per, a_exp, kap] using hp
  obtain ⟨t0, ht0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨t0, ht0, ?_⟩
  intro Ω _ μ _ n core t r g0 order q dist collapsed ell htt hyp
  have ht := hyp.t_pos
  obtain ⟨htt_cap, htt_loc, htt_pre, htt_row, htt1, hbias_small, hmargin, hpoly⟩ :=
    hsub ⟨ht, htt⟩
  have ht1 : t ≤ 1 := le_of_lt htt1
  have hcore : core.Nonempty := Finset.card_pos.mp (Nat.zero_lt_one.trans_le hyp.core_one)
  have hbroad2 : ∀ ω, BroadBounds c K2 (r ω) :=
    fun ω => broadBounds_mono_K c K K2 (r ω) (hyp.broad ω) hKle
  have hlocal2 : TrialLocalInput q μ d c K2 Cloc dist collapsed ell :=
    trialLocalInput_mono_K q hyp.local_input ht hKle
  have hpiv : ∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2 :=
    hloc μ n core t r g0 order q dist collapsed ell ht htt_loc hyp.broad hyp.local_input
  have hprestate : ∀ k ω, k < q.stop ω → HeatPrestate t K2
      (fun i : {i // i ∈ (q.state k ω).active} => r ω i)
      (trialInverse t (r ω) (q.state k ω)) :=
    fun k ω hk => hpre n core t r g0 order q ht htt_pre hyp.broad hyp.start_fourth hyp.start_lag k ω hk
  have hrow_all := hrow2 μ n core t r g0 order q dist collapsed ell ht htt_row
    hyp.core_cap hbroad2 hlocal2 hpiv hprestate
  let M : Finset (Fin n) := Finset.univ.filter (fun i => distanceToCore dist core i < ell / 2)
  let E : Fin n → Set Ω := fun i =>
    {ω | ∃ s : ℕ, s ≤ heatLimit t ∧ leverageScale t / 2 < |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i|}
  have hE_meas : ∀ i ∈ M, MeasurableSet (E i) := by
    intro i _
    exact rowCrossing_measurable q (heatLimit t) i
  have hrow_tail : ∀ i ∈ M, ∀ᵐ ω ∂μ,
      conditionalProbability μ (q.history 0) (E i) ω ≤
        4 * Real.exp (-c_per * t ^ (-a_exp)) := by
    intro i _
    have hrowBias : ∀ k, ∀ᵐ ω ∂μ, k < q.stop ω →
        |μ[(fun ω => recordedLeverageIncrement q k ω i) | q.history k] ω| ≤
          oneRowBias d t L2 ‖heatV q k ω i‖ := by
      intro k
      exact (hrow_all k i).1
    have hrowJump : ∀ k ω, k < q.stop ω →
        |recordedLeverageIncrement q k ω i| ≤ oneRowJump t L2 ‖heatV q k ω i‖ :=
      fun k ω hk => (hrow_all k i).2 ω hk
    have hstart : ∀ ω j, fourthRow (scaledInverse t (g0 ω)) j ≤ (4 / 5) * fourthCap t :=
      hyp.start_fourth
    exact row_crossing_tail q i d ht ht1 hc hK2 hL2 hConc hbroad2 hstart hyp.concentration
      hrowBias hrowJump hmargin hbias_small
  refine ⟨⋃ i ∈ M, E i, Finset.measurableSet_biUnion M (fun i hi => hE_meas i hi), ?_, ?_⟩
  · intro ω hcapω
    obtain ⟨i, hi, s, hs, hcross⟩ := hcap μ n core t r g0 order q dist collapsed ell ht htt_cap hyp.broad hyp.local_input ω hcapω
    have hiM : i ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have hEi : ω ∈ E i := by
      dsimp [E]
      exact ⟨s, hs, hcross⟩
    have hmem : ω ∈ ⋃ i ∈ M, E i := by
      simp only [Set.mem_iUnion]
      exact ⟨i, hiM, hEi⟩
    exact hmem
  · have htail_all : ∀ᵐ ω ∂μ, ∀ i ∈ M,
        conditionalProbability μ (q.history 0) (E i) ω ≤
          4 * Real.exp (-c_per * t ^ (-a_exp)) := by
      rw [eventually_all_finset]
      intro i hi
      exact hrow_tail i hi
    have hbound_nonneg : 0 ≤ (4 : ℝ) * Real.exp (-c_per * t ^ (-a_exp)) := by positivity
    have hcard_le : ((M.card : ℝ)) ≤ (K2 * (3 : ℝ) ^ d) * t ^ (-p_exp) := by
      have h := monitored_card_poly hlocal2 ht ht1 hK2 hCloc hcore
      simpa [M, p_exp] using h
    filter_upwards [condProb_finset_union_le_sum μ q.history M E hE_meas, htail_all] with ω hunion htail
    have hsum_le : ∑ i ∈ M, conditionalProbability μ (q.history 0) (E i) ω ≤
        (M.card : ℝ) * (4 * Real.exp (-c_per * t ^ (-a_exp))) := by
      have h := Finset.sum_le_card_nsmul M
        (fun i => conditionalProbability μ (q.history 0) (E i) ω)
        (4 * Real.exp (-c_per * t ^ (-a_exp))) (fun i hi => htail i hi)
      simpa [nsmul_eq_mul] using h
    have hprod_le : (M.card : ℝ) * (4 * Real.exp (-c_per * t ^ (-a_exp))) ≤
        A_union * t ^ (-p_exp) * Real.exp (-c_per * t ^ (-a_exp)) := by
      dsimp [A_union]
      have hcard' : (M.card : ℝ) ≤ (K2 * (3 : ℝ) ^ d) * t ^ (-p_exp) := hcard_le
      calc (M.card : ℝ) * (4 * Real.exp (-c_per * t ^ (-a_exp)))
          = ((M.card : ℝ)) * 4 * Real.exp (-c_per * t ^ (-a_exp)) := by ring
        _ ≤ (((K2 * (3 : ℝ) ^ d) * t ^ (-p_exp))) * 4 * Real.exp (-c_per * t ^ (-a_exp)) := by
          gcongr
        _ = 4 * (K2 * (3 : ℝ) ^ d) * t ^ (-p_exp) * Real.exp (-c_per * t ^ (-a_exp)) := by ring
    have htotal := hunion.trans (hsum_le.trans hprod_le)
    have htotal' := htotal.trans hpoly
    -- `kap` is definitionally `clearingExponent d`.
    simpa [kap] using htotal'

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.budgetTailUniform_proof
#print axioms AndersonAC.AgentS6.capTailUniform_proof
