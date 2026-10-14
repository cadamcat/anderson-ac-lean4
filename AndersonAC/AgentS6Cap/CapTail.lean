import AndersonAC.AgentS6Cap.RowStream
import AndersonAC.AgentS6Cap.LocalInput
import AndersonAC.AgentS6.CapReduction
import AndersonAC.AgentS6.RunningPrestate
import AndersonAC.AgentS6.TrialLocation
import AndersonAC.AgentS6.Frozen
import AndersonAC.AgentS6Row.Proof
import AndersonAC.S6.Statements

/-! Leverage-cap tail (06-clearing.tex:962–1056, 1060–1110).

Reduction (`capMode_rows`) to monitored rows, one varying-ridge stream per row
(`row_crossing_tail` with bias/jump from `leverage_one_row_estimates`,
bias sum from `row_bias_sum`, margin from `leverage_bias_margins`),
finite-union conditional bound, monitored cardinality (`monitored_card`)
absorbed by `poly_stretched_small` at `κ = clearingExponent d`. -/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory Topology

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

/-- Conditional probability of a finite union is at most the sum. -/
theorem condProb_finset_union_le_sum
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›)
    {ι : Type*} (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    ∀ᵐ ω ∂μ, conditionalProbability μ (F 0) (⋃ i ∈ s, E i) ω ≤
      ∑ i ∈ s, conditionalProbability μ (F 0) (E i) ω := by
  classical
  have hInt : ∀ {S : Set Ω}, MeasurableSet S →
      Integrable (S.indicator (fun _ => (1 : ℝ))) μ :=
    fun hS => (integrable_const (1 : ℝ)).indicator hS
  have hU : MeasurableSet (⋃ i ∈ s, E i) :=
    Finset.measurableSet_biUnion s (fun i him => hE i him)
  have hsum_int : Integrable (∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ))) μ :=
    integrable_finsetSum' s (fun i him => hInt (hE i him))
  have hle : (⋃ i ∈ s, E i).indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ]
      ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) := by
    refine Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ ⋃ i ∈ s, E i
    · rw [Set.indicator_of_mem hω]
      simp only [Set.mem_iUnion] at hω
      obtain ⟨i, him, hEi⟩ := hω
      have h1 : ((E i).indicator (fun _ => (1 : ℝ)) : Ω → ℝ) ω = 1 :=
        Set.indicator_of_mem hEi (fun _ => (1 : ℝ))
      have hnonneg : ∀ j ∈ s, 0 ≤ ((E j).indicator (fun _ => (1 : ℝ)) : Ω → ℝ) ω := by
        intro j _
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      calc (1 : ℝ) = ((E i).indicator (fun _ => (1 : ℝ)) : Ω → ℝ) ω := h1.symm
        _ ≤ ∑ j ∈ s, ((E j).indicator (fun _ => (1 : ℝ)) : Ω → ℝ) ω :=
          Finset.single_le_sum hnonneg him
        _ = ((∑ j ∈ s, (E j).indicator (fun _ => (1 : ℝ))) : Ω → ℝ) ω := by
          simp [Finset.sum_apply]
    · rw [Set.indicator_of_notMem hω]
      have hnonneg : 0 ≤ ((∑ j ∈ s, (E j).indicator (fun _ => (1 : ℝ))) : Ω → ℝ) ω := by
        rw [Finset.sum_apply]
        apply Finset.sum_nonneg
        intro j _
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      simpa using hnonneg
  have hmono := condExp_mono (m := F 0) (hInt hU) hsum_int hle
  have hadd := condExp_finsetSum (fun i him => hInt (hE i him)) (F 0)
  filter_upwards [hmono, hadd] with ω h1 h2
  show μ[(⋃ i ∈ s, E i).indicator (fun _ => (1 : ℝ)) | F 0] ω ≤
    ∑ i ∈ s, μ[(E i).indicator (fun _ => (1 : ℝ)) | F 0] ω
  have h2' : μ[∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) | F 0] ω =
      ∑ i ∈ s, μ[(E i).indicator (fun _ => (1 : ℝ)) | F 0] ω := by
    simpa [Finset.sum_apply] using h2
  calc μ[(⋃ i ∈ s, E i).indicator (fun _ => (1 : ℝ)) | F 0] ω ≤
        μ[∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) | F 0] ω := h1
    _ = ∑ i ∈ s, μ[(E i).indicator (fun _ => (1 : ℝ)) | F 0] ω := h2'

/-- Monitored cardinality as a polynomial in `t⁻¹`. -/
theorem monitored_card_poly
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
    {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    {q : StoppedTrial (Ω := Ω) core t r g0 order}
    {μ : Measure Ω} {d : ℕ} {c K Cloc : ℝ} {dist : Fin n → Fin n → ℝ}
    {collapsed : ℕ → Ω → Fin n → Fin n → ℝ} {ell : ℝ}
    (hin : TrialLocalInput q μ d c K Cloc dist collapsed ell)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc)
    (hcore : core.Nonempty) :
    ((Finset.univ.filter (fun i => distanceToCore dist core i < ell / 2)).card : ℝ) ≤
      (K * (3 : ℝ) ^ d) * t ^ (-((d : ℝ) * max Cloc 4)) := by
  classical
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hzpos : 0 < t ^ (-4 : ℤ) := zpow_pos ht _
  have hellpos : 0 < ell := lt_of_lt_of_le (by positivity : 0 < (1 / 256 : ℝ) * t ^ (-4 : ℤ)) hin.ell_lower
  have hR0 : 0 ≤ ell / 2 := by linarith [hellpos]
  have hsub : Finset.univ.filter (fun i => distanceToCore dist core i < ell / 2) ⊆
      Finset.univ.filter (fun i => distanceToCore dist core i ≤ ell / 2) := by
    intro i hi
    simpa using le_of_lt (Finset.mem_filter.mp hi).2
  have hcard_le : ((Finset.univ.filter
      (fun i => distanceToCore dist core i < ell / 2)).card : ℝ) ≤
      ((Finset.univ.filter
        (fun i => distanceToCore dist core i ≤ ell / 2)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hmon := monitored_card hin (ell / 2) hR0 hcore
  have hell_upper_rpow : ell / 2 ≤ t ^ (-4 : ℝ) := by
    have h1 : ell ≤ 2 * t ^ (-4 : ℤ) := hin.ell_upper
    have hcast : ((-4 : ℤ) : ℝ) = (-4 : ℝ) := by norm_num
    have h2 : (t ^ (-4 : ℤ) : ℝ) = t ^ ((-4 : ℤ) : ℝ) :=
      (Real.rpow_intCast t (-4)).symm
    rw [hcast] at h2
    linarith
  have hMCloc : Cloc ≤ max Cloc 4 := le_max_left _ _
  have hM4 : (4 : ℝ) ≤ max Cloc 4 := le_max_right _ _
  have h1_le : (1 : ℝ) ≤ t ^ (-max Cloc 4) := by
    have hneg : -max Cloc 4 ≤ 0 := by
      have : 0 ≤ max Cloc 4 := le_trans hCloc hMCloc
      linarith
    calc (1 : ℝ) = t ^ (0 : ℝ) := (Real.rpow_zero t).symm
      _ ≤ t ^ (-max Cloc 4) := rpow_anti ht ht1 hneg
  have hCloc_le : t ^ (-Cloc) ≤ t ^ (-max Cloc 4) :=
    rpow_anti ht ht1 (by linarith [hMCloc])
  have h4_le : t ^ (-4 : ℝ) ≤ t ^ (-max Cloc 4) :=
    rpow_anti ht ht1 (by linarith [hM4])
  have hell_le : ell / 2 ≤ t ^ (-max Cloc 4) :=
    hell_upper_rpow.trans h4_le
  have hsum_le : 1 + (t ^ (-Cloc) + ell / 2) ≤ 3 * t ^ (-max Cloc 4) := by
    linarith [h1_le, hCloc_le, hell_le]
  have hsum_nonneg : 0 ≤ 1 + (t ^ (-Cloc) + ell / 2) := by positivity
  have hbase_le : (1 + (t ^ (-Cloc) + ell / 2)) ^ d ≤ (3 * t ^ (-max Cloc 4)) ^ d :=
    pow_le_pow_left₀ hsum_nonneg hsum_le d
  have hpow_eq : (3 * t ^ (-max Cloc 4)) ^ d = (3 : ℝ) ^ d * t ^ (-((d : ℝ) * max Cloc 4)) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  calc ((Finset.univ.filter (fun i => distanceToCore dist core i < ell / 2)).card : ℝ)
      ≤ K * (1 + (t ^ (-Cloc) + ell / 2)) ^ d := hcard_le.trans hmon
    _ ≤ K * ((3 * t ^ (-max Cloc 4)) ^ d) := by gcongr
    _ = (K * (3 : ℝ) ^ d) * t ^ (-((d : ℝ) * max Cloc 4)) := by rw [hpow_eq]; ring

theorem capTail_proof : CapTailStatement := by
  intro Ω _ d hd c K Cloc cConc hc hK hCloc hConc μ _ qlag ε hqlag hε hεpos
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
    leverage_one_row_estimates d c K2 Cloc hc hK2 μ
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
  intro n core t r g0 order q dist collapsed ell htt hyp
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
  have hrow_all := hrow2 n core t r g0 order q dist collapsed ell ht htt_row
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

#print axioms AndersonAC.AgentS6.condProb_finset_union_le_sum
#print axioms AndersonAC.AgentS6.monitored_card_poly
#print axioms AndersonAC.AgentS6.capTail_proof
