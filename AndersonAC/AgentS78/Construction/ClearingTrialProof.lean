import AndersonAC.AgentS78.Construction.ClearingTrialH

/-!
# proof of the clearing first-trial bound from its inputs

`clearingTrialH_of_inputs`: `ClearingTrialStatementH d (ClearingGood d cP CP qlag geo)` from
the uniform Proposition 6.6, the uniform drift contract, the blueprint concentration input,
the trial transport and the two clearing sub-contracts (geometry, residual law).
Part (a) is `AgentS6.trial_pivots_located` (06-clearing.tex:772–784) plus
`S78.localized_pivot_excludes_old_marks` with the per-core separation hypothesis
(07-assembly.tex:200–209); part (b) is Proposition 6.6 with `F₀ = ⊥` and
`t_j ≍ 4^{-j}` (`S78.stage_scale_comparison`).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

section Lemmas

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

open AndersonAC.S6

theorem TrialGeometryInput.mono_K {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    {q : StoppedTrial (Ω := Ω) core t r g0 order} {d : ℕ} {c K K' Cloc : ℝ}
    {dist : ι → ι → ℝ} {collapsed : ℕ → Ω → ι → ι → ℝ} {ell : ℝ}
    (h : TrialGeometryInput q d c K Cloc dist collapsed ell) (hK : K ≤ K') (ht : 0 < t) :
    TrialGeometryInput q d c K' Cloc dist collapsed ell where
  dist_nonneg := h.dist_nonneg
  dist_symm := h.dist_symm
  dist_triangle := h.dist_triangle
  dist_self := h.dist_self
  ell_lower := h.ell_lower
  ell_upper := h.ell_upper
  core_ball := h.core_ball
  shells := fun i n => (h.shells i n).trans
    (mul_le_mul_of_nonneg_right hK (pow_nonneg (by positivity) _))
  volume := fun i L hL => (h.volume i L hL).trans
    (mul_le_mul_of_nonneg_right hK (pow_nonneg (by linarith) _))
  metric := h.metric
  range_geometry := h.range_geometry
  resolvent_decay := fun k ω hk hp i j => (h.resolvent_decay k ω hk hp i j).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hK (Real.sqrt_nonneg t)) (Real.exp_pos _).le)

theorem distanceToCore_map {n : ℕ} (e : ι ≃ Fin n) (dist : ι → ι → ℝ) (core : Finset ι)
    (p : ι) :
    distanceToCore (fun a b => dist (e.symm a) (e.symm b)) (core.map e.toEmbedding) (e p) =
      distanceToCore dist core p := by
  unfold distanceToCore
  by_cases hc : core.Nonempty
  · have hc' : (core.map e.toEmbedding).Nonempty := hc.map
    rw [dif_pos hc', dif_pos hc, Finset.inf'_map]
    congr 1
    funext b
    simp
  · have hc' : ¬ (core.map e.toEmbedding).Nonempty := by
      rwa [Finset.map_nonempty]
    rw [dif_neg hc', dif_neg hc]

theorem exists_near_of_distanceToCore_lt {dist : ι → ι → ℝ} {core : Finset ι} {p : ι} {L : ℝ}
    (hcore : core.Nonempty) (h : distanceToCore dist core p < L) :
    ∃ y ∈ core, dist p y < L := by
  unfold distanceToCore at h
  rw [dif_pos hcore] at h
  obtain ⟨y, hy, hyeq⟩ := Finset.exists_mem_eq_inf' hcore (dist p)
  exact ⟨y, hy, hyeq ▸ h⟩

end Lemmas

theorem queryHistory_zero {Ω ι : Type} [MeasurableSpace Ω] [MeasurableSpace ι]
    (F0 : MeasurableSpace Ω) (pivot : ℕ → Ω → ι) (residual : ℕ → Ω → ℝ) :
    AndersonAC.S6.queryHistory F0 pivot residual 0 = F0 := by
  simp [AndersonAC.S6.queryHistory]

theorem nu_eq (d : ℕ) : AndersonAC.S78.nu d = AndersonAC.S6.nu d := by
  simp only [AndersonAC.S78.nu, AndersonAC.S6.nu, AndersonAC.S78.delta, AndersonAC.S6.delta]
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · have : (d : ℝ) ≠ 0 := by positivity
    field_simp

/-- The plain probability from an a.e. bound of the conditional probability given `⊥`. -/
theorem measure_le_of_condProb_bot {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) {b : ℝ}
    (h : ∀ᵐ ω ∂μ, AndersonAC.S6.conditionalProbability μ ⊥ A ω ≤ b) :
    μ A ≤ ENNReal.ofReal b := by
  obtain ⟨ω, hω⟩ := h.exists
  unfold AndersonAC.S6.conditionalProbability at hω
  rw [condExp_bot] at hω
  have hint : ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real A :=
    integral_indicator_one hA
  rw [hint] at hω
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ A)]
  exact ENNReal.ofReal_le_ofReal hω

/-- `exp(−t^{−κ}) ≤ birthBound (κ/2) j` for `0 < t ≤ 2·4^{−j}`, `j ≥ 1`. -/
theorem exp_le_birthBound_clr {κ t : ℝ} {j : ℕ} (hκ : 0 < κ) (hj : 1 ≤ j) (ht : 0 < t)
    (htj : t ≤ 2 / (4 : ℝ) ^ j) :
    Real.exp (-t ^ (-κ)) ≤ birthBound (κ / 2) j := by
  unfold birthBound
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
    rw [← mul_pow]; norm_num
  have h2j : (2 : ℝ) ≤ 2 ^ j := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have htle : t ≤ (2 ^ j : ℝ)⁻¹ := by
    refine htj.trans ?_
    rw [h4, div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ h2]
    nlinarith
  have hinv : (2 ^ j : ℝ) ≤ t⁻¹ := by
    rw [le_inv_comm₀ h2 ht]; exact htle
  have hlhs : (4 : ℝ) ^ (κ / 2 * (j : ℝ)) = ((2 : ℝ) ^ j) ^ κ := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have hrhs : t ^ (-κ) = (t⁻¹) ^ κ := by
    rw [Real.rpow_neg ht.le, Real.inv_rpow ht.le]
  rw [hlhs, hrhs]
  exact Real.rpow_le_rpow (by positivity) hinv hκ.le

/-- **clearing trial bound reduction.** The clearing first-trial bound (variant with the query-history
hypothesis) on `ClearingGood`, from the uniform Proposition 6.6, the uniform drift contract,
the blueprint concentration input, the trial transport and the geometry and residual
sub-contracts. -/
theorem clearingTrialH_of_inputs {d : ℕ} (hd : 3 ≤ d)
    (hprep : PreparationUniformStatement) (hdrift : LeverageDriftUniformStatement)
    (hconc : AndersonAC.Blueprint.ConcentrationInput) (hT : TrialReindexStatement)
    (cP CP : ℝ) (qlag : ℝ → ℝ) (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m))
    (hgeo : ClearingGeometryStatement d (ClearingGood d cP CP qlag geo) cP CP)
    (hres : ClearingResidualStatement d (ClearingGood d cP CP qlag geo)) :
    ClearingTrialStatementH d (ClearingGood d cP CP qlag geo) := by
  obtain ⟨c, K, Cloc, hc, hccP, hCPK, hK, hCloc, Ng, hgeoN⟩ := hgeo
  obtain ⟨Kr, Nr, hresN⟩ := hres
  set K₁ := max K Kr with hK₁def
  have hK₁ : 1 ≤ K₁ := hK.trans (le_max_left _ _)
  obtain ⟨cConc, hcConc, hvec⟩ := AndersonAC.AgentS6.vectorConcentrationBridge_proof hconc
  obtain ⟨ε, hε, hεpos, t1, ht1, hdr⟩ :=
    hdrift AndersonAC.Blueprint.Packages.ward d hd c K₁ Cloc hc hK₁ hCloc qlag hqlag
  obtain ⟨t2, ht2, hpr⟩ :=
    hprep d hd c K₁ Cloc cConc hc hK₁ hCloc hcConc qlag ε hqlag hε hεpos
  obtain ⟨t3, ht3, hloc⟩ :=
    AndersonAC.AgentS6.trial_pivots_located.{0} AndersonAC.Blueprint.Packages.ward d c K₁ Cloc hc
  set t0 := min t1 (min t2 t3) with ht0def
  have ht0 : 0 < t0 := lt_min ht1 (lt_min ht2 ht3)
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (half_pos ht0) (by norm_num : (1 / 4 : ℝ) < 1)
  have hκ := AndersonAC.AgentS6.clearingExponent_pos d hd
  refine ⟨AndersonAC.S6.clearingExponent d / 2, half_pos hκ, max (max Ng Nr) N₁, ?_⟩
  intro n₀ m hN hm u hu E j hj hsched M x hx B hB hBmem hBel hsep order q hhist hresid
  have hNg : Ng ≤ n₀ := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNr : Nr ≤ n₀ := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ j := ((le_max_right _ _).trans hN).trans hj.le
  have hj1 : 1 ≤ j := by omega
  have hjm : j ≤ m := (Nat.div_le_self m 2).trans' hsched
  obtain ⟨htlo, hthi⟩ := stage_scale_comparison u j m hu hjm
  have htpos : 0 < (stageScale u j m) := lt_of_le_of_lt (by positivity) htlo
  have htt0 : (stageScale u j m) < t0 := by
    refine lt_of_le_of_lt hthi ?_
    have h4 : (1 / 4 : ℝ) ^ j ≤ (1 / 4 : ℝ) ^ N₁ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hN₁
    have : 2 / (4 : ℝ) ^ j = 2 * (1 / 4 : ℝ) ^ j := by
      rw [div_eq_mul_inv, one_div, inv_pow]
    rw [this]
    linarith
  have htt1 : (stageScale u j m) < t1 := lt_of_lt_of_le htt0 (min_le_left _ _)
  have htt2 : (stageScale u j m) < t2 := lt_of_lt_of_le htt0 ((min_le_right _ _).trans (min_le_left _ _))
  have htt3 : (stageScale u j m) < t3 := lt_of_lt_of_le htt0 ((min_le_right _ _).trans (min_le_right _ _))
  have hxg : ClearingGoodAt cP CP qlag n₀ u j x := hx.1
  -- the local input of the trial on the active sites
  obtain ⟨collapsed, hG⟩ := hgeoN n₀ m hNg hm u hu E j hj hsched M x hx B hB hBmem hBel
    order q hhist hresid
  have hR := hresN n₀ m hNr hm u hu E j hj hsched M x hx B hB hBmem hBel hsep order q hhist hresid
  have hG' : TrialGeometryInput (truncTrial q) d c K Cloc
      (fun a b : ActiveSite x => physicalDistance d m a.val b.val) collapsed
      (inspectionRadius j) := hG.trunc
  have hL := trialLocalInput_of_split (hG'.mono_K (le_max_left K Kr) htpos) hR
    (le_max_right K Kr) htpos
  -- transport to `Fin (Fintype.card (ActiveSite x))`
  obtain ⟨e, -⟩ : ∃ _e : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)), True :=
    ⟨Fintype.equivFin _, trivial⟩
  obtain ⟨q', hh', hs', ho', -, hp', hL'⟩ := hT (Fintype.card (ActiveSite x)) e B (stageScale u j m) (fun _ i => x.r i) (fun _ => trialG0 x)
    order (truncTrial q)
  have hL'' := hL' (sourcesLaw (Torus d m) M) d c K₁ Cloc _ collapsed _ hL
  have hcard1 : 1 ≤ (B.map e.toEmbedding).card := by
    rw [Finset.card_map]; exact hB.card_pos
  have hcard2 : ((B.map e.toEmbedding).card : ℝ) ≤ AndersonAC.S6.coreCap d (stageScale u j m) := by
    rw [Finset.card_map]; unfold AndersonAC.S6.coreCap; rw [← nu_eq]; exact hBel
  have hbroad : ∀ ω : RandomSources (Torus d m) M,
      AndersonAC.S6.BroadBounds c K₁ (fun i : Fin (Fintype.card (ActiveSite x)) => x.r (e.symm i).val) := by
    intro _
    refine ⟨hc, fun i => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hxg.broad _ (e.symm i).property
    exact ⟨h1.trans (hCPK.trans (le_max_left _ _)), hccP.trans h2,
      h3.trans (hCPK.trans (le_max_left _ _))⟩
  have hfourth : ∀ (_ω : RandomSources (Torus d m) M) (i : Fin (Fintype.card (ActiveSite x))),
      AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse (stageScale u j m)
        ((trialG0 x).submatrix e.symm e.symm)) i ≤ (4 / 5) * AndersonAC.S6.fourthCap (stageScale u j m) := by
    intro _ i
    refine le_of_eq_of_le ?_ (hxg.fourth (e.symm i))
    simp only [AndersonAC.S6.fourthRow, AndersonAC.S6.scaledInverse, Matrix.smul_apply,
      Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm
      (fun a => ‖(Real.sqrt (stageScale u j m) : ℂ) • trialG0 x (e.symm i) a‖ ^ 4)
  have hlag : ∀ (_ω : RandomSources (Torus d m) M) (i : Fin (Fintype.card (ActiveSite x))),
      ‖(trialG0 x).submatrix e.symm e.symm i i - x.r (e.symm i).val‖ ≤
        qlag (stageScale u j m) * (stageScale u j m) ^ AndersonAC.S6.betaW :=
    fun _ i => hxg.lag _ (e.symm i).property
  have hdrift' := hdr (sourcesLaw (Torus d m) M) (Fintype.card (ActiveSite x)) (B.map e.toEmbedding) (stageScale u j m) _ _ _ q' _ _ _ htpos
    htt1 hcard1 hcard2 hbroad hfourth hlag hL''
  have hfail := hpr (sourcesLaw (Torus d m) M) (Fintype.card (ActiveSite x)) (B.map e.toEmbedding) (stageScale u j m) _ _ _ q' _ _ _ htpos
    htt2 hcard1 hcard2 hbroad hfourth hlag hL'' (hvec _ _ _) hdrift'
  have hloc' := hloc (sourcesLaw (Torus d m) M) (Fintype.card (ActiveSite x)) _ (stageScale u j m) _ _ _ q' _ _ _ htpos htt3 hbroad hL''
  refine ⟨fun k ω hk => ?_, ?_⟩
  · -- (a) location and non-pending
    have h1 := hloc' k ω (by rw [hs']; exact hk)
    rw [hp', distanceToCore_map e (fun a b : ActiveSite x => physicalDistance d m a.val b.val)] at h1
    obtain ⟨y, hyB, hy⟩ := exists_near_of_distanceToCore_lt hB h1
    have hnear : physicalDistance d m (q.pivot k ω).val y.val ≤ inspectionRadius j / 2 := hy.le
    refine ⟨fun hpend => ?_, y, hyB, hnear⟩
    obtain ⟨_, hnotcore, -⟩ := q.heat k ω hk
    have hnotB : (q.pivot k ω).val ∉ B.map (Function.Embedding.subtype _) := by
      rw [Finset.mem_map]
      rintro ⟨a, ha, hav⟩
      exact hnotcore (Subtype.val_injective hav ▸ ha)
    have hRl : inspectionRadius j < separationRadius j := by
      unfold inspectionRadius separationRadius
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    refine localized_pivot_excludes_old_marks (B.map (Function.Embedding.subtype _))
      (x.pending.filter (fun z => z ∉ B.map (Function.Embedding.subtype _))) _
      (separationRadius j) (inspectionRadius j) hRl
      ⟨y.val, Finset.mem_map_of_mem _ hyB, hnear⟩ ?_
      (Finset.mem_filter.mpr ⟨hpend, hnotB⟩)
    intro z hz y' hy'
    rw [Finset.mem_filter] at hz
    exact hsep z hz.1 hz.2 y' hy'
  · -- (b) the failure probability
    have ho'' : q'.outcome = q.outcome := ho'
    rw [← ho'']
    have hA : MeasurableSet {ω | q'.outcome ω = AndersonAC.S6.TrialOutcome.fail} :=
      q'.outcome_measurable
        (MeasurableSpace.measurableSet_top (s := {AndersonAC.S6.TrialOutcome.fail}))
    have h0 : q'.history 0 = ⊥ := by
      rw [hh']; show q.history 0 = ⊥; rw [hhist 0, queryHistory_zero]
    rw [h0] at hfail
    exact (measure_le_of_condProb_bot _ hA hfail).trans
      (ENNReal.ofReal_le_ofReal (exp_le_birthBound_clr hκ hj1 htpos hthi))

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.clearingTrialH_of_inputs
