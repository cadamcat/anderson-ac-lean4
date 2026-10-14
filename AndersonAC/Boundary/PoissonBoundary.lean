import AndersonAC.Boundary.Poisson

/-!
# Poisson kernel layer-cake identity

The Poisson kernel is an integral of its radial derivative. This identity will turn the Poisson
transform into an average of centered ball densities, where Vitali differentiation applies.
-/

open MeasureTheory Filter
open scoped Topology

namespace AndersonAC.Boundary

private noncomputable def poissonLayerWeight (y r : ℝ) : ℝ :=
  2 * y * r / ((r ^ 2 + y ^ 2) ^ 2)

private noncomputable def poissonLayerPrimitive (y r : ℝ) : ℝ :=
  -y * (r ^ 2 + y ^ 2)⁻¹

private noncomputable def poissonCorrection (u : ℝ) : ℝ :=
  u / (1 + u ^ 2)

private noncomputable def poissonCorrectionDerivative (u : ℝ) : ℝ :=
  (1 - u ^ 2) / ((1 + u ^ 2) ^ 2)

/-- The symmetric ball density at radius `r`, with value zero outside positive radii. -/
noncomputable def symmetricBallDensity (μ : Measure ℝ) (x r : ℝ) : ℝ :=
  if 0 < r then μ.real (Metric.closedBall x r) / (2 * r) else 0

/-- The integrable profile produced by rescaling the radial Poisson layer weight. -/
noncomputable def poissonLayerProfile (u : ℝ) : ℝ :=
  4 * u ^ 2 / ((1 + u ^ 2) ^ 2)

/-- The symmetric ball density is measurable as a function of its radius. -/
theorem measurable_symmetricBallDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Measurable (symmetricBallDensity μ x) := by
  have hmassMon : Monotone (fun r : ℝ => μ.real (Metric.closedBall x r)) := by
    intro r s hrs
    exact measureReal_mono (Metric.closedBall_subset_closedBall hrs)
  have hmassMeas : Measurable (fun r : ℝ => μ.real (Metric.closedBall x r)) :=
    hmassMon.measurable
  have hden : Measurable (fun r : ℝ => 2 * r) := by fun_prop
  unfold symmetricBallDensity
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (hmassMeas.div hden) measurable_const

/-- At Lebesgue-a.e. point, the symmetric ball density converges to the RN density. -/
theorem ae_tendsto_symmetricBallDensity (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Filter.Tendsto (symmetricBallDensity μ x)
        (𝓝[>] 0) (𝓝 ((μ.rnDeriv volume x).toReal)) := by
  have hratio := Besicovitch.ae_tendsto_rnDeriv μ (volume : Measure ℝ)
  have hfinite : ∀ᵐ x ∂(volume : Measure ℝ), μ.rnDeriv volume x ≠ ⊤ :=
    Measure.rnDeriv_ne_top μ volume
  filter_upwards [hratio, hfinite] with x hx htop
  have hreal : Filter.Tendsto
      (fun r : ℝ => (μ (Metric.closedBall x r) /
        volume (Metric.closedBall x r)).toReal)
      (𝓝[>] 0) (𝓝 ((μ.rnDeriv volume x).toReal)) := by
    exact (ENNReal.tendsto_toReal htop).comp hx
  have heq : (fun r : ℝ => (μ (Metric.closedBall x r) /
      volume (Metric.closedBall x r)).toReal) =ᶠ[𝓝[>] 0]
      symmetricBallDensity μ x := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : 0 < r := Set.mem_Ioi.mp hr
    simp [symmetricBallDensity, hrpos, Measure.real_def, ENNReal.toReal_div]
    rw [ENNReal.toReal_ofReal (le_of_lt hrpos)]
  exact Filter.Tendsto.congr' heq hreal

private theorem symmetricBallDensity_bounded_of_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x d : ℝ)
    (hlim : Filter.Tendsto (symmetricBallDensity μ x) (𝓝[>] 0) (𝓝 d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖symmetricBallDensity μ x r‖ ≤ C := by
  have hlt : d < |d| + 1 := by linarith [le_abs_self d]
  have hnear : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      symmetricBallDensity μ x r < |d| + 1 :=
    hlim.eventually (Iio_mem_nhds hlt)
  obtain ⟨δ, hδ, hδsmall⟩ :=
    (nhdsGT_basis_of_exists_gt (a := (0 : ℝ)) ⟨1, by norm_num⟩).mem_iff.mp hnear
  let C : ℝ := max (|d| + 1) (μ.real Set.univ / (2 * δ))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro r
  by_cases hr : 0 < r
  · have hDnonneg : 0 ≤ symmetricBallDensity μ x r := by
      simp [symmetricBallDensity, hr]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hDnonneg]
    by_cases hrδ : r < δ
    · have hsmall : symmetricBallDensity μ x r < |d| + 1 :=
        hδsmall ⟨hr, hrδ⟩
      have hC1 : |d| + 1 ≤ C := by simp [C]
      exact hsmall.le.trans hC1
    · have hδr : δ ≤ r := le_of_not_gt hrδ
      have hmass : μ.real (Metric.closedBall x r) ≤ μ.real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      have hratio : symmetricBallDensity μ x r ≤ μ.real Set.univ / (2 * δ) := by
        simp only [symmetricBallDensity, if_pos hr]
        calc
          μ.real (Metric.closedBall x r) / (2 * r) ≤
              μ.real Set.univ / (2 * r) :=
            div_le_div_of_nonneg_right hmass (by positivity)
          _ ≤ μ.real Set.univ / (2 * δ) :=
            div_le_div_of_nonneg_left ENNReal.toReal_nonneg (by positivity) (by nlinarith)
      have hC2 : μ.real Set.univ / (2 * δ) ≤ C := by simp [C]
      exact hratio.trans hC2
  · have hzero : symmetricBallDensity μ x r = 0 := by
      simp [symmetricBallDensity, hr]
    rw [hzero, norm_zero]
    exact hC

private theorem hasDerivAt_poissonLayerPrimitive {y r : ℝ} (hy : 0 < y) :
    HasDerivAt (poissonLayerPrimitive y) (poissonLayerWeight y r) r := by
  have hpow : HasDerivAt (fun u : ℝ => u ^ 2 + y ^ 2) (2 * r) r := by
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * r) r := by
      convert (hasDerivAt_id r).pow 2 using 1
      · funext u
        simp [id]
      · simp [id]
    simpa using hsq.const_add (y ^ 2)
  have hden : r ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hinv := (hasDerivAt_inv hden).comp r hpow
  convert hinv.const_mul (-y) using 1
  · funext u
    dsimp [poissonLayerPrimitive]
  · simp [poissonLayerWeight]
    field_simp

private theorem poissonLayerPrimitive_tendsto {y : ℝ} :
    Filter.Tendsto (poissonLayerPrimitive y) atTop (𝓝 0) := by
  have hden_tendsto : Filter.Tendsto (fun r : ℝ => r ^ 2 + y ^ 2) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall fun r => le_add_of_nonneg_right (sq_nonneg y))
    exact Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  convert Filter.Tendsto.const_div_atTop hden_tendsto (-y) using 1
  funext r
  simp [poissonLayerPrimitive, div_eq_mul_inv]

private theorem poissonLayerWeight_nonneg {y r : ℝ} (hy : 0 < y) (hr : 0 ≤ r) :
    0 ≤ poissonLayerWeight y r := by
  dsimp [poissonLayerWeight]
  positivity

private theorem hasDerivAt_poissonCorrection {u : ℝ} :
    HasDerivAt poissonCorrection (poissonCorrectionDerivative u) u := by
  have hden : 1 + u ^ 2 ≠ 0 := by positivity
  have hsq : HasDerivAt (fun v : ℝ => 1 + v ^ 2) (2 * u) u := by
    have hpow : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
      convert (hasDerivAt_id u).pow 2 using 1
      · funext v
        simp [id]
      · simp [id]
    simpa using hpow.const_add 1
  convert (hasDerivAt_id u).div hsq hden using 1
  · funext v
    simp [poissonCorrection]
  · simp [poissonCorrectionDerivative]
    field_simp
    ring

private theorem poissonCorrection_tendsto :
    Filter.Tendsto poissonCorrection atTop (𝓝 0) := by
  have hden : Filter.Tendsto (fun u : ℝ => u + u⁻¹) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact le_add_of_nonneg_right (inv_nonneg.mpr hu.le)
  have hsmall : Filter.Tendsto (fun u : ℝ => (u + u⁻¹)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have heq : (fun u : ℝ => (u + u⁻¹)⁻¹) =ᶠ[atTop] poissonCorrection := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    dsimp [poissonCorrection]
    field_simp [ne_of_gt hu]
    ring
  exact Filter.Tendsto.congr' heq hsmall

private theorem integrableOn_poissonCorrectionDerivative :
    IntegrableOn poissonCorrectionDerivative (Set.Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun u : ℝ => (1 + u ^ 2)⁻¹) (Set.Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hmeas : Measurable poissonCorrectionDerivative := by
    unfold poissonCorrectionDerivative
    exact Measurable.div (by fun_prop) (by fun_prop)
  apply hbase.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := Set.mem_Ioi.mp hu
  have hden : 0 < 1 + u ^ 2 := by positivity
  have hnum : |1 - u ^ 2| ≤ 1 + u ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg u]
  have hnorm : ‖poissonCorrectionDerivative u‖ = |1 - u ^ 2| / (1 + u ^ 2) ^ 2 := by
    simp [poissonCorrectionDerivative, Real.norm_eq_abs]
  rw [hnorm]
  calc
    |1 - u ^ 2| / (1 + u ^ 2) ^ 2 ≤ (1 + u ^ 2) / (1 + u ^ 2) ^ 2 := by
      exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = (1 + u ^ 2)⁻¹ := by field_simp [ne_of_gt hden]

/-- The rescaled Poisson layer profile is integrable on the real line. -/
theorem integrable_poissonLayerProfile : Integrable poissonLayerProfile volume := by
  have hbase : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) volume := integrable_inv_one_add_sq
  have hmajor : Integrable (fun u : ℝ => 4 * (1 + u ^ 2)⁻¹) volume := hbase.const_mul 4
  have hmeas : Measurable poissonLayerProfile := by
    unfold poissonLayerProfile
    exact Measurable.div (by fun_prop) (by fun_prop)
  apply hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with u
  have hnonneg : 0 ≤ poissonLayerProfile u := by
    unfold poissonLayerProfile
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  change 4 * u ^ 2 / (1 + u ^ 2) ^ 2 ≤ 4 * (1 + u ^ 2)⁻¹
  have hden : 0 < 1 + u ^ 2 := by positivity
  have hineq : 4 * u ^ 2 / (1 + u ^ 2) ^ 2 ≤ 4 / (1 + u ^ 2) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hden) hden]
    nlinarith [sq_nonneg u]
  simpa [div_eq_mul_inv] using hineq

/-- The rescaled Poisson layer profile has total mass `π` on the positive half-line. -/
theorem integral_poissonLayerProfile :
    ∫ u in Set.Ioi (0 : ℝ), poissonLayerProfile u = Real.pi := by
  have hrel : ∀ u : ℝ,
      poissonLayerProfile u = 2 * (1 + u ^ 2)⁻¹ - 2 * poissonCorrectionDerivative u := by
    intro u
    dsimp [poissonLayerProfile, poissonCorrectionDerivative]
    have hden : 1 + u ^ 2 ≠ 0 := by positivity
    field_simp [hden]
    ring
  have hqInt : ∫ u in Set.Ioi (0 : ℝ), poissonCorrectionDerivative u = 0 := by
    have hderiv : ∀ u ∈ Set.Ici (0 : ℝ),
        HasDerivAt poissonCorrection (poissonCorrectionDerivative u) u := by
      intro u _
      exact hasDerivAt_poissonCorrection
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      integrableOn_poissonCorrectionDerivative poissonCorrection_tendsto]
    simp [poissonCorrection]
  calc
    ∫ u in Set.Ioi (0 : ℝ), poissonLayerProfile u =
        ∫ u in Set.Ioi 0, (2 * (1 + u ^ 2)⁻¹ - 2 * poissonCorrectionDerivative u) := by
          apply integral_congr_ae
          exact ae_of_all _ hrel
    _ = 2 * (∫ u in Set.Ioi (0 : ℝ), (1 + u ^ 2)⁻¹) -
          2 * (∫ u in Set.Ioi (0 : ℝ), poissonCorrectionDerivative u) := by
        rw [integral_sub (integrable_inv_one_add_sq.integrableOn.const_mul 2)
          (integrableOn_poissonCorrectionDerivative.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ = Real.pi := by
      rw [hqInt, integral_Ioi_inv_one_add_sq]
      simp [Real.arctan_zero]
      ring

/-- The radial derivative of the Poisson kernel is integrable on the positive half-line. -/
theorem integrableOn_poissonLayerWeight (y : ℝ) (hy : 0 < y) :
    IntegrableOn (poissonLayerWeight y) (Set.Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun r _ => hasDerivAt_poissonLayerPrimitive hy)
    (fun r hr => poissonLayerWeight_nonneg hy hr.le)
    poissonLayerPrimitive_tendsto

/-- The radial derivative integrates to the Poisson kernel tail. -/
theorem integral_poissonLayerWeight {y s : ℝ} (hy : 0 < y) (hs : 0 ≤ s) :
    ∫ r in Set.Ioi s, poissonLayerWeight y r = y / (s ^ 2 + y ^ 2) := by
  have hderiv : ∀ r ∈ Set.Ici s,
      HasDerivAt (poissonLayerPrimitive y) (poissonLayerWeight y r) r := by
    intro r _
    exact hasDerivAt_poissonLayerPrimitive hy
  have hweight_nonneg : ∀ r ∈ Set.Ioi s, 0 ≤ poissonLayerWeight y r := by
    intro r hr
    exact poissonLayerWeight_nonneg hy (le_trans hs hr.le)
  have hI := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hweight_nonneg
    poissonLayerPrimitive_tendsto
  rw [hI]
  dsimp [poissonLayerPrimitive]
  field_simp
  ring

private theorem integral_poissonLayerWeight_cutoff {y s : ℝ} (hy : 0 < y) (hs : 0 ≤ s) :
    ∫ r in Set.Ioi (0 : ℝ),
      (if s ≤ r then poissonLayerWeight y r else 0) = y / (s ^ 2 + y ^ 2) := by
  have heq : (fun r : ℝ => if s ≤ r then poissonLayerWeight y r else 0) =
      Set.indicator (Set.Ici s) (poissonLayerWeight y) := by
    funext r
    simp [Set.indicator]
  rw [heq, ← integral_indicator measurableSet_Ioi, Set.indicator_indicator,
    integral_indicator (measurableSet_Ioi.inter measurableSet_Ici)]
  by_cases hs0 : s = 0
  · subst s
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici 0 = Set.Ioi 0 := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · rintro ⟨hr, _⟩
        exact hr
      · intro hr
        exact ⟨hr, le_of_lt hr⟩
    rw [hset]
    exact integral_poissonLayerWeight hy le_rfl
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici s = Set.Ici s := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · rintro ⟨_, hrs⟩
        exact hrs
      · intro hrs
        exact ⟨lt_of_lt_of_le hspos hrs, hrs⟩
    rw [hset, integral_Ici_eq_integral_Ioi]
    exact integral_poissonLayerWeight hy hs

/-- Layer-cake form of the Poisson transform as an integral of centered ball masses. -/
theorem poissonTransform_eq_ballLayerIntegral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x y : ℝ) (hy : 0 < y) :
    poissonTransform μ x y =
      ∫ r in Set.Ioi (0 : ℝ),
        μ.real (Metric.closedBall x r) * poissonLayerWeight y r := by
  classical
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ × ℝ → ℝ := fun p =>
    if dist p.1 x ≤ p.2 then poissonLayerWeight y p.2 else 0
  have hweight : Integrable (poissonLayerWeight y) ν := by
    change Integrable (poissonLayerWeight y) (volume.restrict (Set.Ioi (0 : ℝ)))
    exact integrableOn_poissonLayerWeight y hy
  have hweightNorm : Integrable (fun r => ‖poissonLayerWeight y r‖) ν := hweight.norm
  have hweightProd : Integrable (fun p : ℝ × ℝ => ‖poissonLayerWeight y p.2‖) (μ.prod ν) :=
    hweightNorm.comp_snd μ
  have hweightMeas : Measurable (poissonLayerWeight y) := by
    unfold poissonLayerWeight
    fun_prop
  have hFmeas : Measurable F := by
    dsimp [F]
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_snd)
      (hweightMeas.comp measurable_snd) measurable_const
  have hFsm : AEStronglyMeasurable F (μ.prod ν) := hFmeas.aestronglyMeasurable
  have hFbound : ∀ᵐ p ∂(μ.prod ν), ‖F p‖ ≤ ‖poissonLayerWeight y p.2‖ := by
    filter_upwards with p
    by_cases hp : dist p.1 x ≤ p.2
    · simp [F, hp]
    · simp [F, hp]
  have hFint : Integrable F (μ.prod ν) := hweightProd.mono' hFsm hFbound
  have hinner : ∀ t : ℝ, ∫ r, F (t, r) ∂ν = poissonKernel x y t := by
    intro t
    let s : ℝ := |t - x|
    have hs : 0 ≤ s := abs_nonneg _
    have hcongr : ∀ r : ℝ,
        F (t, r) = (if s ≤ r then poissonLayerWeight y r else 0) := by
      intro r
      simp [F, s, Real.dist_eq]
    calc
      ∫ r, F (t, r) ∂ν = ∫ r, (if s ≤ r then poissonLayerWeight y r else 0) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ hcongr
      _ = ∫ r in Set.Ioi (0 : ℝ),
          (if s ≤ r then poissonLayerWeight y r else 0) := rfl
      _ = poissonKernel x y t := by
        rw [integral_poissonLayerWeight_cutoff hy hs]
        simp [poissonKernel, s, sq_abs]
  have houter : ∀ r : ℝ,
      ∫ t, F (t, r) ∂μ =
        μ.real (Metric.closedBall x r) * poissonLayerWeight y r := by
    intro r
    have hpoint : (fun t : ℝ => F (t, r)) =
        (Metric.closedBall x r).indicator (fun _ => poissonLayerWeight y r) := by
      funext t
      simp [F, Set.indicator]
    rw [hpoint, integral_indicator_const _ measurableSet_closedBall]
    simp [smul_eq_mul]
  calc
    poissonTransform μ x y = ∫ t, ∫ r, F (t, r) ∂ν ∂μ := by
      unfold poissonTransform
      apply integral_congr_ae
      filter_upwards with t
      exact (hinner t).symm
    _ = ∫ r, ∫ t, F (t, r) ∂μ ∂ν := by
      calc
        ∫ t, ∫ r, F (t, r) ∂ν ∂μ = ∫ p, F p ∂μ.prod ν :=
          (integral_prod F hFint).symm
        _ = ∫ r, ∫ t, F (t, r) ∂μ ∂ν := integral_prod_symm F hFint
    _ = ∫ r in Set.Ioi (0 : ℝ),
        μ.real (Metric.closedBall x r) * poissonLayerWeight y r := by
      calc
        ∫ r, ∫ t, F (t, r) ∂μ ∂ν =
            ∫ r, μ.real (Metric.closedBall x r) * poissonLayerWeight y r ∂ν := by
          apply integral_congr_ae
          exact ae_of_all _ houter
        _ = ∫ r in Set.Ioi (0 : ℝ),
            μ.real (Metric.closedBall x r) * poissonLayerWeight y r := rfl

/-- After scaling the layer-cake formula, the Poisson transform is the profile average of centered
ball densities. -/
theorem poissonTransform_eq_profile_ballDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x y : ℝ) (hy : 0 < y) :
    poissonTransform μ x y =
      ∫ u, poissonLayerProfile u * symmetricBallDensity μ x (y * u) := by
  have hchange :
      ∫ r in Set.Ioi (0 : ℝ),
        μ.real (Metric.closedBall x r) * poissonLayerWeight y r =
      y * ∫ u in Set.Ioi (0 : ℝ),
        μ.real (Metric.closedBall x (y * u)) * poissonLayerWeight y (y * u) := by
    simpa [smul_eq_mul] using
      (integral_comp_mul_left_Ioi'
        (fun r : ℝ => μ.real (Metric.closedBall x r) * poissonLayerWeight y r)
        0 hy).symm
  have hpoint : ∀ u ∈ Set.Ioi (0 : ℝ),
      y * (μ.real (Metric.closedBall x (y * u)) * poissonLayerWeight y (y * u)) =
        poissonLayerProfile u * symmetricBallDensity μ x (y * u) := by
    intro u hu
    have hu' : 0 < u := Set.mem_Ioi.mp hu
    have hru : 0 < y * u := mul_pos hy hu'
    have hmass : μ.real (Metric.closedBall x (y * u)) =
        2 * (y * u) * symmetricBallDensity μ x (y * u) := by
      simp only [symmetricBallDensity, if_pos hru]
      field_simp [ne_of_gt hy, ne_of_gt hu']
    rw [hmass]
    have hden1 : 1 + u ^ 2 ≠ 0 := by positivity
    have hden2 : (y * u) ^ 2 + y ^ 2 ≠ 0 := by positivity
    dsimp [poissonLayerProfile, poissonLayerWeight]
    field_simp [ne_of_gt hy, hden1, hden2]
    ring
  calc
    poissonTransform μ x y =
        ∫ r in Set.Ioi (0 : ℝ),
          μ.real (Metric.closedBall x r) * poissonLayerWeight y r :=
      poissonTransform_eq_ballLayerIntegral μ x y hy
    _ = y * ∫ u in Set.Ioi (0 : ℝ),
          μ.real (Metric.closedBall x (y * u)) * poissonLayerWeight y (y * u) := hchange
    _ = ∫ u in Set.Ioi (0 : ℝ),
          poissonLayerProfile u * symmetricBallDensity μ x (y * u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hpoint u hu
    _ = ∫ u, poissonLayerProfile u * symmetricBallDensity μ x (y * u) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : 0 < u
      · simp [Set.indicator, hu]
      · have hu' : u ≤ 0 := le_of_not_gt hu
        have hru : y * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy.le hu'
        have hD : symmetricBallDensity μ x (y * u) = 0 := by
          simp [symmetricBallDensity, not_lt_of_ge hru]
        simp [Set.indicator, hu, hD]

/-- A finite Lebesgue density of the measure at `x` determines the Poisson-transform boundary
value at `x`. -/
theorem poissonTransform_tendsto_of_symmetricBallDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x d : ℝ)
    (hD : Filter.Tendsto (symmetricBallDensity μ x) (𝓝[>] 0) (𝓝 d)) :
    Filter.Tendsto (fun y : ℝ => poissonTransform μ x y)
      (𝓝[>] 0) (𝓝 (Real.pi * d)) := by
  obtain ⟨C, hC, hD_bdd⟩ := symmetricBallDensity_bounded_of_tendsto μ x d hD
  let H : ℝ → ℝ → ℝ := fun y u => poissonLayerProfile u * symmetricBallDensity μ x (y * u)
  let L : ℝ → ℝ := fun u => if 0 < u then poissonLayerProfile u * d else 0
  have hprofileMeas : Measurable poissonLayerProfile := by
    unfold poissonLayerProfile
    exact Measurable.div (by fun_prop) (by fun_prop)
  have hDmeas : Measurable (symmetricBallDensity μ x) := measurable_symmetricBallDensity μ x
  have hHmeas (y : ℝ) : Measurable (H y) := by
    dsimp [H]
    exact hprofileMeas.mul (hDmeas.comp (by fun_prop))
  have hmeas : ∀ᶠ y in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (H y) volume := by
    exact Filter.Eventually.of_forall fun y => (hHmeas y).aestronglyMeasurable
  have hbound : ∀ᶠ y in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂volume,
      ‖H y u‖ ≤ C * poissonLayerProfile u := by
    filter_upwards [] with y
    filter_upwards with u
    have hprof : 0 ≤ poissonLayerProfile u := by
      unfold poissonLayerProfile
      positivity
    calc
      ‖H y u‖ = poissonLayerProfile u * ‖symmetricBallDensity μ x (y * u)‖ := by
        dsimp [H]
        simp only [abs_mul, abs_of_nonneg hprof]
      _ ≤ poissonLayerProfile u * C :=
        mul_le_mul_of_nonneg_left (hD_bdd (y * u)) hprof
      _ = C * poissonLayerProfile u := by ring
  have hmajor : Integrable (fun u => C * poissonLayerProfile u) volume := by
    simpa [mul_comm] using integrable_poissonLayerProfile.const_mul C
  have hlim : ∀ᵐ u ∂volume,
      Filter.Tendsto (fun y : ℝ => H y u) (𝓝[>] 0) (𝓝 (L u)) := by
    filter_upwards [] with u
    by_cases hu : 0 < u
    · have hyu0 : Filter.Tendsto (fun y : ℝ => y * u) (𝓝[>] 0) (𝓝 0) := by
        have hid : Filter.Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
          Filter.tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using hid.mul_const u
      have hyu_pos : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y * u := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact mul_pos (Set.mem_Ioi.mp hy) hu
      have hyu : Filter.Tendsto (fun y : ℝ => y * u) (𝓝[>] 0) (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨hyu0, hyu_pos⟩
      have hDy : Filter.Tendsto (fun y : ℝ => symmetricBallDensity μ x (y * u))
          (𝓝[>] 0) (𝓝 d) := hD.comp hyu
      simpa [H, L, hu] using (tendsto_const_nhds.mul hDy)
    · have hu' : u ≤ 0 := le_of_not_gt hu
      have hzero : ∀ᶠ y in 𝓝[>] (0 : ℝ), symmetricBallDensity μ x (y * u) = 0 := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hru : y * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
          (Set.mem_Ioi.mp hy).le hu'
        simp [symmetricBallDensity, not_lt_of_ge hru]
      have hHzero : (fun y : ℝ => H y u) =ᶠ[𝓝[>] 0] fun _ => 0 := by
        filter_upwards [hzero] with y hy
        simp [H, hy]
      simpa [L, hu] using
        (Filter.Tendsto.congr' hHzero.symm tendsto_const_nhds)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (fun u => C * poissonLayerProfile u) hmeas hbound hmajor hlim
  have hlimit : ∫ u, L u ∂volume = Real.pi * d := by
    calc
      ∫ u, L u ∂volume = ∫ u in Set.Ioi (0 : ℝ), poissonLayerProfile u * d := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with u
        by_cases hu : 0 < u
        · simp [L, Set.indicator, hu]
        · simp [L, Set.indicator, hu]
      _ = (∫ u in Set.Ioi (0 : ℝ), poissonLayerProfile u) * d := by
        rw [integral_mul_const]
      _ = Real.pi * d := by rw [integral_poissonLayerProfile]
  have htransformed : Filter.Tendsto (fun y => ∫ u, H y u ∂volume)
      (𝓝[>] 0) (𝓝 (Real.pi * d)) := by
    rw [← hlimit]
    simpa [H] using hDCT
  have heq : (fun y : ℝ => poissonTransform μ x y) =ᶠ[𝓝[>] 0]
      fun y => ∫ u, H y u ∂volume := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa [H] using
      (poissonTransform_eq_profile_ballDensity μ x y (Set.mem_Ioi.mp hy))
  exact Filter.Tendsto.congr' heq.symm htransformed

/-- The Poisson transform of an arbitrary finite measure converges almost everywhere to `π` times
the Radon–Nikodym density of its absolutely continuous part. -/
theorem poissonTransform_tendsto_ae (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      Filter.Tendsto (fun y : ℝ => poissonTransform μ x y)
        (𝓝[>] 0) (𝓝 (Real.pi * (μ.rnDeriv volume x).toReal)) := by
  filter_upwards [ae_tendsto_symmetricBallDensity μ] with x hx
  exact poissonTransform_tendsto_of_symmetricBallDensity μ x
    (μ.rnDeriv volume x).toReal hx

/-- The imaginary part of the Borel transform of an arbitrary finite measure converges almost
everywhere to `π` times the density of the absolutely continuous part. -/
theorem im_resolventTransform_tendsto_ae (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      Filter.Tendsto
        (fun y : ℝ =>
          (MeasureTheory.resolventTransform μ ((x : ℂ) + (y : ℂ) * Complex.I)).im)
        (𝓝[>] 0) (𝓝 (Real.pi * (μ.rnDeriv volume x).toReal)) := by
  filter_upwards [poissonTransform_tendsto_ae μ] with x hx
  apply Filter.Tendsto.congr' ?_ hx
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hypos : 0 < y := Set.mem_Ioi.mp hy
  exact (im_resolventTransform_eq_poissonTransform μ x y hypos).symm

end AndersonAC.Boundary
