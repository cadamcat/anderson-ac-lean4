import AndersonAC.BoundaryFinite.Nevanlinna
import AndersonAC.Boundary.PoissonBoundary
import AndersonAC.Boundary.BoundaryDifference
import AndersonAC.HInf.Uniqueness

/-!
# Finite vertical boundary values of Borel transforms (Teschl Corollary 3.25)

Every Pick function `H` on the upper half-plane admits a Nevanlinna representation
(`TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add`), whose imaginary part decomposes on any
bounded energy range into the Poisson transform of a truncated finite measure plus a uniformly
`O(η)` far-field tail. By `poissonTransform_tendsto_ae`, the imaginary part of any Pick function
therefore has a finite vertical boundary limit almost everywhere on `ℝ`.

To recover the real part of a Pick function `F` without square roots or singular integrals, we
consider the two auxiliary Pick functions
`H₀(z) = -(F(z) + i)⁻¹` and `H₁(z) = -(F(z) - 1 + i)⁻¹`.
For any `w = u + i v` with `0 ≤ v`,
`Im H₀ = (v + 1) / (u² + (v + 1)²)` and `Im H₁ = (v + 1) / ((u - 1)² + (v + 1)²)`,
so `u = Re w` is an explicit rational function of `v`, `Im H₀`, and `Im H₁`:
`u = 2⁻¹ * (1 + (v + 1) / Im H₀ - (v + 1) / Im H₁)`.
Since `‖H₀(z)‖² ≤ Im H₀(z)` and `‖H₁(z)‖² ≤ Im H₁(z)` on the upper half-plane, a vanishing
imaginary boundary limit forces a vanishing complex boundary limit, which occurs only on a
Lebesgue-null set by `AndersonAC.HInf.volume_boundaryZero_eq_zero`. Thus `Re F(E + i η)` and
`F(E + i η)` converge as `η ↓ 0` for Lebesgue-almost every `E ∈ ℝ`.
-/

noncomputable section

open Complex MeasureTheory Filter Set Topology

namespace AndersonAC.Boundary

private def nevanlinnaWeightCut (N : ℕ) : ℝ → ℝ :=
  (Icc (-(N : ℝ)) (N : ℝ)).indicator (fun x => 1 + x ^ 2)

private def nevanlinnaWeightTail (N : ℕ) : ℝ → ℝ :=
  (Icc (-(N : ℝ)) (N : ℝ))ᶜ.indicator (fun x => 1 + x ^ 2)

private theorem measurable_nevanlinnaWeightCut (N : ℕ) :
    Measurable (nevanlinnaWeightCut N) := by
  unfold nevanlinnaWeightCut
  exact (by fun_prop : Measurable (fun x : ℝ => 1 + x ^ 2)).indicator measurableSet_Icc

private theorem measurable_nevanlinnaWeightTail (N : ℕ) :
    Measurable (nevanlinnaWeightTail N) := by
  unfold nevanlinnaWeightTail
  exact (by fun_prop : Measurable (fun x : ℝ => 1 + x ^ 2)).indicator measurableSet_Icc.compl

private theorem nevanlinnaWeightCut_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ nevanlinnaWeightCut N x := by
  by_cases hx : x ∈ Icc (-(N : ℝ)) (N : ℝ)
  · simp only [nevanlinnaWeightCut, indicator_of_mem hx]
    positivity
  · simp [nevanlinnaWeightCut, hx]

private theorem nevanlinnaWeightTail_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ nevanlinnaWeightTail N x := by
  by_cases hx : x ∈ Icc (-(N : ℝ)) (N : ℝ)
  · rw [nevanlinnaWeightTail, indicator_of_notMem (notMem_compl_iff.mpr hx)]
  · have hxcompl : x ∈ (Icc (-(N : ℝ)) (N : ℝ))ᶜ := hx
    simp only [nevanlinnaWeightTail, indicator_of_mem hxcompl]
    positivity

private theorem nevanlinnaWeightCut_add_tail (N : ℕ) (x : ℝ) :
    nevanlinnaWeightCut N x + nevanlinnaWeightTail N x = 1 + x ^ 2 := by
  simp [nevanlinnaWeightCut, nevanlinnaWeightTail]

private theorem nevanlinnaWeightCut_le (N : ℕ) (x : ℝ) :
    nevanlinnaWeightCut N x ≤ 1 + (N : ℝ) ^ 2 := by
  by_cases hx : x ∈ Icc (-(N : ℝ)) (N : ℝ)
  · simp only [nevanlinnaWeightCut, indicator_of_mem hx]
    nlinarith [hx.1, hx.2]
  · simp only [nevanlinnaWeightCut, indicator_of_notMem hx]
    positivity

private theorem integrable_nevanlinnaWeightCut (ρ : Measure ℝ) [IsFiniteMeasure ρ] (N : ℕ) :
    Integrable (nevanlinnaWeightCut N) ρ := by
  refine (integrable_const (1 + (N : ℝ) ^ 2)).mono'
    (measurable_nevanlinnaWeightCut N).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (nevanlinnaWeightCut_nonneg N x)]
  exact nevanlinnaWeightCut_le N x

private def nevanlinnaCutMeasure (ρ : Measure ℝ) (N : ℕ) : Measure ℝ :=
  ρ.withDensity (fun x => ENNReal.ofReal (nevanlinnaWeightCut N x))

private instance isFiniteMeasure_nevanlinnaCutMeasure
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (N : ℕ) :
    IsFiniteMeasure (nevanlinnaCutMeasure ρ N) := by
  unfold nevanlinnaCutMeasure
  exact isFiniteMeasure_withDensity_ofReal (integrable_nevanlinnaWeightCut ρ N).hasFiniteIntegral

private theorem poissonTransform_nevanlinnaCutMeasure
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (N : ℕ) (E η : ℝ) :
    poissonTransform (nevanlinnaCutMeasure ρ N) E η =
      ∫ x, nevanlinnaWeightCut N x * poissonKernel E η x ∂ρ := by
  unfold poissonTransform nevanlinnaCutMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_nevanlinnaWeightCut N).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (nevanlinnaWeightCut_nonneg N x), smul_eq_mul]

private theorem nevanlinnaWeightTail_mul_poissonKernel_le
    {N : ℕ} {E η : ℝ} (hEN : |E| + 1 ≤ (N : ℝ)) (hη : 0 < η) (x : ℝ) :
    nevanlinnaWeightTail N x * poissonKernel E η x ≤ η * (1 + (1 + |E|) ^ 2) := by
  by_cases hx : x ∈ Icc (-(N : ℝ)) (N : ℝ)
  · rw [nevanlinnaWeightTail, indicator_of_notMem (notMem_compl_iff.mpr hx), zero_mul]
    positivity
  · have hxcompl : x ∈ (Icc (-(N : ℝ)) (N : ℝ))ᶜ := hx
    simp only [nevanlinnaWeightTail, indicator_of_mem hxcompl]
    have hnotabs : ¬ |x| ≤ (N : ℝ) := by
      rwa [abs_le]
    have hNx : (N : ℝ) < |x| := lt_of_not_ge hnotabs
    have hEx : |E| + 1 < |x| := lt_of_le_of_lt hEN hNx
    have htri : |x| ≤ |x - E| + |E| := by
      simpa using abs_add_le (x - E) E
    have hone : 1 ≤ |x - E| := by linarith
    have hxbound : |x| ≤ (1 + |E|) * |x - E| := by
      have hmul : |E| ≤ |E| * |x - E| := le_mul_of_one_le_right (abs_nonneg E) hone
      linarith
    have hsq1 : 1 ≤ (x - E) ^ 2 := by
      have h := mul_le_mul hone hone zero_le_one (by positivity)
      simpa [sq, sq_abs] using h
    have hsqx : x ^ 2 ≤ (1 + |E|) ^ 2 * (x - E) ^ 2 := by
      have h := mul_le_mul hxbound hxbound (abs_nonneg x) (by positivity)
      have h1 : |x| * |x| = x ^ 2 := by rw [← sq, sq_abs]
      have h2 : ((1 + |E|) * |x - E|) * ((1 + |E|) * |x - E|) =
          (1 + |E|) ^ 2 * (x - E) ^ 2 := by
        calc
          ((1 + |E|) * |x - E|) * ((1 + |E|) * |x - E|) =
              (1 + |E|) ^ 2 * |x - E| ^ 2 := by ring
          _ = (1 + |E|) ^ 2 * (x - E) ^ 2 := by rw [sq_abs]
      linarith
    have hnum : 1 + x ^ 2 ≤ (1 + (1 + |E|) ^ 2) * ((x - E) ^ 2 + η ^ 2) := by
      nlinarith [sq_nonneg η, sq_nonneg (1 + |E|)]
    have hden : 0 < (x - E) ^ 2 + η ^ 2 := by positivity
    unfold poissonKernel
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith

private theorem nevanlinnaKernel_im_vertical (E η x : ℝ) :
    (TauCeti.nevanlinnaKernel ((E : ℂ) + (η : ℂ) * I) x).im =
      (1 + x ^ 2) * poissonKernel E η x := by
  rw [TauCeti.nevanlinnaKernel_im]
  unfold poissonKernel
  have hnorm : normSq ((x : ℂ) - ((E : ℂ) + (η : ℂ) * I)) = (x - E) ^ 2 + η ^ 2 := by
    simp only [normSq_apply, sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im]
    ring
  rw [hnorm]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add]
  ring

private theorem integral_nevanlinnaKernel_im_eq_cut_add_tail
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (N : ℕ) {E η : ℝ} (hEN : |E| + 1 ≤ (N : ℝ))
    (hη : 0 < η) :
    (∫ x, TauCeti.nevanlinnaKernel ((E : ℂ) + (η : ℂ) * I) x ∂ρ).im =
      poissonTransform (nevanlinnaCutMeasure ρ N) E η +
        ∫ x, nevanlinnaWeightTail N x * poissonKernel E η x ∂ρ := by
  let z : ℂ := (E : ℂ) + (η : ℂ) * I
  have hz : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet, z] using hη
  have hint : Integrable (TauCeti.nevanlinnaKernel z) ρ :=
    TauCeti.integrable_nevanlinnaKernel hz ρ
  have hswap : (∫ x, TauCeti.nevanlinnaKernel z x ∂ρ).im =
      ∫ x, (TauCeti.nevanlinnaKernel z x).im ∂ρ := by
    simpa using (Complex.imCLM.integral_comp_comm hint).symm
  have hcutInt : Integrable (fun x => nevanlinnaWeightCut N x * poissonKernel E η x) ρ := by
    refine ((integrable_poissonKernel ρ E η hη).const_mul (1 + (N : ℝ) ^ 2)).mono'
      ((measurable_nevanlinnaWeightCut N).mul (measurable_poissonKernel E η)).aestronglyMeasurable
      ?_
    filter_upwards with x
    have hpk : 0 ≤ poissonKernel E η x := div_nonneg hη.le (by positivity)
    have hnonneg : 0 ≤ nevanlinnaWeightCut N x * poissonKernel E η x :=
      mul_nonneg (nevanlinnaWeightCut_nonneg N x) hpk
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_right (nevanlinnaWeightCut_le N x) hpk
  have htailInt : Integrable (fun x => nevanlinnaWeightTail N x * poissonKernel E η x) ρ := by
    refine (integrable_const (η * (1 + (1 + |E|) ^ 2))).mono'
      ((measurable_nevanlinnaWeightTail N).mul (measurable_poissonKernel E η)).aestronglyMeasurable
      ?_
    filter_upwards with x
    have hpk : 0 ≤ poissonKernel E η x := div_nonneg hη.le (by positivity)
    have hnonneg : 0 ≤ nevanlinnaWeightTail N x * poissonKernel E η x :=
      mul_nonneg (nevanlinnaWeightTail_nonneg N x) hpk
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact nevanlinnaWeightTail_mul_poissonKernel_le hEN hη x
  rw [hswap, poissonTransform_nevanlinnaCutMeasure, ← integral_add hcutInt htailInt]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [z]
  rw [nevanlinnaKernel_im_vertical, ← add_mul, nevanlinnaWeightCut_add_tail]

private theorem tendsto_integral_nevanlinnaWeightTail
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (N : ℕ) {E : ℝ} (hEN : |E| + 1 ≤ (N : ℝ)) :
    Tendsto (fun η : ℝ => ∫ x, nevanlinnaWeightTail N x * poissonKernel E η x ∂ρ)
      (𝓝[>] 0) (𝓝 0) := by
  let B : ℝ → ℝ := fun η => ρ.real univ * (η * (1 + (1 + |E|) ^ 2))
  have hB : Tendsto B (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun η : ℝ => η * (1 + (1 + |E|) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hid.mul_const (1 + (1 + |E|) ^ 2)
    simpa [B] using h1.const_mul (ρ.real univ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with η hη
    have hηpos : 0 < η := mem_Ioi.mp hη
    refine integral_nonneg fun x => mul_nonneg (nevanlinnaWeightTail_nonneg N x) ?_
    unfold poissonKernel
    exact div_nonneg hηpos.le (by positivity)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    have hηpos : 0 < η := mem_Ioi.mp hη
    have htailInt : Integrable (fun x => nevanlinnaWeightTail N x * poissonKernel E η x) ρ := by
      refine (integrable_const (η * (1 + (1 + |E|) ^ 2))).mono'
        ((measurable_nevanlinnaWeightTail N).mul (measurable_poissonKernel E η)).aestronglyMeasurable
        ?_
      filter_upwards with x
      have hpk : 0 ≤ poissonKernel E η x := div_nonneg hηpos.le (by positivity)
      have hnonneg : 0 ≤ nevanlinnaWeightTail N x * poissonKernel E η x :=
        mul_nonneg (nevanlinnaWeightTail_nonneg N x) hpk
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact nevanlinnaWeightTail_mul_poissonKernel_le hEN hηpos x
    have hle := integral_mono htailInt (integrable_const (η * (1 + (1 + |E|) ^ 2)))
      (fun x => nevanlinnaWeightTail_mul_poissonKernel_le hEN hηpos x)
    simpa [B, integral_const, smul_eq_mul] using hle

/-- Every Pick function on the upper half-plane has a finite vertical boundary limit of its
imaginary part almost everywhere on the real line. -/
theorem pick_im_tendsto_ae {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (H z).im) :
    ∀ᵐ E : ℝ ∂(volume : Measure ℝ),
      ∃ v₀ : ℝ, Tendsto (fun η : ℝ => (H ((E : ℂ) + (η : ℂ) * I)).im) (𝓝[>] 0) (𝓝 v₀) := by
  obtain ⟨ρ, b, hρ, -, hrep⟩ := TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add hH him
  let _ := hρ
  have haeN : ∀ N : ℕ, ∀ᵐ E : ℝ ∂(volume : Measure ℝ),
      ∃ L : ℝ, Tendsto (fun η : ℝ => poissonTransform (nevanlinnaCutMeasure ρ N) E η)
        (𝓝[>] 0) (𝓝 L) := by
    intro N
    filter_upwards [poissonTransform_tendsto_ae (nevanlinnaCutMeasure ρ N)] with E hE
    exact ⟨_, hE⟩
  filter_upwards [ae_all_iff.mpr haeN] with E hE
  obtain ⟨N, hN⟩ := exists_nat_gt (|E| + 1)
  have hEN : |E| + 1 ≤ (N : ℝ) := le_of_lt hN
  obtain ⟨L, hL⟩ := hE N
  refine ⟨L, ?_⟩
  have hlin : Tendsto (fun η : ℝ => b * η) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.const_mul b
  have htail := tendsto_integral_nevanlinnaWeightTail ρ N hEN
  have hsum : Tendsto
      (fun η : ℝ => b * η +
        (poissonTransform (nevanlinnaCutMeasure ρ N) E η +
          ∫ x, nevanlinnaWeightTail N x * poissonKernel E η x ∂ρ))
      (𝓝[>] 0) (𝓝 L) := by
    simpa using hlin.add (hL.add htail)
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hηpos : 0 < η := mem_Ioi.mp hη
  let z : ℂ := (E : ℂ) + (η : ℂ) * I
  have hz : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet, z] using hηpos
  have hrepE := congrArg Complex.im (hrep z hz)
  rw [← integral_nevanlinnaKernel_im_eq_cut_add_tail ρ N hEN hηpos]
  simpa [z, Complex.add_im, Complex.mul_im] using hrepE.symm

/-- The transformed Pick function `z ↦ -(F z + i)⁻¹`. -/
private def shiftedNegInv (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(F z + I)⁻¹

private theorem shiftedNegInv_im_eq (w : ℂ) :
    (-(w + I)⁻¹).im = (w.im + 1) / (w.re ^ 2 + (w.im + 1) ^ 2) := by
  simp only [neg_im, inv_im, normSq_apply, add_re, add_im, I_re, I_im, add_zero]
  ring

private theorem add_I_ne_zero_of_im_nonneg' {w : ℂ} (hw : 0 ≤ w.im) :
    w + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

private theorem shiftedNegInv_im_pos {w : ℂ} (hw : 0 ≤ w.im) :
    0 < (-(w + I)⁻¹).im := by
  rw [shiftedNegInv_im_eq]
  have hnum : 0 < w.im + 1 := by linarith
  have hden : 0 < w.re ^ 2 + (w.im + 1) ^ 2 := by positivity
  exact div_pos hnum hden

private theorem shiftedNegInv_norm_sq_le_im {w : ℂ} (hw : 0 ≤ w.im) :
    ‖-(w + I)⁻¹‖ ^ 2 ≤ (-(w + I)⁻¹).im := by
  rw [norm_neg, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq, shiftedNegInv_im_eq]
  have hnorm : Complex.normSq (w + I) = w.re ^ 2 + (w.im + 1) ^ 2 := by
    simp only [normSq_apply, add_re, add_im, I_re, I_im, add_zero]
    ring
  rw [hnorm, inv_eq_one_div]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

private theorem shiftedNegInv_norm_le_one {w : ℂ} (hw : 0 ≤ w.im) :
    ‖-(w + I)⁻¹‖ ≤ 1 := by
  rw [norm_neg, norm_inv]
  have him : 1 ≤ (w + I).im := by
    simp only [add_im, I_im]
    linarith
  have hnorm : 1 ≤ ‖w + I‖ := by
    have hle := abs_im_le_norm (w + I)
    rw [abs_of_nonneg (by linarith)] at hle
    exact him.trans hle
  exact inv_le_one_of_one_le₀ hnorm

private theorem differentiableOn_shiftedNegInv {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    DifferentiableOn ℂ (shiftedNegInv F) UpperHalfPlane.upperHalfPlaneSet := by
  unfold shiftedNegInv
  exact ((hF.add_const I).inv (fun z hz => add_I_ne_zero_of_im_nonneg' (him z hz))).neg

private theorem shiftedNegInv_im_tendsto_ae {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∀ᵐ E : ℝ ∂(volume : Measure ℝ),
      ∃ a₀ : ℝ, a₀ ≠ 0 ∧
        Tendsto (fun η : ℝ => (shiftedNegInv F ((E : ℂ) + (η : ℂ) * I)).im)
          (𝓝[>] 0) (𝓝 a₀) := by
  have hdiff : DifferentiableOn ℂ (shiftedNegInv F) {z : ℂ | 0 < z.im} :=
    differentiableOn_shiftedNegInv hF him
  have hbdd : ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖shiftedNegInv F z‖ ≤ M :=
    ⟨1, fun z hz => shiftedNegInv_norm_le_one (him z hz)⟩
  have hne : ∃ z : ℂ, 0 < z.im ∧ shiftedNegInv F z ≠ 0 := by
    refine ⟨I, by simp, ?_⟩
    unfold shiftedNegInv
    exact neg_ne_zero.mpr (inv_ne_zero (add_I_ne_zero_of_im_nonneg' (him I (by simp))))
  have hzero := AndersonAC.HInf.volume_boundaryZero_eq_zero (shiftedNegInv F) hdiff hbdd hne
  have haeNotZero : ∀ᵐ E : ℝ ∂(volume : Measure ℝ),
      ¬ Tendsto (fun η : ℝ => shiftedNegInv F ((E : ℂ) + (η : ℂ) * I)) (𝓝[>] 0) (𝓝 0) :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have haeIm := pick_im_tendsto_ae (differentiableOn_shiftedNegInv hF him)
    (fun z hz => (shiftedNegInv_im_pos (him z hz)).le)
  filter_upwards [haeIm, haeNotZero] with E ⟨a₀, ha₀⟩ hnot0
  refine ⟨a₀, ?_, ha₀⟩
  intro ha₀0
  apply hnot0
  rw [ha₀0] at ha₀
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun η : ℝ => ‖shiftedNegInv F ((E : ℂ) + (η : ℂ) * I)‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ha₀ ?_ ?_
    · filter_upwards with η
      positivity
    · filter_upwards [self_mem_nhdsWithin] with η hη
      have hz : ((E : ℂ) + (η : ℂ) * I) ∈ UpperHalfPlane.upperHalfPlaneSet := by
        simpa [UpperHalfPlane.upperHalfPlaneSet] using mem_Ioi.mp hη
      exact shiftedNegInv_norm_sq_le_im (him _ hz)
  have hsqrt : Tendsto
      (fun η : ℝ => Real.sqrt (‖shiftedNegInv F ((E : ℂ) + (η : ℂ) * I)‖ ^ 2))
      (𝓝[>] 0) (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt

private theorem re_eq_of_shiftedNegInv_im {w : ℂ} (hw : 0 ≤ w.im) :
    w.re = 2⁻¹ * (1 + (w.im + 1) / (-(w + I)⁻¹).im - (w.im + 1) / (-(w - 1 + I)⁻¹).im) := by
  have hw1 : (w - 1).im = w.im := by simp
  have hw1_re : (w - 1).re = w.re - 1 := by simp
  rw [shiftedNegInv_im_eq w, shiftedNegInv_im_eq (w - 1), hw1, hw1_re]
  have hnum : w.im + 1 ≠ 0 := by linarith
  have hden0 : w.re ^ 2 + (w.im + 1) ^ 2 ≠ 0 := by positivity
  have hden1 : (w.re - 1) ^ 2 + (w.im + 1) ^ 2 ≠ 0 := by positivity
  field_simp [hnum, hden0, hden1]
  ring

/-- Every Pick function on the upper half-plane has a finite complex vertical boundary limit
almost everywhere on the real line. -/
theorem pick_hasBoundary_ae {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∀ᵐ E : ℝ ∂(volume : Measure ℝ),
      ∃ w : ℂ, AndersonAC.Blueprint.HasBoundary F E w := by
  have hF1 : DifferentiableOn ℂ (fun z => F z - 1) UpperHalfPlane.upperHalfPlaneSet :=
    hF.sub_const 1
  have him1 : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z - 1).im := by
    intro z hz
    simpa using him z hz
  filter_upwards [pick_im_tendsto_ae hF him,
    shiftedNegInv_im_tendsto_ae hF him,
    shiftedNegInv_im_tendsto_ae hF1 him1] with E ⟨v₀, hv₀⟩ ⟨a₀, ha₀ne, ha₀⟩ ⟨b₀, hb₀ne, hb₀⟩
  let u₀ : ℝ := 2⁻¹ * (1 + (v₀ + 1) / a₀ - (v₀ + 1) / b₀)
  refine ⟨(u₀ : ℂ) + (v₀ : ℂ) * I, ?_⟩
  have hv1 : Tendsto (fun η : ℝ => (F ((E : ℂ) + (η : ℂ) * I)).im + 1)
      (𝓝[>] 0) (𝓝 (v₀ + 1)) := hv₀.add_const 1
  have hdiv0 : Tendsto
      (fun η : ℝ => ((F ((E : ℂ) + (η : ℂ) * I)).im + 1) /
        (shiftedNegInv F ((E : ℂ) + (η : ℂ) * I)).im)
      (𝓝[>] 0) (𝓝 ((v₀ + 1) / a₀)) := hv1.div ha₀ ha₀ne
  have hdiv1 : Tendsto
      (fun η : ℝ => ((F ((E : ℂ) + (η : ℂ) * I)).im + 1) /
        (shiftedNegInv (fun z => F z - 1) ((E : ℂ) + (η : ℂ) * I)).im)
      (𝓝[>] 0) (𝓝 ((v₀ + 1) / b₀)) := hv1.div hb₀ hb₀ne
  have hreFormula : Tendsto
      (fun η : ℝ => 2⁻¹ * (1 +
        ((F ((E : ℂ) + (η : ℂ) * I)).im + 1) /
          (shiftedNegInv F ((E : ℂ) + (η : ℂ) * I)).im -
        ((F ((E : ℂ) + (η : ℂ) * I)).im + 1) /
          (shiftedNegInv (fun z => F z - 1) ((E : ℂ) + (η : ℂ) * I)).im))
      (𝓝[>] 0) (𝓝 u₀) := by
    dsimp [u₀]
    exact ((tendsto_const_nhds.add hdiv0).sub hdiv1).const_mul 2⁻¹
  have hre : Tendsto (fun η : ℝ => (F ((E : ℂ) + (η : ℂ) * I)).re) (𝓝[>] 0) (𝓝 u₀) := by
    refine hreFormula.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hz : ((E : ℂ) + (η : ℂ) * I) ∈ UpperHalfPlane.upperHalfPlaneSet := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using mem_Ioi.mp hη
    exact (re_eq_of_shiftedNegInv_im (him _ hz)).symm
  have hreC : Tendsto (fun η : ℝ => ((F ((E : ℂ) + (η : ℂ) * I)).re : ℂ))
      (𝓝[>] 0) (𝓝 (u₀ : ℂ)) :=
    (Complex.continuous_ofReal.tendsto u₀).comp hre
  have himC : Tendsto (fun η : ℝ => ((F ((E : ℂ) + (η : ℂ) * I)).im : ℂ) * I)
      (𝓝[>] 0) (𝓝 ((v₀ : ℂ) * I)) :=
    ((Complex.continuous_ofReal.tendsto v₀).comp hv₀).mul_const I
  unfold AndersonAC.Blueprint.HasBoundary
  refine (hreC.add himC).congr' ?_
  filter_upwards with η
  exact Complex.re_add_im (F ((E : ℂ) + (η : ℂ) * I))

private theorem borelTransform_eq_resolventTransform' (μ : Measure ℝ) :
    AndersonAC.Blueprint.borelTransform μ = MeasureTheory.resolventTransform μ := by
  funext z
  rw [AndersonAC.Blueprint.borelTransform, MeasureTheory.resolventTransform_apply]
  apply integral_congr_ae
  filter_upwards with t
  simp [_root_.resolvent, Ring.inverse_eq_inv']

private theorem borelTransform_differentiableOn_upperHalfPlane (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (AndersonAC.Blueprint.borelTransform μ)
      UpperHalfPlane.upperHalfPlaneSet := by
  have hsubset : UpperHalfPlane.upperHalfPlaneSet ⊆
      (algebraMap ℝ ℂ '' μ.support)ᶜ := by
    intro z hz hzmem
    rcases hzmem with ⟨t, _, htz⟩
    have hzim : 0 < z.im := hz
    rw [← htz] at hzim
    simp at hzim
  rw [borelTransform_eq_resolventTransform']
  exact (MeasureTheory.analyticOn_resolventTransform (μ := μ)).differentiableOn.mono hsubset

private theorem borelTransform_im_nonneg_upperHalfPlane (μ : Measure ℝ) [IsFiniteMeasure μ]
    (z : ℂ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    0 ≤ (AndersonAC.Blueprint.borelTransform μ z).im := by
  have hzim : 0 < z.im := hz
  rw [borelTransform_eq_resolventTransform']
  have hrepr : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  rw [hrepr, im_resolventTransform_eq_poissonTransform μ z.re z.im hzim]
  unfold poissonTransform
  apply integral_nonneg
  intro t
  exact div_nonneg (le_of_lt hzim) (by positivity)

/-- **Teschl Corollary 3.25 (`BoundaryInput.finite`).** The Borel transform of every finite measure
on `ℝ` has a finite complex vertical boundary value at Lebesgue-almost every energy. -/
theorem boundaryFinite_proof :
    ∀ μ : Measure ℝ, IsFiniteMeasure μ →
      ∀ᵐ E ∂(volume : Measure ℝ),
        ∃ w : ℂ, AndersonAC.Blueprint.HasBoundary (AndersonAC.Blueprint.borelTransform μ) E w := by
  intro μ hμ
  let _ := hμ
  exact pick_hasBoundary_ae (borelTransform_differentiableOn_upperHalfPlane μ)
    (borelTransform_im_nonneg_upperHalfPlane μ)

/-- The complete `BoundaryInput` package (`Teschl Corollary 3.25`, bounded-boundary criterion,
and `difference_nonzero`). -/
theorem boundary_proof_full : AndersonAC.Blueprint.BoundaryInput :=
  boundary_proof_of_finite boundaryFinite_proof

end AndersonAC.Boundary
