import AndersonAC.S9.Core

/-! Scalar cavity boundary algebra from §9:474–511. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace AndersonAC.SolS9

/-- A positive finite cavity boundary keeps every real own-site
denominator away from zero and gives a positive finite scalar boundary. -/
theorem cavity_positive_boundary_all (M : ℂ → ℂ) (g : ℝ → ℂ → ℂ) (E : ℝ)
    (hM : positiveBoundary M E)
    (hcavity : ∀ s z, 0 < z.im → g s z = ((s : ℂ) - M z)⁻¹) :
    ∀ s : ℝ, positiveBoundary (g s) E := by
  rcases hM with ⟨w, hw, hwim⟩
  change Tendsto (fun η : ℝ => M ((E : ℂ) + η * Complex.I)) (𝓝[>] 0) (𝓝 w) at hw
  intro s
  have hne : (s : ℂ) - w ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hi
    linarith
  refine ⟨((s : ℂ) - w)⁻¹, ?_, ?_⟩
  · change Tendsto (fun η : ℝ => g s ((E : ℂ) + η * Complex.I)) (𝓝[>] 0)
      (𝓝 (((s : ℂ) - w)⁻¹))
    have hlim := (tendsto_const_nhds.sub hw).inv₀ hne
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hηpos : 0 < η := hη
    symm
    apply hcavity
    simpa using hηpos
  · simp only [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    exact div_pos hwim (Complex.normSq_pos.mpr hne)

/-- A diffuse own-site law and almost-sure positive site boundaries rule
out a real cavity boundary. This is the conditioning argument at §9:488–502. -/
theorem cavity_im_pos_of_ae_positive {Own : Type*} [MeasurableSpace Own]
    (κ : Measure Own) [IsProbabilityMeasure κ] (V : Own → ℝ)
    (hatom : ∀ a : ℝ, κ {s | V s = a} = 0)
    (M : ℂ → ℂ) (g : Own → ℂ → ℂ) (E : ℝ)
    (hMheight : ∀ z : ℂ, 0 < z.im → 0 < (M z).im)
    (hMfinite : finiteBoundary M E)
    (hcavity : ∀ s z, 0 < z.im → g s z = ((V s : ℂ) - M z)⁻¹)
    (hpositive : ∀ᵐ s ∂κ, positiveBoundary (g s) E) :
    positiveBoundary M E := by
  rcases hMfinite with ⟨w, hw⟩
  change Tendsto (fun η : ℝ => M ((E : ℂ) + η * Complex.I)) (𝓝[>] 0) (𝓝 w) at hw
  have hwim : 0 ≤ w.im := by
    apply ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hw)
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (hMheight _ (by simpa using hη)).le
  refine ⟨w, hw, ?_⟩
  apply lt_of_le_of_ne hwim
  intro hzero
  have hwzero : w.im = 0 := hzero.symm
  have hdifferent : ∀ᵐ s ∂κ, V s ≠ w.re := by
    simpa only [ae_iff, not_not] using hatom w.re
  obtain ⟨s, hs, hsne⟩ := (hpositive.and hdifferent).exists
  rcases hs with ⟨u, hu, huim⟩
  have hne : (V s : ℂ) - w ≠ 0 := by
    intro heq
    have hr := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hr
    exact hsne (sub_eq_zero.mp hr)
  have hlimit : verticalBoundary (g s) E (((V s : ℂ) - w)⁻¹) := by
    change Tendsto (fun η : ℝ => g s ((E : ℂ) + η * Complex.I)) (𝓝[>] 0)
      (𝓝 (((V s : ℂ) - w)⁻¹))
    apply ((tendsto_const_nhds.sub hw).inv₀ hne).congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    symm
    apply hcavity
    simpa using hη
  have heq : u = ((V s : ℂ) - w)⁻¹ := tendsto_nhds_unique hu hlimit
  rw [heq] at huim
  simp [Complex.inv_im, hwzero] at huim

end AndersonAC.SolS9
