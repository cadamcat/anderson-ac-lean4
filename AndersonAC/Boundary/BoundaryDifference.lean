import AndersonAC.Boundary.Poisson
import AndersonAC.Boundary.BoundaryCriterion
import AndersonAC.Blueprint.SpectralInputs
import AndersonAC.HInf.Uniqueness

/-!
# Boundary nonvanishing from bounded analytic uniqueness

Once two Borel transforms have finite boundary values, the difference has their difference as a
boundary value. If that value vanishes, the difference of their shifted reciprocals also tends to
zero. Those shifted reciprocals are the bounded transforms used by the H∞ uniqueness input.
-/

open MeasureTheory Filter Complex
open scoped Topology

namespace AndersonAC.Boundary

private def upperHalfPlane : Set ℂ := {z | 0 < z.im}

private def verticalPath (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

/-- A shifted reciprocal difference used as a bounded analytic witness. -/
noncomputable def shiftedReciprocalDifference (μ ν : Measure ℝ) (z : ℂ) : ℂ :=
  (AndersonAC.Blueprint.borelTransform μ z + I)⁻¹ -
    (AndersonAC.Blueprint.borelTransform ν z + I)⁻¹

private theorem borelTransform_eq_resolventTransform (μ : Measure ℝ) :
    AndersonAC.Blueprint.borelTransform μ = MeasureTheory.resolventTransform μ := by
  funext z
  rw [AndersonAC.Blueprint.borelTransform, MeasureTheory.resolventTransform_apply]
  apply integral_congr_ae
  filter_upwards with t
  simp [resolvent, Ring.inverse_eq_inv']

private theorem borelTransform_im_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ]
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (AndersonAC.Blueprint.borelTransform μ z).im := by
  rw [borelTransform_eq_resolventTransform]
  have hrepr : z = (z.re : ℂ) + (z.im : ℂ) * I := by
    exact (Complex.re_add_im z).symm
  rw [hrepr, im_resolventTransform_eq_poissonTransform μ z.re z.im hz]
  unfold poissonTransform
  apply integral_nonneg
  intro t
  exact div_nonneg (le_of_lt hz) (by positivity)

private theorem borelTransform_differentiableOn_upper (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (AndersonAC.Blueprint.borelTransform μ) upperHalfPlane := by
  have hsubset : upperHalfPlane ⊆
      (algebraMap ℝ ℂ '' μ.support)ᶜ := by
    intro z hz hzmem
    rcases hzmem with ⟨t, ht, htz⟩
    rw [← htz] at hz
    simp [upperHalfPlane] at hz
  rw [borelTransform_eq_resolventTransform]
  exact (MeasureTheory.analyticOn_resolventTransform (μ := μ)).differentiableOn.mono hsubset

private theorem borelTransform_add_I_ne_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    (z : ℂ) (hz : 0 < z.im) :
    AndersonAC.Blueprint.borelTransform μ z + I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hnonneg := borelTransform_im_nonneg μ z hz
  simp at him
  linarith

private theorem shiftedReciprocalDifference_differentiableOn
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    DifferentiableOn ℂ (shiftedReciprocalDifference μ ν) upperHalfPlane := by
  have hμ := (borelTransform_differentiableOn_upper μ).add_const I
  have hν := (borelTransform_differentiableOn_upper ν).add_const I
  have hμinv : DifferentiableOn ℂ
      (fun z => (AndersonAC.Blueprint.borelTransform μ z + I)⁻¹) upperHalfPlane :=
    hμ.inv (fun z hz => borelTransform_add_I_ne_zero μ z hz)
  have hνinv : DifferentiableOn ℂ
      (fun z => (AndersonAC.Blueprint.borelTransform ν z + I)⁻¹) upperHalfPlane :=
    hν.inv (fun z hz => borelTransform_add_I_ne_zero ν z hz)
  exact hμinv.sub hνinv

private theorem shiftedReciprocalDifference_norm_le_two
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (z : ℂ) (hz : 0 < z.im) :
    ‖shiftedReciprocalDifference μ ν z‖ ≤ 2 := by
  have hμim : 1 ≤ (AndersonAC.Blueprint.borelTransform μ z + I).im := by
    have hnonneg := borelTransform_im_nonneg μ z hz
    simp only [add_im, I_im]
    linarith
  have hνim : 1 ≤ (AndersonAC.Blueprint.borelTransform ν z + I).im := by
    have hnonneg := borelTransform_im_nonneg ν z hz
    simp only [add_im, I_im]
    linarith
  have hμnorm : 1 ≤ ‖AndersonAC.Blueprint.borelTransform μ z + I‖ := by
    have hle := abs_im_le_norm (AndersonAC.Blueprint.borelTransform μ z + I)
    rw [abs_of_nonneg (le_trans (by norm_num) hμim)] at hle
    exact hμim.trans hle
  have hνnorm : 1 ≤ ‖AndersonAC.Blueprint.borelTransform ν z + I‖ := by
    have hle := abs_im_le_norm (AndersonAC.Blueprint.borelTransform ν z + I)
    rw [abs_of_nonneg (le_trans (by norm_num) hνim)] at hle
    exact hνim.trans hle
  have hμinv : ‖(AndersonAC.Blueprint.borelTransform μ z + I)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    simpa [one_div] using
      (div_le_one (lt_of_lt_of_le zero_lt_one hμnorm)).2 hμnorm
  have hνinv : ‖(AndersonAC.Blueprint.borelTransform ν z + I)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    simpa [one_div] using
      (div_le_one (lt_of_lt_of_le zero_lt_one hνnorm)).2 hνnorm
  unfold shiftedReciprocalDifference
  calc
    ‖(AndersonAC.Blueprint.borelTransform μ z + I)⁻¹ -
        (AndersonAC.Blueprint.borelTransform ν z + I)⁻¹‖ ≤
        ‖(AndersonAC.Blueprint.borelTransform μ z + I)⁻¹‖ +
          ‖(AndersonAC.Blueprint.borelTransform ν z + I)⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hμinv hνinv
    _ = 2 := by norm_num

private theorem shiftedReciprocalDifference_ne_zero
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (z : ℂ) (hz : 0 < z.im)
    (hneq : AndersonAC.Blueprint.borelTransform μ z -
      AndersonAC.Blueprint.borelTransform ν z ≠ 0) :
    shiftedReciprocalDifference μ ν z ≠ 0 := by
  have hμ := borelTransform_add_I_ne_zero μ z hz
  have hν := borelTransform_add_I_ne_zero ν z hz
  have hnum : AndersonAC.Blueprint.borelTransform ν z -
      AndersonAC.Blueprint.borelTransform μ z ≠ 0 := by
    intro h
    apply hneq
    calc
      AndersonAC.Blueprint.borelTransform μ z -
          AndersonAC.Blueprint.borelTransform ν z =
          -(AndersonAC.Blueprint.borelTransform ν z -
            AndersonAC.Blueprint.borelTransform μ z) := by ring
      _ = 0 := by rw [h]; simp
  have hformula : shiftedReciprocalDifference μ ν z =
      (AndersonAC.Blueprint.borelTransform ν z -
        AndersonAC.Blueprint.borelTransform μ z) /
        ((AndersonAC.Blueprint.borelTransform μ z + I) *
          (AndersonAC.Blueprint.borelTransform ν z + I)) := by
    unfold shiftedReciprocalDifference
    field_simp [hμ, hν]
    ring
  rw [hformula]
  exact div_ne_zero hnum (mul_ne_zero hμ hν)

/-- The shifted-reciprocal difference has zero boundary limit only on a null set, assuming the
bounded-holomorphic uniqueness principle. -/
theorem shiftedReciprocalDifference_zero_limit_null
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hUnique : ∀ f : ℂ → ℂ,
      DifferentiableOn ℂ f {z : ℂ | 0 < z.im} →
      (∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ M) →
      (∃ z : ℂ, 0 < z.im ∧ f z ≠ 0) →
      volume {x : ℝ | Filter.Tendsto
        (fun η : ℝ => f ((x : ℂ) + (η : ℂ) * I)) (𝓝[>] 0) (𝓝 0)} = 0)
    (hnonzero : ∃ z : ℂ, 0 < z.im ∧
      AndersonAC.Blueprint.borelTransform μ z -
        AndersonAC.Blueprint.borelTransform ν z ≠ 0) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ¬ Filter.Tendsto
        (fun y : ℝ => shiftedReciprocalDifference μ ν (verticalPath x y))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨z, hz, hneq⟩ := hnonzero
  have hdiff : DifferentiableOn ℂ (shiftedReciprocalDifference μ ν)
      {z : ℂ | 0 < z.im} := by
    simpa [upperHalfPlane] using shiftedReciprocalDifference_differentiableOn μ ν
  have hbounded : ∃ M : ℝ, ∀ z : ℂ, 0 < z.im →
      ‖shiftedReciprocalDifference μ ν z‖ ≤ M := by
    refine ⟨2, ?_⟩
    intro z hz
    exact shiftedReciprocalDifference_norm_le_two μ ν z hz
  have hne : ∃ z : ℂ, 0 < z.im ∧
      shiftedReciprocalDifference μ ν z ≠ 0 :=
    ⟨z, hz, shiftedReciprocalDifference_ne_zero μ ν z hz hneq⟩
  have hzero : volume {x : ℝ | Filter.Tendsto
      (fun η : ℝ => shiftedReciprocalDifference μ ν
        ((x : ℂ) + (η : ℂ) * I)) (𝓝[>] 0) (𝓝 0)} = 0 :=
    hUnique _ hdiff hbounded hne
  have hae := measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hae] with x hx
  simpa [verticalPath] using hx

/-- A finite boundary value of a Borel transform has nonnegative imaginary part. -/
theorem borelTransform_boundary_im_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ℝ) (w : ℂ)
    (hlim : AndersonAC.Blueprint.HasBoundary
      (AndersonAC.Blueprint.borelTransform μ) x w) : 0 ≤ w.im := by
  have hlim' : Filter.Tendsto
      (fun y : ℝ => (AndersonAC.Blueprint.borelTransform μ (verticalPath x y)).im)
      (𝓝[>] 0) (𝓝 w.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp (by
      simpa [verticalPath, AndersonAC.Blueprint.HasBoundary] using hlim)
  by_contra hw
  have hwlt : w.im < 0 := lt_of_not_ge hw
  have hneg : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      (AndersonAC.Blueprint.borelTransform μ (verticalPath x y)).im < 0 :=
    hlim'.eventually (Iio_mem_nhds hwlt)
  obtain ⟨y, hyneg, hypos⟩ := (hneg.and self_mem_nhdsWithin).exists
  exact (not_lt_of_ge (borelTransform_im_nonneg μ (verticalPath x y) (by
    simp [verticalPath]
    exact Set.mem_Ioi.mp hypos))) hyneg

/-- If both transforms have finite boundary values and the shifted-reciprocal difference has no
zero boundary limit on a positive-measure set, then the difference has a nonzero boundary value
almost everywhere. The zero-set premise is discharged by the integrated
`AndersonAC.HInf.volume_boundaryZero_eq_zero` theorem.
-/
theorem difference_nonzero_of_boundary_and_shiftedReciprocal_zero_ae
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∃ w : ℂ, AndersonAC.Blueprint.HasBoundary
        (AndersonAC.Blueprint.borelTransform μ) x w)
    (hν : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∃ w : ℂ, AndersonAC.Blueprint.HasBoundary
        (AndersonAC.Blueprint.borelTransform ν) x w)
    (hzero : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ¬ Filter.Tendsto
        (fun y : ℝ => shiftedReciprocalDifference μ ν (verticalPath x y))
        (𝓝[>] 0) (𝓝 0)) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∃ w : ℂ,
        AndersonAC.Blueprint.HasBoundary
          (fun z => AndersonAC.Blueprint.borelTransform μ z -
            AndersonAC.Blueprint.borelTransform ν z) x w ∧ w ≠ 0 := by
  filter_upwards [hμ, hν, hzero] with x hμx hνx hnotzero
  obtain ⟨u, hu⟩ := hμx
  obtain ⟨v, hv⟩ := hνx
  have huim : 0 ≤ u.im := borelTransform_boundary_im_nonneg μ x u hu
  have hvim : 0 ≤ v.im := borelTransform_boundary_im_nonneg ν x v hv
  have huDen : u + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hvDen : v + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hdiff : Filter.Tendsto
      (fun y : ℝ => AndersonAC.Blueprint.borelTransform μ (verticalPath x y) -
        AndersonAC.Blueprint.borelTransform ν (verticalPath x y))
      (𝓝[>] 0) (𝓝 (u - v)) := by
    simpa [verticalPath, AndersonAC.Blueprint.HasBoundary] using hu.sub hv
  by_cases huv : u = v
  · have huPlus : Filter.Tendsto
        (fun y : ℝ => AndersonAC.Blueprint.borelTransform μ (verticalPath x y) + I)
        (𝓝[>] 0) (𝓝 (u + I)) := by
      simpa [verticalPath] using hu.add_const I
    have hvPlus : Filter.Tendsto
        (fun y : ℝ => AndersonAC.Blueprint.borelTransform ν (verticalPath x y) + I)
        (𝓝[>] 0) (𝓝 (v + I)) := by
      simpa [verticalPath] using hv.add_const I
    have huInv : Filter.Tendsto
        (fun y : ℝ =>
          (AndersonAC.Blueprint.borelTransform μ (verticalPath x y) + I)⁻¹)
        (𝓝[>] 0) (𝓝 ((u + I)⁻¹)) :=
      (continuousAt_inv₀ huDen).tendsto.comp huPlus
    have hvInv : Filter.Tendsto
        (fun y : ℝ =>
          (AndersonAC.Blueprint.borelTransform ν (verticalPath x y) + I)⁻¹)
        (𝓝[>] 0) (𝓝 ((v + I)⁻¹)) :=
      (continuousAt_inv₀ hvDen).tendsto.comp hvPlus
    have hzeroLimit : Filter.Tendsto
        (fun y : ℝ => shiftedReciprocalDifference μ ν (verticalPath x y))
        (𝓝[>] 0) (𝓝 0) := by
      simpa [shiftedReciprocalDifference, huv] using huInv.sub hvInv
    exact (hnotzero hzeroLimit).elim
  · exact ⟨u - v, hdiff, sub_ne_zero.mpr huv⟩

/-- Nonzero boundary values for differences of finite Borel transforms, given their finite
boundary limits and the bounded-holomorphic zero-boundary uniqueness theorem. -/
theorem difference_nonzero_of_boundary_and_hinf
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∃ w : ℂ, AndersonAC.Blueprint.HasBoundary
        (AndersonAC.Blueprint.borelTransform μ) x w)
    (hν : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∃ w : ℂ, AndersonAC.Blueprint.HasBoundary
        (AndersonAC.Blueprint.borelTransform ν) x w)
    (hnonzero : ∃ z : ℂ, 0 < z.im ∧
      AndersonAC.Blueprint.borelTransform μ z -
        AndersonAC.Blueprint.borelTransform ν z ≠ 0) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∃ w : ℂ,
        AndersonAC.Blueprint.HasBoundary
          (fun z => AndersonAC.Blueprint.borelTransform μ z -
            AndersonAC.Blueprint.borelTransform ν z) x w ∧ w ≠ 0 := by
  exact difference_nonzero_of_boundary_and_shiftedReciprocal_zero_ae μ ν hμ hν
    (shiftedReciprocalDifference_zero_limit_null μ ν
      AndersonAC.HInf.volume_boundaryZero_eq_zero hnonzero)

/-- The complete `BoundaryInput` package follows from its finite-complex-boundary field: the
bounded-boundary criterion is already proved, and the nonzero-difference field follows from the
integrated H∞ uniqueness theorem above. -/
theorem boundary_proof_of_finite
    (hfinite : ∀ μ : Measure ℝ, IsFiniteMeasure μ →
      ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
        ∃ w : ℂ, AndersonAC.Blueprint.HasBoundary
          (AndersonAC.Blueprint.borelTransform μ) x w) :
    AndersonAC.Blueprint.BoundaryInput := by
  refine ⟨hfinite, boundedBoundaryCriterion_proof, ?_⟩
  intro μ ν hμ hν hnonzero
  exact @difference_nonzero_of_boundary_and_hinf μ ν hμ hν
    (hfinite μ hμ) (hfinite ν hν) hnonzero

end AndersonAC.Boundary
