import AndersonAC.S9.HelperStatements
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Construct the averaged spectral measure before taking the Poisson
bound to the underlying Borel measure. The sharp domination principle is
an explicit helper contract, not an owned hole. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AndersonAC.SolS9

theorem averaging_from_transform_bound {Own : Type*} [MeasurableSpace Own]
    (D : BoundedPoissonMeasureInput) (ρlaw : Measure Own) [IsProbabilityMeasure ρlaw]
    (μ : Own → Measure ℝ)
    (hmeas : ∀ A : Set ℝ, MeasurableSet A → Measurable (fun s => μ s A))
    (hprob : ∀ s, IsProbabilityMeasure (μ s)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ E η : ℝ, 0 < η →
      (∫ s, (borelTransform (μ s) ((E : ℂ) + η * Complex.I)).im ∂ρlaw) ≤ Real.pi * C)
    (A : Set ℝ) (hA : MeasurableSet A) :
    ∫⁻ s, μ s A ∂ρlaw ≤ ENNReal.ofReal C * volume A := by
  let κ : Kernel Own ℝ :=
    { toFun := μ, measurable' := Measure.measurable_of_measurable_coe μ hmeas }
  letI : IsMarkovKernel κ := ⟨hprob⟩
  let ν : Measure ℝ := κ ∘ₘ ρlaw
  have hνprob : IsProbabilityMeasure ν := inferInstance
  letI : IsProbabilityMeasure ν := hνprob
  have htransform : ∀ z : ℂ, 0 < z.im →
      borelTransform ν z = ∫ s, borelTransform (μ s) z ∂ρlaw ∧
        Integrable (fun s => borelTransform (μ s) z) ρlaw := by
    intro z hz
    have hzsupport : z ∉ (algebraMap ℝ ℂ) '' ν.support := by
      rintro ⟨t, _, heq⟩
      have hi := hz
      rw [← heq] at hi
      simp at hi
    have hint : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) ν := by
      have hi := MeasureTheory.integrable_resolvent hzsupport
      convert hi using 1
      funext t
      simp [resolvent, Ring.inverse_eq_inv']
    have hint' : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹)
        ((κ ∘ₖ Kernel.const Unit ρlaw) ()) := by
      simpa [← Measure.comp_eq_comp_const_apply] using hint
    constructor
    · have heq := Kernel.integral_comp hint'
      simpa [← Measure.comp_eq_comp_const_apply, Kernel.const_apply, κ, ν,
        borelTransform, AndersonAC.Blueprint.borelTransform] using heq
    · have hi := hint'.integral_comp
      simpa [Kernel.const_apply, κ, borelTransform,
        AndersonAC.Blueprint.borelTransform] using hi
  have hdom : ν ≤ ENNReal.ofReal C • volume := by
    apply D ν (inferInstance) C hC
    intro E η hη
    have hz : 0 < ((E : ℂ) + η * Complex.I).im := by simpa using hη
    obtain ⟨heq, hint⟩ := htransform _ hz
    change (borelTransform ν ((E : ℂ) + η * Complex.I)).im ≤ Real.pi * C
    rw [heq]
    change RCLike.im (∫ s, borelTransform (μ s) ((E : ℂ) + η * Complex.I) ∂ρlaw) ≤ Real.pi * C
    rw [← integral_im hint]
    exact hbound E η hη
  calc
    (∫⁻ s, μ s A ∂ρlaw) = ν A :=
      (Measure.bind_apply hA (Measure.measurable_of_measurable_coe μ hmeas).aemeasurable).symm
    _ ≤ (ENNReal.ofReal C • volume) A := (Measure.le_iff'.mp hdom) A
    _ = ENNReal.ofReal C * volume A := by rw [Measure.smul_apply, smul_eq_mul]

end AndersonAC.SolS9
