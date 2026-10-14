import AndersonAC.AgentS6Conc.Support

noncomputable section
open MeasureTheory
open scoped NNReal

namespace AndersonAC.AgentS6Conc

/-- Conditioning on a measurable set in the conditioning sigma-algebra leaves
conditional expectations unchanged on the restricted measure. -/
theorem condExp_scaledRestrict_ae_eq {Ω E : Type*} {m mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → E} (hm : m ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[m] A) {c : ℝ≥0} (hf : Integrable f μ) :
    (c • μ.restrict A)[f | m] =ᵐ[c • μ.restrict A] μ[f | m] := by
  have hscale := condExp_smulMeasure_ae_eq (μ := μ.restrict A) hm (c := c) (hf.restrict)
  have hrest := condExp_restrict_ae_eq_restrict (μ := μ) hm hA hf
  have hrest' : (μ.restrict A)[f | m] =ᵐ[c • μ.restrict A] μ[f | m] :=
    hrest.filter_mono (Measure.ae_smul_measure_le c)
  exact hscale.trans hrest'

end AndersonAC.AgentS6Conc

end
