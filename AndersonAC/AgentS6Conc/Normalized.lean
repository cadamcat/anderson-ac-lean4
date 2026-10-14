import AndersonAC.AgentS6Conc.Support

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace AndersonAC.AgentS6Conc

def normalizedRestrict {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) :
    Measure Ω := ((μ A).toNNReal)⁻¹ • μ.restrict A

theorem ae_normalizedRestrict_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) :
    ∀ᵐ ω ∂normalizedRestrict μ A, P ω := by
  have hRestrict : ∀ᵐ ω ∂μ.restrict A, P ω := ae_restrict_of_ae hP
  exact hRestrict.filter_mono (Measure.ae_smul_measure_le ((μ A).toNNReal⁻¹))

theorem isProbabilityMeasure_normalizedRestrict {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Set Ω}
    (_hA : MeasurableSet A) (hApos : μ A ≠ 0) :
    IsProbabilityMeasure (normalizedRestrict μ A) := by
  apply isProbabilityMeasure_iff.mpr
  have hAtop : μ A ≠ ∞ := measure_ne_top μ A
  have htoNNpos : 0 < (μ A).toNNReal := ENNReal.toNNReal_pos hApos hAtop
  have htoNNne : (μ A).toNNReal ≠ 0 := htoNNpos.ne'
  have hcoeff : (((μ A).toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) = (μ A)⁻¹ := by
    rw [ENNReal.coe_inv htoNNne, ENNReal.coe_toNNReal hAtop]
  rw [normalizedRestrict, Measure.smul_apply, Measure.restrict_apply_univ, ENNReal.smul_def,
    hcoeff]
  exact ENNReal.inv_mul_cancel hApos hAtop

theorem normalizedRestrict_event_le_real {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A E : Set Ω}
    (_hA : MeasurableSet A) (hE : MeasurableSet E) (hApos : μ A ≠ 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hprob : normalizedRestrict μ A E ≤ ENNReal.ofReal B) :
    μ.real (E ∩ A) ≤ B * μ.real A := by
  have hAtop : μ A ≠ ∞ := measure_ne_top μ A
  have htoNNpos : 0 < (μ A).toNNReal := ENNReal.toNNReal_pos hApos hAtop
  have htoNNne : (μ A).toNNReal ≠ 0 := htoNNpos.ne'
  have hcoeff : (((μ A).toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) = (μ A)⁻¹ := by
    rw [ENNReal.coe_inv htoNNne, ENNReal.coe_toNNReal hAtop]
  have happly : normalizedRestrict μ A E =
      (μ A)⁻¹ * μ (E ∩ A) := by
    simp [normalizedRestrict, Measure.smul_apply, Measure.restrict_apply hE,
      ENNReal.smul_def, hcoeff]
  have hmul : μ (E ∩ A) = μ A * normalizedRestrict μ A E := by
    calc
      μ (E ∩ A) = μ A * ((μ A)⁻¹ * μ (E ∩ A)) :=
        (ENNReal.mul_inv_cancel_left hApos hAtop).symm
      _ = μ A * normalizedRestrict μ A E := by rw [happly]
  have hmul_le : μ (E ∩ A) ≤ μ A * ENNReal.ofReal B := by
    rw [hmul]
    gcongr
  have hmulTop : μ A * ENNReal.ofReal B ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top μ A) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hmulTop hmul_le
  simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, mul_comm] using hreal

end AndersonAC.AgentS6Conc

end
