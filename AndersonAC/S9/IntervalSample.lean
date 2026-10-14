import AndersonAC.S9.Core

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace AndersonAC.SolS9

abbrev IntervalSample (a b : ℝ) := Set.Icc a b

def intervalSampleLaw (a b : ℝ) : Measure (IntervalSample a b) :=
  letI : MeasureSpace (IntervalSample a b) := Measure.Subtype.measureSpace
  (ENNReal.ofReal (b - a))⁻¹ • volume

theorem intervalSampleLaw_probability (a b : ℝ) (hab : a < b) :
    IsProbabilityMeasure (intervalSampleLaw a b) := by
  letI : MeasureSpace (IntervalSample a b) := Measure.Subtype.measureSpace
  constructor
  change ((ENNReal.ofReal (b - a))⁻¹ • volume) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))) ENNReal.ofReal_ne_top

theorem intervalSampleLaw_map (a b : ℝ) :
    (intervalSampleLaw a b).map (fun s : IntervalSample a b => (s : ℝ)) =
      AndersonAC.Blueprint.uniformInterval a b := by
  letI : MeasureSpace (IntervalSample a b) := Measure.Subtype.measureSpace
  rw [intervalSampleLaw, Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  congr 1
  exact (measurePreserving_subtype_coe measurableSet_Icc).map_eq

end AndersonAC.SolS9
