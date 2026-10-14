import AndersonAC.S9.IntervalSample
import AndersonAC.S9.HelperStatements

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9

theorem rank_one_interval_kernel (CM : CompactMomentKernelInput)
    {d : ℕ} (T : StateSpace d →L[ℂ] StateSpace d) (v : StateSpace d) (hv : ‖v‖ = 1)
    (a b : ℝ)
    (S : ∀ s : ℝ, SpectralResolution (T + (s : ℂ) • InnerProductSpace.rankOne ℂ v v))
    (A : Set ℝ) (hA : MeasurableSet A) :
    Measurable (fun s : IntervalSample a b => (S s).vectorMeasure v A) := by
  let P := InnerProductSpace.rankOne ℂ v v
  let M := ‖T‖ + max |a| |b|
  have hM : 0 ≤ M := add_nonneg (norm_nonneg T)
    ((abs_nonneg a).trans (le_max_left _ _))
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro w
    change ‖inner ℂ v w • v‖ ≤ 1 * ‖w‖
    rw [norm_smul, hv, mul_one, one_mul]
    simpa [hv] using norm_inner_le_norm v w
  have hnorm : ∀ s : IntervalSample a b, ‖T + (s : ℂ) • P‖ ≤ M := by
    intro s
    have hsabs : |(s : ℝ)| ≤ max |a| |b| := by
      apply abs_le.mpr
      constructor
      · exact (neg_le_neg (le_max_left |a| |b|)).trans
          ((neg_abs_le a).trans s.property.1)
      · exact s.property.2.trans ((le_abs_self b).trans (le_max_right _ _))
    calc
      ‖T + (s : ℂ) • P‖ ≤ ‖T‖ + ‖(s : ℂ) • P‖ := norm_add_le _ _
      _ = ‖T‖ + |(s : ℝ)| * ‖P‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖T‖ + |(s : ℝ)| := by
        simpa [add_comm] using add_le_add_left
          (mul_le_of_le_one_right (abs_nonneg (s : ℝ)) hP) ‖T‖
      _ ≤ M := by simpa [M, add_comm] using add_le_add_left hsabs ‖T‖
  apply CM (IntervalSample a b) (fun s => (S s).vectorMeasure v) M hM
  · intro s
    constructor
    rw [(S s).vectorMeasure_univ v, hv]
    norm_num
  · intro s
    have hsub : Set.Icc (-‖T + (s : ℂ) • P‖) ‖T + (s : ℂ) • P‖ ⊆ Set.Icc (-M) M :=
      Set.Icc_subset_Icc (neg_le_neg (hnorm s)) (hnorm s)
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) ((S s).vectorMeasure_supported v)
  · intro n
    have heq : (fun s : IntervalSample a b => ∫ t : ℝ, t ^ n ∂(S s).vectorMeasure v) =
        (fun s : IntervalSample a b => (inner ℂ v (((T + ((s : ℝ) : ℂ) • P) ^ n) v)).re) := by
      funext s
      exact (S s).vectorMeasure_moments v n
    rw [heq]
    have hc : Continuous (fun s : IntervalSample a b =>
        (inner ℂ v (((T + ((s : ℝ) : ℂ) • P) ^ n) v)).re) := by fun_prop
    exact hc.measurable
  · exact hA

end AndersonAC.SolS9
