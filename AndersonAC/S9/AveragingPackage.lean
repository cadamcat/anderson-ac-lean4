import AndersonAC.S9.SharpPoisson
import AndersonAC.S9Kern.CompactMomentKernel
import AndersonAC.Blueprint.Interfaces
import AndersonAC.S9.Resolution
import AndersonAC.S9.ScalarCavity
import AndersonAC.S9.RankOneKernel
import AndersonAC.S9.IntervalAveraging
import AndersonAC.S9.MeasureAveraging

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal

namespace AndersonAC.SolS9

theorem averaging_of_measure_inputs (D : BoundedPoissonMeasureInput)
    (CM : CompactMomentKernelInput) : AndersonAC.Blueprint.AveragingInput := by
  intro d T hT v hv a b hab S A hA
  let L := intervalSampleLaw a b
  letI : IsProbabilityMeasure L := intervalSampleLaw_probability a b hab
  have hP : IsSelfAdjoint (InnerProductSpace.rankOne ℂ v v) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    simp [InnerProductSpace.rankOne_apply, inner_smul_left, inner_smul_right,
      inner_conj_symm, mul_comm]
  have hTs : ∀ s : ℝ, IsSelfAdjoint (T + (s : ℂ) • InnerProductSpace.rankOne ℂ v v) := by
    intro s
    exact hT.add ((show IsSelfAdjoint (s : ℂ) from Complex.conj_ofReal s).smul hP)
  have hvne : v ≠ 0 := by
    intro heq
    have hzero : (0 : ℝ) = 1 := by simpa [heq] using hv
    exact zero_ne_one hzero
  rw [← intervalSampleLaw_map a b,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).lintegral_map]
  rw [← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab)]
  apply averaging_from_transform_bound D L
    (fun s : IntervalSample a b => (S s).vectorMeasure v)
    (fun B hB => rank_one_interval_kernel CM T v hv a b S B hB)
  · intro s
    constructor
    rw [(S s).vectorMeasure_univ v, hv]
    norm_num
  · exact inv_nonneg.mpr (sub_pos.mpr hab).le
  · intro E η hη
    let z : ℂ := (E : ℂ) + η * Complex.I
    have hz : 0 < z.im := by simpa [z] using hη
    let w := rankOneCavity T v z
    have hw : 0 < w.im := rankOneCavity_im_pos T hT v hvne z hz
    have heq : (fun s : IntervalSample a b => (borelTransform ((S s).vectorMeasure v) z).im) =
        (fun s : IntervalSample a b => cauchyKernel w.re w.im (s : ℝ)) := by
      funext s
      have hr := ResolutionTransformInput_proof d
        (T + ((s : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ v v) (hTs s) (S s) v z hz
      change inner ℂ v (operatorResolvent
        (T + ((s : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ v v) z v) =
          borelTransform ((S s).vectorMeasure v) z at hr
      rw [← hr, rank_one_cavity_identity T hT v hv (s : ℝ) z hz]
      exact imaginary_cavity_kernel w (s : ℝ)
    rw [heq]
    have hmap := (MeasurableEmbedding.subtype_coe measurableSet_Icc).integral_map
      (μ := L) (cauchyKernel w.re w.im)
    rw [intervalSampleLaw_map a b] at hmap
    rw [← hmap]
    simpa [div_eq_mul_inv, mul_comm] using uniformInterval_cauchy_bound a b w.re w.im hab hw
  · exact hA

end AndersonAC.SolS9

namespace AndersonAC.Blueprint.Packages

-- Discharges exactly spectral averaging package, with both measure-theoretic inputs proved.
theorem averaging : AveragingInput :=
  AndersonAC.SolS9.averaging_of_measure_inputs
    AndersonAC.SolS9.boundedPoisson_from_finite
    AndersonAC.SolS9.CompactMomentKernelInput_proof


end AndersonAC.Blueprint.Packages
