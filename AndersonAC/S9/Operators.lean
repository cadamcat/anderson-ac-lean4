import AndersonAC.S9.Core

/-! Infinite-dimensional resolvent and rank-one algebra for §9.
The paper uses `(T-z)⁻¹`; no finite-matrix identity substitutes for this
operator identity. -/

noncomputable section

namespace AndersonAC.SolS9

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def operatorResolvent (T : K →L[ℂ] K) (z : ℂ) : K →L[ℂ] K :=
  Ring.inverse (T - z • (1 : K →L[ℂ] K))

theorem operator_shift_isUnit (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) : IsUnit (T - z • (1 : K →L[ℂ] K)) := by
  have hnot : z ∉ spectrum ℂ T := by
    intro h
    exact hz.ne' (hT.im_eq_zero_of_mem_spectrum h)
  have hunit := (spectrum.notMem_iff.mp hnot).neg
  simpa only [neg_sub, Algebra.algebraMap_eq_smul_one] using hunit

end AndersonAC.SolS9
