import AndersonAC.S9.OperatorWard

noncomputable section

namespace AndersonAC.SolS9

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem resolvent_im_pos (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) (v : K) (hv : v ≠ 0) :
    0 < (inner ℂ v (operatorResolvent T z v)).im := by
  have hne : operatorResolvent T z v ≠ 0 := by
    intro hzero
    have hcancel := Ring.mul_inverse_cancel (T - z • (1 : K →L[ℂ] K))
      (operator_shift_isUnit T hT z hz)
    have heq : (T - z • (1 : K →L[ℂ] K)) (operatorResolvent T z v) = v := by
      simpa only [operatorResolvent, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
        using congrArg (fun f : K →L[ℂ] K => f v) hcancel
    rw [hzero, map_zero] at heq
    exact hv heq.symm
  rw [resolvent_ward T hT z hz v]
  exact mul_pos hz (sq_pos_of_pos (norm_pos_iff.mpr hne))

end AndersonAC.SolS9
