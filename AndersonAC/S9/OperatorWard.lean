import AndersonAC.S9.Operators

noncomputable section

namespace AndersonAC.SolS9

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The scalar Ward identity for the true resolvent on a complete Hilbert
space. It gives strict positivity for a nonzero vector and the resolvent
norm bound used in the rank-one argument. -/
theorem resolvent_ward (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) (v : K) :
    (inner ℂ v (operatorResolvent T z v)).im =
      z.im * ‖operatorResolvent T z v‖ ^ 2 := by
  let w := operatorResolvent T z v
  have hunit := operator_shift_isUnit T hT z hz
  have hcancel := Ring.mul_inverse_cancel (T - z • (1 : K →L[ℂ] K)) hunit
  have hvec : T w - z • w = v := by
    have h := congrArg (fun f : K →L[ℂ] K => f v) hcancel
    simpa [w, operatorResolvent, ContinuousLinearMap.mul_apply] using h
  have him : (inner ℂ (T w) w).im = 0 :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT).im_inner_apply_self w
  change (inner ℂ v w).im = z.im * ‖w‖ ^ 2
  calc
    (inner ℂ v w).im = (inner ℂ (T w - z • w) w).im := by rw [hvec]
    _ = z.im * ‖w‖ ^ 2 := by
      simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K,
        Complex.mul_im, ← Complex.ofReal_pow, him, mul_comm]

end AndersonAC.SolS9
