import AndersonAC.S9.OperatorPositive

noncomputable section

namespace AndersonAC.SolS9

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem scalar_rank_one_resolvent (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (v : K) (hv : ‖v‖ = 1) (h : ℝ) (z : ℂ) (hz : 0 < z.im) :
    inner ℂ v (operatorResolvent (T + (h : ℂ) • InnerProductSpace.rankOne ℂ v v) z v) =
      inner ℂ v (operatorResolvent T z v) /
        (1 + (h : ℂ) * inner ℂ v (operatorResolvent T z v)) := by
  have hP : IsSelfAdjoint (InnerProductSpace.rankOne ℂ v v) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro a b
    simp [InnerProductSpace.rankOne_apply, inner_smul_left, inner_smul_right,
      inner_conj_symm, mul_comm]
  let Th := T + (h : ℂ) • InnerProductSpace.rankOne ℂ v v
  have hTh : IsSelfAdjoint Th := hT.add
    ((show IsSelfAdjoint (h : ℂ) from Complex.conj_ofReal h).smul hP)
  let u := operatorResolvent Th z v
  let g := inner ℂ v (operatorResolvent T z v)
  let gh := inner ℂ v u
  have hA : IsUnit (T - z • (1 : K →L[ℂ] K)) := operator_shift_isUnit T hT z hz
  have hAh : IsUnit (Th - z • (1 : K →L[ℂ] K)) := operator_shift_isUnit Th hTh z hz
  have hAh_eval : Th u - z • u = v := by
    have hcancel := Ring.mul_inverse_cancel (Th - z • (1 : K →L[ℂ] K)) hAh
    simpa [u, operatorResolvent, ContinuousLinearMap.mul_apply] using
      congrArg (fun f : K →L[ℂ] K => f v) hcancel
  have hAu : (T - z • (1 : K →L[ℂ] K)) u = v - ((h : ℂ) * gh) • v := by
    apply eq_sub_of_add_eq
    change T u - z • u + ((h : ℂ) * gh) • v = v
    have hEval : T u + ((h : ℂ) * gh) • v - z • u = v := by
      have heval := hAh_eval
      change T u + (h : ℂ) • (inner ℂ v u • v) - z • u = v at heval
      rw [smul_smul] at heval
      simpa only [gh] using heval
    convert hEval using 1 <;> abel
  have hG_eval : operatorResolvent T z ((T - z • (1 : K →L[ℂ] K)) u) = u := by
    have hcancel := Ring.inverse_mul_cancel (T - z • (1 : K →L[ℂ] K)) hA
    simpa [operatorResolvent, ContinuousLinearMap.mul_apply] using
      congrArg (fun f : K →L[ℂ] K => f u) hcancel
  have hvec : u = operatorResolvent T z v - ((h : ℂ) * gh) • operatorResolvent T z v := by
    have hvec := congrArg (fun w => operatorResolvent T z w) hAu
    rw [hG_eval, map_sub, map_smul] at hvec
    exact hvec
  have hscalar : gh = g - ((h : ℂ) * gh) * g := by
    have hi := congrArg (fun w => inner ℂ v w) hvec
    simpa only [inner_sub_right, inner_smul_right] using hi
  have hvne : v ≠ 0 := by
    intro heq
    have hzero : (0 : ℝ) = 1 := by simpa [heq] using hv
    exact zero_ne_one hzero
  have hgim : 0 < g.im := resolvent_im_pos T hT z hz v hvne
  have hden : 1 + (h : ℂ) * g ≠ 0 := by
    by_cases hh : h = 0
    · simp [hh]
    intro heq
    have hi := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at hi
    exact (mul_ne_zero hh hgim.ne') hi
  change gh = g / (1 + (h : ℂ) * g)
  apply (eq_div_iff hden).mpr
  linear_combination hscalar

end AndersonAC.SolS9
