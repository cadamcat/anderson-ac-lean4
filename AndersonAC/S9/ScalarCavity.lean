import AndersonAC.S9.RankOne

noncomputable section

namespace AndersonAC.SolS9

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def rankOneCavity (T : K →L[ℂ] K) (v : K) (z : ℂ) : ℂ :=
  -(inner ℂ v (operatorResolvent T z v))⁻¹

theorem rankOneCavity_im_pos (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (v : K) (hv : v ≠ 0) (z : ℂ) (hz : 0 < z.im) :
    0 < (rankOneCavity T v z).im := by
  have hg := resolvent_im_pos T hT z hz v hv
  have hne : inner ℂ v (operatorResolvent T z v) ≠ 0 := by
    intro hzero
    simp [hzero] at hg
  simp only [rankOneCavity, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hg (Complex.normSq_pos.mpr hne)

theorem rank_one_cavity_identity (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (v : K) (hv : ‖v‖ = 1) (h : ℝ) (z : ℂ) (hz : 0 < z.im) :
    inner ℂ v (operatorResolvent (T + (h : ℂ) • InnerProductSpace.rankOne ℂ v v) z v) =
      ((h : ℂ) - rankOneCavity T v z)⁻¹ := by
  let g := inner ℂ v (operatorResolvent T z v)
  have hvne : v ≠ 0 := by
    intro heq
    have hzero : (0 : ℝ) = 1 := by simpa [heq] using hv
    exact zero_ne_one hzero
  have hg : 0 < g.im := resolvent_im_pos T hT z hz v hvne
  have hgn : g ≠ 0 := by intro heq; simp [heq] at hg
  have hd : 1 + (h : ℂ) * g ≠ 0 := by
    by_cases hh : h = 0
    · simp [hh]
    intro heq
    have hi := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at hi
    exact (mul_ne_zero hh hg.ne') hi
  have hd2 : (h : ℂ) + g⁻¹ ≠ 0 := by
    have heq : ((h : ℂ) + g⁻¹) * g = 1 + (h : ℂ) * g := by
      field_simp [hgn]
      ring
    intro hzero
    rw [hzero, zero_mul] at heq
    exact hd heq.symm
  rw [scalar_rank_one_resolvent T hT v hv h z hz]
  change g / (1 + (h : ℂ) * g) = ((h : ℂ) - -g⁻¹)⁻¹
  rw [sub_neg_eq_add]
  field_simp [hgn, hd, hd2]
  simp [add_comm]

end AndersonAC.SolS9
