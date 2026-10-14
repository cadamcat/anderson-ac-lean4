import AndersonAC.S3.Definitions

/-! Exact finite-grid identities at the scalar fixed point, §3 lines 405–409. -/

noncomputable section
open scoped BigOperators

namespace AndersonAC.S3

variable {d L : ℕ} [NeZero L]

theorem grid_resolvent_im (E t : ℝ) (r : ℂ) (k : Torus d L) :
    (gridResolvent E t r k).im = t * r.im * ‖gridResolvent E t r k‖ ^ 2 := by
  unfold gridResolvent
  rw [Complex.inv_im, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_sub, mul_zero, zero_add]
  ring

theorem initial_normalization (hL : 4 ≤ L) (E t : ℝ) (r : ℂ)
    (ht : 0 < t) (hp : 0 < r.im) (hr : scalarMap (d := d) (L := L) E t r = r) :
    t * gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖ ^ 2) = 1 := by
  have him := congrArg Complex.im hr
  have havg : (scalarMap (d := d) (L := L) E t r).im =
      t * r.im * gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖ ^ 2) := by
    unfold scalarMap gridAvg gridAvgReal
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
    change (Fintype.card (Torus d L) : ℝ)⁻¹ *
      Complex.imAddGroupHom (∑ k : Torus d L, gridResolvent E t r k) = _
    rw [map_sum]
    change (Fintype.card (Torus d L) : ℝ)⁻¹ *
      (∑ k : Torus d L, (gridResolvent E t r k).im) = _
    simp_rw [grid_resolvent_im]
    rw [← Finset.mul_sum]
    ring
  rw [havg] at him
  apply (mul_left_cancel₀ hp.ne')
  calc
    r.im * (t * gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖ ^ 2)) = r.im := by
      nlinarith [him]
    _ = r.im * 1 := by ring

end AndersonAC.S3
