import AndersonAC.S9.Averaging
import AndersonAC.S9.IntervalSample

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace AndersonAC.SolS9

theorem uniformInterval_cauchy_bound (a b x y : ℝ) (hab : a < b) (hy : 0 < y) :
    (∫ s, cauchyKernel x y s ∂AndersonAC.Blueprint.uniformInterval a b) ≤
      Real.pi / (b - a) := by
  have hint : Integrable (cauchyKernel x y) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_cauchyKernel x y hy]
    exact Real.pi_ne_zero
  have hnonneg : ∀ s : ℝ, 0 ≤ cauchyKernel x y s := by
    intro s
    unfold cauchyKernel
    positivity
  have harea : (∫ s in Set.Icc a b, cauchyKernel x y s) ≤ Real.pi :=
    (integral_mono_measure Measure.restrict_le_self (ae_of_all _ hnonneg) hint).trans_eq
      (integral_cauchyKernel x y hy)
  rw [AndersonAC.Blueprint.uniformInterval, integral_smul_measure]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_pos.mpr hab).le, smul_eq_mul]
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left harea (inv_nonneg.mpr (sub_pos.mpr hab).le)

theorem imaginary_cavity_kernel (w : ℂ) (s : ℝ) :
    (((s : ℂ) - w)⁻¹).im = cauchyKernel w.re w.im s := by
  simp [Complex.inv_im, Complex.normSq_apply, cauchyKernel, pow_two]

end AndersonAC.SolS9
