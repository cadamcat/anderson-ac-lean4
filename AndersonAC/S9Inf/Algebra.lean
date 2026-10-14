import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring

/-! The two algebraic steps in the fixed-energy positivity propagation
argument, `09-spectral.tex:432–448`. No boundary or spectral input is used. -/

noncomputable section

open Matrix

namespace AndersonAC.SolS9

theorem boundary_psd_zero_diagonal_proof (g a k : ℂ) (hkim : k.im = 0)
    (hpsd : (Matrix.of (fun i j : Fin 2 =>
      if i = 0 then (if j = 0 then g.im else a.im)
      else (if j = 0 then a.im else k.im))).PosSemidef) : a.im = 0 := by
  have hzero := hpsd.dotProduct_mulVec_zero_iff (x := ![(0 : ℝ), 1])
  have hform : star ![(0 : ℝ), 1] ⬝ᵥ
      (Matrix.of (fun i j : Fin 2 =>
        if i = 0 then (if j = 0 then g.im else a.im)
        else (if j = 0 then a.im else k.im))) *ᵥ ![0, 1] = 0 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hkim]
  have hcol := congrFun (hzero.mp hform) 0
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hcol

theorem rank_one_imaginary_part_proof (g : ℂ) (a h : ℝ) (hg : 0 < g.im)
    (ha : a ≠ 0) (hh : h ≠ 0) :
    0 < (-(h : ℂ) * (a : ℂ) ^ 2 / (1 + (h : ℂ) * g)).im := by
  have hne : 1 + (h : ℂ) * g ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at him
    exact (mul_ne_zero hh hg.ne') him
  have hnum : -(h : ℂ) * (a : ℂ) ^ 2 = ((-h * a ^ 2 : ℝ) : ℂ) := by
    simp
  rw [hnum, Complex.div_im]
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.add_im, Complex.one_im,
    Complex.mul_im, zero_mul, add_zero, zero_add]
  have hpos : 0 < h ^ 2 * a ^ 2 * g.im :=
    mul_pos (mul_pos (sq_pos_of_ne_zero hh) (sq_pos_of_ne_zero ha)) hg
  convert div_pos hpos (Complex.normSq_pos.mpr hne) using 1
  ring

end AndersonAC.SolS9
