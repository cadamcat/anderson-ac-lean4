import AndersonAC.S6.Statements
import AndersonAC.S6Core.CoreResolvent
import AndersonAC.S2.WardAlgebra
import AndersonAC.AgentS6.WardRow

/-! Deterministic inverse identities and the scaled Ward row estimate of §6. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
open AndersonAC.S6
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixImag_diag_re (g : Matrix ι ι ℂ) (i : ι) :
    (matrixImag g i i).re = (g i i).im := by
  have h := congrArg Complex.re (AndersonAC.SolS2.complex_imaginary_difference (g i i))
  simpa only [matrixImag, AndersonAC.Blueprint.matrixImag, Matrix.smul_apply,
    smul_eq_mul, Matrix.sub_apply, Matrix.conjTranspose_apply,
    div_eq_mul_inv, one_mul, Complex.star_def, Complex.ofReal_re] using h

theorem weighted_ward_diagonal (t : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ)
    (hWard : (t : ℂ) • (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ) = matrixImag g)
    (i : ι) : t * ∑ j, p j * ‖g i j‖ ^ 2 = (g i i).im := by
  have hentry : ((g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ) i i).re =
      ∑ j, p j * ‖g i j‖ ^ 2 := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Complex.re_sum, Complex.star_def]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.sq_norm]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have h := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) hWard
  simpa only [Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hentry, matrixImag_diag_re] using h

theorem scaled_ward_row_bound (t c K : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ)
    (ht : 0 < t) (hc : 0 < c) (hp : ∀ i, c ≤ p i)
    (hdiag : ∀ i, ‖g i i‖ ≤ K)
    (hWard : (t : ℂ) • (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ) = matrixImag g) :
    Planned.ward_row_bound t c K p g ht hc hp hdiag hWard := by
  intro i
  have hmass : ∑ j, p j * ‖scaledInverse t g i j‖ ^ 2 = (g i i).im := by
    rw [← AndersonAC.SolS6.weighted_ward_diagonal t p g hWard i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [scaledInverse, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht.le]
    ring
  refine ⟨hmass, (le_div_iff₀ hc).mpr ?_⟩
  calc
    sqRow (scaledInverse t g) i * c = ∑ j, c * ‖scaledInverse t g i j‖ ^ 2 := by
      simp only [sqRow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j, p j * ‖scaledInverse t g i j‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hp j) (sq_nonneg _)
    _ = (g i i).im := hmass
    _ ≤ ‖g i i‖ := Complex.im_le_norm _
    _ ≤ K := hdiag i

end AndersonAC.SolS6

namespace AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem core_resolvent (g : Matrix (B ⊕ R) (B ⊕ R) ℂ) (V : Matrix B B ℂ)
    (hg : IsUnit g.det) (hV : IsUnit V.det)
    (hnew : IsUnit (g⁻¹ + Matrix.fromBlocks V 0 0 0).det) :
    Planned.core_resolvent g V hg hV hnew :=
  AndersonAC.SolS6.coreResolvent_proof B R g V hg hV hnew

end AndersonAC.S6
#print axioms AndersonAC.SolS6.scaled_ward_row_bound
#print axioms AndersonAC.S6.ward_row_bound
#print axioms AndersonAC.S6.core_resolvent
