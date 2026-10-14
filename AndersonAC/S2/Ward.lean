import AndersonAC.S2.Definitions
import AndersonAC.S2Inv.InverseCore

/-! Dissipative finite matrices and Ward algebra from §2. -/

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator ComplexOrder

namespace AndersonAC.SolS2
open AndersonAC.S2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realMatrix_hermitian (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    (realMatrix M).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, realMatrix, Complex.star_def, Complex.conj_ofReal, hM.apply i j]

theorem pairing_smul_right (c : ℂ) (x y : ι → ℂ) : pairing x (c • y) = c * pairing x y := by
  simp [pairing, Finset.mul_sum, mul_left_comm, mul_assoc]

theorem pairing_diagonal_im (r x : ι → ℂ) :
    (pairing x ((Matrix.diagonal r).mulVec x)).im = ∑ i, (r i).im * ‖x i‖ ^ 2 := by
  simp only [pairing, Matrix.mulVec_diagonal, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (conj (x i) * (r i * x i)).im = _
  rw [Complex.sq_norm]
  change (conj (x i) * (r i * x i)).im =
    (r i).im * ((x i).re * (x i).re + (x i).im * (x i).im)
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem damped_pairing_im (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    (t : ℝ) (r x : ι → ℂ) :
    (pairing x ((dampedMatrix M t r).mulVec x)).im =
      -t * ∑ i, (r i).im * ‖x i‖ ^ 2 := by
  have hreal : (pairing x ((realMatrix M).mulVec x)).im = 0 := by
    have hh := (realMatrix_hermitian M hM).im_star_dotProduct_mulVec_self x
    change (pairing x ((realMatrix M).mulVec x)).im = 0 at hh
    exact hh
  rw [dampedMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    pairing_sub_right, pairing_smul_right, Complex.sub_im, hreal,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    pairing_diagonal_im]
  ring

theorem damped_kernel_zero (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    {t : ℝ} (ht : 0 < t) (r : ι → ℂ) (hp : ∀ i, 0 < (r i).im)
    (x : ι → ℂ) (hx : (dampedMatrix M t r).mulVec x = 0) : x = 0 := by
  have him := damped_pairing_im M hM t r x
  rw [hx] at him
  simp only [pairing, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_im] at him
  have hs : (∑ i, (r i).im * ‖x i‖ ^ 2) = 0 := by
    have htne : -t ≠ 0 := neg_ne_zero.mpr ht.ne'
    exact (mul_eq_zero.mp him.symm).resolve_left htne
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (r i).im * ‖x i‖ ^ 2 :=
    fun i hi => mul_nonneg (hp i).le (sq_nonneg _)
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs
  funext i
  have hnorm : ‖x i‖ ^ 2 = 0 := (mul_eq_zero.mp (hterms i (Finset.mem_univ i))).resolve_left (hp i).ne'
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x i)])

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem damped_invertible (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    {t : ℝ} (ht : 0 < t) (r : ι → ℂ) (hp : ∀ i, 0 < (r i).im) :
    IsUnit (dampedMatrix M t r) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : (dampedMatrix M t r).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (damped_kernel_zero M hM ht r hp (x - y) hz)

end AndersonAC.S2
