import Mathlib

open Matrix WithLp
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace AndersonAC.SolS78

-- These definitions are copied verbatim from S78.Statements.
def resetInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ) : Matrix ι ι ℂ := (M - (t : ℂ) • Matrix.diagonal r)⁻¹

def squareKernel {ι : Type} (h : Matrix ι ι ℂ) : Matrix ι ι ℂ := fun i j => (h i j) ^ 2

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma real_symmetric_hermitian (M : Matrix ι ι ℂ)
    (hM : ∀ i j, M i j = M j i ∧ (M i j).im = 0) : M.IsHermitian := by
  ext i j
  apply Complex.ext
  · simp [Matrix.conjTranspose_apply, (hM j i).1]
  · simp [Matrix.conjTranspose_apply, (hM j i).2, (hM i j).2]

lemma damped_inner_im (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ)
    (hM : M.IsHermitian) (x : ι → ℂ) :
    (star x ⬝ᵥ (M - (t : ℂ) • diagonal r) *ᵥ x).im =
      -t * ∑ i, (r i).im * ‖x i‖ ^ 2 := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  have hreal := hM.im_star_dotProduct_mulVec_self x
  change (star x ⬝ᵥ M *ᵥ x).im = 0 at hreal
  rw [hreal]
  simp only [dotProduct, Complex.im_sum, mulVec_diagonal]
  have he : ∀ i, (star (x i) * (r i * x i)).im = (r i).im * ‖x i‖ ^ 2 := by
    intro i
    rw [show star (x i) * (r i * x i) = r i * (star (x i) * x i) by ring]
    change (r i * ((starRingEnd ℂ) (x i) * x i)).im = _
    rw [Complex.conj_mul', Complex.mul_im]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, add_zero]
  have hsum : (∑ i, (star (x i) * (r i * x i)).im) = ∑ i, (r i).im * ‖x i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact he i
  simp only [Pi.star_apply]
  rw [hsum]
  ring

lemma damped_coercive (M : Matrix ι ι ℂ) (r : ι → ℂ) (t c : ℝ)
    (hM : M.IsHermitian) (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (x : ι → ℂ) :
    (t * c) * ‖toLp 2 x‖ ≤ ‖toLp 2 ((M - (t : ℂ) • diagonal r) *ᵥ x)‖ := by
  let A := M - (t : ℂ) • diagonal r
  have hsum : c * ‖toLp 2 x‖ ^ 2 ≤ ∑ i, (r i).im * ‖x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hr i) (sq_nonneg _)
  have him := damped_inner_im M r t hM x
  have hbound : t * c * ‖toLp 2 x‖ ^ 2 ≤
      ‖toLp 2 x‖ * ‖toLp 2 (A *ᵥ x)‖ := by
    calc
      t * c * ‖toLp 2 x‖ ^ 2 ≤ t * (∑ i, (r i).im * ‖x i‖ ^ 2) := by
        nlinarith
      _ = -(star x ⬝ᵥ A *ᵥ x).im := by dsimp only [A]; rw [him]; ring
      _ ≤ ‖star x ⬝ᵥ A *ᵥ x‖ := (neg_le_abs _).trans (Complex.abs_im_le_norm _)
      _ = ‖inner ℂ (toLp 2 x) (toLp 2 (A *ᵥ x))‖ := by
        rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
      _ ≤ _ := norm_inner_le_norm _ _
  by_cases hx : ‖toLp 2 x‖ = 0
  · simp [hx]
  · have hxpos : 0 < ‖toLp 2 x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    nlinarith

lemma damped_isUnit (M : Matrix ι ι ℂ) (r : ι → ℂ) (t c : ℝ)
    (hM : M.IsHermitian) (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im) :
    IsUnit (M - (t : ℂ) • diagonal r).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hzero : (M - (t : ℂ) • diagonal r) *ᵥ (x - y) = 0 := by
    rw [mulVec_sub, hxy, sub_self]
  have h := damped_coercive M r t c hM ht hc hr (x - y)
  rw [hzero, toLp_zero, norm_zero] at h
  have hn : ‖toLp 2 (x - y)‖ = 0 := by
    have htc : 0 < t * c := mul_pos ht hc
    nlinarith [norm_nonneg (toLp 2 (x - y))]
  have hz : x - y = 0 := by simpa using congrArg ofLp (norm_eq_zero.mp hn)
  exact sub_eq_zero.mp hz

lemma damped_inverse_norm (M : Matrix ι ι ℂ) (r : ι → ℂ) (t c : ℝ)
    (hM : M.IsHermitian) (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im) :
    ‖resetInverse M r t‖ ≤ (t * c)⁻¹ := by
  have hu := damped_isUnit M r t c hM ht hc hr
  rw [Matrix.cstar_norm_def]
  apply (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (resetInverse M r t)).opNorm_le_bound (by positivity)
  intro x
  have h := damped_coercive M r t c hM ht hc hr (resetInverse M r t *ᵥ ofLp x)
  rw [mulVec_mulVec, show (M - (t : ℂ) • diagonal r) * resetInverse M r t = 1 from
    Matrix.mul_nonsing_inv _ hu, one_mulVec] at h
  change (t * c) * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (resetInverse M r t) x‖ ≤ ‖x‖ at h
  exact (le_inv_mul_iff₀ (by positivity : 0 < t * c)).mpr (by simpa [mul_comm] using h)

lemma damped_inverse_symmetric (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ)
    (hM : ∀ i j, M i j = M j i) :
    (resetInverse M r t).transpose = resetInverse M r t := by
  dsimp [resetInverse]
  rw [transpose_nonsing_inv, transpose_sub, transpose_smul, diagonal_transpose]
  congr 2
  ext i j
  exact (hM i j).symm

lemma damped_inverse_row (M : Matrix ι ι ℂ) (r : ι → ℂ) (t c C : ℝ)
    (hM : ∀ i j, M i j = M j i ∧ (M i j).im = 0)
    (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (hdiag : ∀ i, (resetInverse M r t i i).im ≤ C) (i : ι) :
    ‖toLp 2 (fun j => resetInverse M r t i j)‖ ^ 2 ≤ C / (t * c) := by
  let g := resetInverse M r t
  have hu := damped_isUnit M r t c (real_symmetric_hermitian M hM) ht hc hr
  have hsym := damped_inverse_symmetric M r t (fun i j => (hM i j).1)
  have hcol : (M - (t : ℂ) • diagonal r) *ᵥ (fun j => g j i) = Pi.single i 1 := by
    have he := congrArg (fun A : Matrix ι ι ℂ => fun j => A j i) (Matrix.mul_nonsing_inv _ hu)
    funext j
    have hej := congrFun he j
    simpa only [g, resetInverse, Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, eq_comm] using hej
  have him := damped_inner_im M r t (real_symmetric_hermitian M hM) (fun j => g j i)
  rw [hcol] at him
  have him' : t * (∑ j, (r j).im * ‖g j i‖ ^ 2) = (g i i).im := by
    simpa [dotProduct, Pi.single_apply, Complex.mul_im, Complex.conj_im] using (congrArg Neg.neg him).symm
  have hsum : c * (∑ j, ‖g j i‖ ^ 2) ≤ ∑ j, (r j).im * ‖g j i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hr j) (sq_nonneg _)
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j, ‖g i j‖ ^ 2) ≤ C / (t * c)
  have hs : ∀ j, g i j = g j i := by
    intro j
    exact (congrArg (fun A : Matrix ι ι ℂ => A i j) hsym).symm
  simp_rw [hs]
  apply (le_div_iff₀ (by positivity : 0 < t * c)).mpr
  have hd := hdiag i
  change (g i i).im ≤ C at hd
  nlinarith

end AndersonAC.SolS78
