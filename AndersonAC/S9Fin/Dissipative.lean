import AndersonAC.S9Fin.Algebra

noncomputable section
open AndersonAC.S9
open scoped ComplexConjugate Matrix

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma diagonal_quadratic_im (r x : n → ℂ) :
    (star x ⬝ᵥ (Matrix.diagonal r *ᵥ x)).im = ∑ i, (r i).im * ‖x i‖ ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (star (x i) * (r i * x i)).im = (r i).im * ‖x i‖ ^ 2
  change RCLike.im (star (x i) * (r i * x i)) = RCLike.im (r i) * ‖x i‖ ^ 2
  calc
    RCLike.im (star (x i) * (r i * x i)) = RCLike.im (r i * (x i * star (x i))) := by
      congr 1
      ring
    _ = RCLike.im (r i) * ‖x i‖ ^ 2 := by
      rw [RCLike.star_def, RCLike.mul_conj, RCLike.mul_im,
        RCLike.im_ofReal_pow, RCLike.re_ofReal_pow, mul_zero, zero_add]

lemma damped_quadratic_im (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η : ℝ) (r : n → ℂ) (x : EuclideanSpace ℂ n) :
    (inner ℂ x ((S - (η : ℂ) • Matrix.diagonal r).toEuclideanLin x)).im =
      -η * ∑ i, (r i).im * ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (((S - (η : ℂ) • Matrix.diagonal r) *ᵥ WithLp.ofLp x) ⬝ᵥ
    star (WithLp.ofLp x)).im = _
  rw [dotProduct_comm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  have hHerm : (star (WithLp.ofLp x) ⬝ᵥ S *ᵥ WithLp.ofLp x).im = 0 :=
    hS.im_star_dotProduct_mulVec_self (WithLp.ofLp x)
  rw [Complex.sub_im, hHerm, smul_eq_mul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    diagonal_quadratic_im]
  ring

lemma damped_lower_bound (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p) (r : n → ℂ)
    (hr : ∀ i, p ≤ (r i).im) (x : EuclideanSpace ℂ n) :
    (η * p) * ‖x‖ ≤ ‖(S - (η : ℂ) • Matrix.diagonal r).toEuclideanLin x‖ := by
  have hsum : p * ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, (r i).im * ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hr i) (sq_nonneg _))
  have hquad : (η * p) * ‖x‖ ^ 2 ≤
      -(inner ℂ x ((S - (η : ℂ) • Matrix.diagonal r).toEuclideanLin x)).im := by
    rw [damped_quadratic_im S hS η r x, EuclideanSpace.norm_sq_eq]
    nlinarith [mul_le_mul_of_nonneg_left hsum hη.le]
  have habs := neg_le_abs
    (inner ℂ x ((S - (η : ℂ) • Matrix.diagonal r).toEuclideanLin x)).im
  have himnorm := Complex.abs_im_le_norm
    (inner ℂ x ((S - (η : ℂ) • Matrix.diagonal r).toEuclideanLin x))
  have hcs := norm_inner_le_norm (𝕜 := ℂ) x ((S - (η : ℂ) • Matrix.diagonal r).toEuclideanLin x)
  have hprod := hquad.trans (habs.trans (himnorm.trans hcs))
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    apply (mul_le_mul_iff_right₀ hn).mp
    simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hprod

lemma damped_isUnit (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p) (r : n → ℂ)
    (hr : ∀ i, p ≤ (r i).im) : IsUnit (S - (η : ℂ) • Matrix.diagonal r) := by
  let A := S - (η : ℂ) • Matrix.diagonal r
  have hinj : Function.Injective A.toEuclideanLin := by
    intro x y hxy
    have hl := damped_lower_bound S hS η p hη hp r hr (x - y)
    have hz : A.toEuclideanLin (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    change (η * p) * ‖x - y‖ ≤ ‖A.toEuclideanLin (x - y)‖ at hl
    rw [hz, norm_zero] at hl
    have hn : ‖x - y‖ = 0 := by
      have hh : ‖x - y‖ ≤ (0 : ℝ) :=
        (mul_le_mul_iff_right₀ (mul_pos hη hp)).mp (by simpa using hl)
      exact le_antisymm hh (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have h : A.toEuclideanLin (WithLp.toLp 2 x) =
      A.toEuclideanLin (WithLp.toLp 2 y) := by
    change WithLp.toLp 2 (A *ᵥ x) = WithLp.toLp 2 (A *ᵥ y)
    rw [hxy]
  exact congrArg WithLp.ofLp (hinj h)

set_option maxHeartbeats 800000 in
theorem dissipative_inverse_bound_proof (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p) (r : n → ℂ)
    (hr : ∀ i, p ≤ (r i).im) :
    matrixOpNorm ((S - (η : ℂ) • Matrix.diagonal r)⁻¹) ≤ (η * p)⁻¹ := by
  let A := S - (η : ℂ) • Matrix.diagonal r
  have hA := damped_isUnit S hS η p hη hp r hr
  have hAd : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA
  change ‖A⁻¹.toEuclideanLin.toContinuousLinearMap‖ ≤ (η * p)⁻¹
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hl := damped_lower_bound S hS η p hη hp r hr (A⁻¹.toEuclideanLin x)
  have heq : A.toEuclideanLin (A⁻¹.toEuclideanLin x) = x := by
    have hm := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin x)
      (Matrix.mul_nonsing_inv A hAd)
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply, Matrix.toLpLin_one, LinearMap.id_apply] using hm
  change (η * p) * ‖A⁻¹.toEuclideanLin x‖ ≤ ‖A.toEuclideanLin (A⁻¹.toEuclideanLin x)‖ at hl
  rw [heq] at hl
  exact (le_inv_mul_iff₀ (mul_pos hη hp)).mpr hl

end AndersonAC.SolS9
