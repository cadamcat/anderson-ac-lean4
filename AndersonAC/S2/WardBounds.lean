import AndersonAC.S2.Ward

/-! The L² inverse bound for a real symmetric matrix with strictly positive damping. -/

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator ComplexOrder

namespace AndersonAC.SolS2
open AndersonAC.S2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem damped_euclidean_pairing_im (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    (t : ℝ) (r : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    (inner ℂ x (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r)) x)).im =
      -t * ∑ i, (r i).im * ‖x i‖ ^ 2 := by
  have hi : inner ℂ x (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r)) x) =
      pairing (WithLp.ofLp x) ((dampedMatrix M t r).mulVec (WithLp.ofLp x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, dotProduct_comm]
    rfl
  rw [hi]
  exact damped_pairing_im M hM t r (WithLp.ofLp x)

theorem damped_coercive (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    {t c : ℝ} (ht : 0 < t) (hc : 0 < c) (r : ι → ℂ)
    (hp : ∀ i, c ≤ (r i).im) (x : EuclideanSpace ℂ ι) :
    t * c * ‖x‖ ≤ ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r) x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlow : c * ‖x‖ ^ 2 ≤ ∑ i, (r i).im * ‖x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hp i) (sq_nonneg _))
  have hpos : 0 ≤ ∑ i, (r i).im * ‖x i‖ ^ 2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hc.le.trans (hp i)) (sq_nonneg _))
  have hneg : -t * (∑ i, (r i).im * ‖x i‖ ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) hpos
  have hupper := (Complex.abs_im_le_norm
    (inner ℂ x ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r) x))).trans
    (norm_inner_le_norm x ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r) x))
  rw [damped_euclidean_pairing_im M hM, abs_of_nonpos hneg] at hupper
  have hbound : t * c * ‖x‖ ^ 2 ≤ ‖x‖ * ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r) x‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hlow ht.le]
  apply (mul_le_mul_iff_right₀ hnx).mp
  convert hbound using 1 <;> ring

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem resolvent_norm_bound (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    {t pMin : ℝ} (ht : 0 < t) (hpMin : 0 < pMin) (r : ι → ℂ)
    (hp : ∀ i, pMin ≤ (r i).im) :
    ‖resolvent M t r‖ ≤ (t * pMin)⁻¹ := by
  have hunit := damped_invertible M hM ht r (fun i => hpMin.trans_le (hp i))
  have hBG : dampedMatrix M t r * resolvent M t r = 1 :=
    (dampedMatrix M t r).mul_nonsing_inv ((dampedMatrix M t r).isUnit_iff_isUnit_det.mp hunit)
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have hinv : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r)
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (resolvent M t r) y) = y := by
    calc
      _ = (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (dampedMatrix M t r * resolvent M t r) y := by
        simp only [map_mul, ContinuousLinearMap.mul_apply]
      _ = y := by rw [hBG, map_one]; rfl
  have hb := damped_coercive M hM ht hpMin r hp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (resolvent M t r) y)
  rw [hinv] at hb
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ (mul_pos ht hpMin)).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hb

end AndersonAC.S2
