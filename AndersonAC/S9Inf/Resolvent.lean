import OAI.MathematicalPhysics.Anderson.Certificates

/-! Operator identities used by the boundary propagation argument. -/

noncomputable section

open OAI.Anderson
open scoped ComplexConjugate

namespace AndersonAC.SolS9Inf

section Hilbert

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def green (T : K →L[ℂ] K) (z : ℂ) : K →L[ℂ] K :=
  Ring.inverse (T - z • (1 : K →L[ℂ] K))

theorem unit_inverse_apply_left (A : K →L[ℂ] K) (hA : IsUnit A) (w : K) :
    A (Ring.inverse A w) = w := by
  simpa using congrArg (fun M : K →L[ℂ] K => M w) (Ring.mul_inverse_cancel A hA)

theorem unit_inverse_apply_right (A : K →L[ℂ] K) (hA : IsUnit A) (w : K) :
    Ring.inverse A (A w) = w := by
  simpa using congrArg (fun M : K →L[ℂ] K => M w) (Ring.inverse_mul_cancel A hA)

theorem unit_injective (A : K →L[ℂ] K) (hA : IsUnit A) : Function.Injective A := by
  intro u v huv
  have h := congrArg (fun w : K => Ring.inverse A w) huv
  simpa only [unit_inverse_apply_right A hA] using h

theorem shifted_isUnit (T : K →L[ℂ] K) (hT : IsSelfAdjoint T) (z : ℂ)
    (hz : z.im ≠ 0) : IsUnit (T - z • (1 : K →L[ℂ] K)) := by
  have hspec : z ∉ spectrum ℂ T := fun h => hz (hT.im_eq_zero_of_mem_spectrum h)
  have hunit := (spectrum.notMem_iff.mp hspec).neg
  simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using hunit

/-- Algebraic rank-one inversion, using both actual operator units. -/
theorem inverse_rank_one_apply (A : K →L[ℂ] K) (hA : IsUnit A) (v w : K)
    (hv : v ≠ 0) (h : ℂ)
    (hB : IsUnit (A + h • InnerProductSpace.rankOne ℂ v v)) :
    Ring.inverse (A + h • InnerProductSpace.rankOne ℂ v v) w =
      Ring.inverse A w -
        (h * inner ℂ v (Ring.inverse A w) /
          (1 + h * inner ℂ v (Ring.inverse A v))) • Ring.inverse A v := by
  have hd : 1 + h * inner ℂ v (Ring.inverse A v) ≠ 0 := by
    intro hzero
    have hnew : (A + h • InnerProductSpace.rankOne ℂ v v) (Ring.inverse A v) = 0 := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        InnerProductSpace.rankOne_apply, unit_inverse_apply_left A hA]
      calc
        _ = (1 + h * inner ℂ v (Ring.inverse A v)) • v := by
          rw [add_smul, one_smul, smul_smul]
        _ = 0 := by rw [hzero, zero_smul]
    have hvec : Ring.inverse A v = 0 :=
      (unit_injective _ hB) (hnew.trans (map_zero _).symm)
    apply hv
    have heq := unit_inverse_apply_left A hA v
    rw [hvec, map_zero] at heq
    exact heq.symm
  let α : ℂ := h * inner ℂ v (Ring.inverse A w) /
    (1 + h * inner ℂ v (Ring.inverse A v))
  have hcoef : h * inner ℂ v (Ring.inverse A w) - α -
      h * (α * inner ℂ v (Ring.inverse A v)) = 0 := by
    dsimp [α]
    field_simp [hd]
    ring
  apply unit_injective _ hB
  rw [unit_inverse_apply_left _ hB]
  symm
  change (A + h • InnerProductSpace.rankOne ℂ v v)
    (Ring.inverse A w - α • Ring.inverse A v) = w
  calc
    _ = w + (h * inner ℂ v (Ring.inverse A w) - α -
        h * (α * inner ℂ v (Ring.inverse A v))) • v := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        map_sub, map_smul, InnerProductSpace.rankOne_apply, inner_sub_right,
        inner_smul_right, unit_inverse_apply_left A hA]
      module
    _ = w := by rw [hcoef, zero_smul, add_zero]

/-- The scalar-damped resolvent has a nonnegative imaginary quadratic form. -/
theorem green_quadratic_im (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) (v : K) :
    (inner ℂ v (green T z v)).im = z.im * ‖green T z v‖ ^ 2 := by
  let q := green T z v
  have hA := shifted_isUnit T hT z hz
  have hq : T q - z • q = v := by
    simpa [q, green] using unit_inverse_apply_left (T - z • (1 : K →L[ℂ] K)) hA v
  have hsym : T.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hreal : (inner ℂ (T q) q).im = 0 := hsym.im_inner_apply_self q
  change (inner ℂ v q).im = z.im * ‖q‖ ^ 2
  rw [← hq, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [Complex.sub_im, Complex.mul_im, hreal, ← Complex.ofReal_pow]

theorem green_quadratic_im_nonneg (T : K →L[ℂ] K) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) (v : K) : 0 ≤ (inner ℂ v (green T z v)).im := by
  rw [green_quadratic_im T hT z hz.ne' v]
  exact mul_nonneg hz.le (sq_nonneg _)

end Hilbert

end AndersonAC.SolS9Inf
