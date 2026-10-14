import AndersonAC.S6.Projection
import AndersonAC.S6.LocalizationInputs

/-! The full-range weighted absorption argument. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem weighted_range_absorption (H E K : Matrix R R ℂ) (w : EuclideanSpace ℂ R)
    (hH : IsUnit H.det) (hcomm : E * H = (H + K) * E)
    (hsource : Matrix.toEuclideanLin E (Matrix.toEuclideanLin H w) = Matrix.toEuclideanLin H w)
    (hsmall : ‖H⁻¹ * K‖ ≤ 1 / 2) :
    ‖Matrix.toEuclideanLin E w‖ ≤ 2 * ‖w‖ := by
  have hmul : Matrix.toEuclideanLin ((H + K) * E) w = Matrix.toEuclideanLin H w := by
    rw [← hcomm]
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hsource
  have hfac : H⁻¹ * ((H + K) * E) = E + (H⁻¹ * K) * E := by
    rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.nonsing_inv_mul H hH,
      Matrix.add_mul, Matrix.one_mul]
  have hid : Matrix.toEuclideanLin (E + (H⁻¹ * K) * E) w = w := by
    calc
      _ = Matrix.toEuclideanLin (H⁻¹ * ((H + K) * E)) w := by rw [hfac]
      _ = Matrix.toEuclideanLin H⁻¹ (Matrix.toEuclideanLin ((H + K) * E) w) := by
        simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
      _ = Matrix.toEuclideanLin H⁻¹ (Matrix.toEuclideanLin H w) := by rw [hmul]
      _ = Matrix.toEuclideanLin (H⁻¹ * H) w := by
        simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
      _ = w := by simp [Matrix.nonsing_inv_mul H hH, Matrix.toEuclideanLin]
  let v := Matrix.toEuclideanLin E w
  have hsum : v + Matrix.toEuclideanLin (H⁻¹ * K) v = w := by
    simpa only [map_add, LinearMap.add_apply, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hid
  have hnorm : ‖v‖ ≤ ‖w‖ + ‖Matrix.toEuclideanLin (H⁻¹ * K) v‖ := by
    calc
      ‖v‖ = ‖w - Matrix.toEuclideanLin (H⁻¹ * K) v‖ :=
        congrArg norm (eq_sub_of_add_eq hsum)
      _ ≤ ‖w‖ + ‖Matrix.toEuclideanLin (H⁻¹ * K) v‖ :=
        norm_sub_le w (Matrix.toEuclideanLin (H⁻¹ * K) v)
  have hop : ‖Matrix.toEuclideanLin (H⁻¹ * K) v‖ ≤ ‖H⁻¹ * K‖ * ‖v‖ :=
    Matrix.l2_opNorm_mulVec (H⁻¹ * K) v
  have hlast := mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)
  change ‖v‖ ≤ 2 * ‖w‖
  linarith

theorem projection_decay_of_weighted_range (C : Matrix R B ℂ) (a t L : ℝ) (ρ : R → ℝ)
    (hL : 0 ≤ L)
    (hweighted : ∀ v ∈ AndersonAC.S6.matrixRange C,
      ‖Matrix.toEuclideanLin (AndersonAC.S6.exponentialWeight a t ρ) v‖ ≤ L * ‖v‖) :
    ∀ i, AndersonAC.S6.projectionWeight C i ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i) := by
  intro i
  obtain ⟨hnonneg, _, hattain⟩ := AndersonAC.S6.projection_coordinate C i
  by_cases hpos : 0 < AndersonAC.S6.projectionWeight C i
  · obtain ⟨v, hv, hvnorm, hvi⟩ := hattain hpos
    let x := a * t * ρ i
    have hentry : (Matrix.toEuclideanLin (AndersonAC.S6.exponentialWeight a t ρ) v) i =
        (Real.exp x : ℂ) * v i := by
      change ((AndersonAC.S6.exponentialWeight a t ρ) *ᵥ (fun j => v j)) i = _
      simp [AndersonAC.S6.exponentialWeight, Matrix.mulVec_diagonal, x]
    have hbound : Real.exp x * ‖v i‖ ≤ L := by
      have hc := PiLp.norm_apply_le
        (Matrix.toEuclideanLin (AndersonAC.S6.exponentialWeight a t ρ) v) i
      rw [hentry, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos x).le] at hc
      have hw := hweighted v hv
      rw [hvnorm, mul_one] at hw
      exact hc.trans hw
    have hsquare := mul_self_le_mul_self (mul_nonneg (Real.exp_pos x).le (norm_nonneg (v i))) hbound
    have hexp : Real.exp x ^ 2 * Real.exp (-2 * x) = 1 := by
      have hinv : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      rw [show -2 * x = -x + -x by ring, Real.exp_add]
      calc
        Real.exp x ^ 2 * (Real.exp (-x) * Real.exp (-x)) =
            (Real.exp x * Real.exp (-x)) ^ 2 := by ring
        _ = 1 := by rw [hinv]; norm_num
    have hsq : Real.exp x ^ 2 * AndersonAC.S6.projectionWeight C i ≤ L ^ 2 := by
      rw [← hvi]
      nlinarith [hsquare]
    have hm := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-2 * x)).le
    have hx : -2 * a * t * ρ i = -2 * x := by dsimp [x]; ring
    rw [hx]
    nlinarith [hexp]
  · have hz : AndersonAC.S6.projectionWeight C i = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
    rw [hz]
    positivity

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.weighted_range_absorption
#print axioms AndersonAC.SolS6.projection_decay_of_weighted_range
