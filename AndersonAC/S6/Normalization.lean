import AndersonAC.S6.Definitions

/-! Transfer weighted full-range estimates through the frozen positive damping. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem sqrtDamping_mass (p : R → ℝ) (hp : ∀ i, 0 ≤ p i) (x : EuclideanSpace ℂ R) :
    ‖Matrix.toEuclideanLin (AndersonAC.S6.sqrtDamping p) x‖ ^ 2 =
      ∑ i, p i * ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hentry : (Matrix.toEuclideanLin (AndersonAC.S6.sqrtDamping p) x) i =
      (Real.sqrt (p i) : ℂ) * x i := by
    change (AndersonAC.S6.sqrtDamping p *ᵥ (fun j => x j)) i = _
    simp [AndersonAC.S6.sqrtDamping, Matrix.mulVec_diagonal]
  rw [hentry, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg (p i)), Real.sq_sqrt (hp i)]

theorem sqrtDamping_two_sided_sq (c K : ℝ) (p : R → ℝ) (x : EuclideanSpace ℂ R)
    (hc : 0 ≤ c) (hlower : ∀ i, c ≤ p i) (hupper : ∀ i, p i ≤ K) :
    c * ‖x‖ ^ 2 ≤ ‖Matrix.toEuclideanLin (AndersonAC.S6.sqrtDamping p) x‖ ^ 2 ∧
    ‖Matrix.toEuclideanLin (AndersonAC.S6.sqrtDamping p) x‖ ^ 2 ≤ K * ‖x‖ ^ 2 := by
  have hmass := sqrtDamping_mass p (fun i => hc.trans (hlower i)) x
  rw [hmass, EuclideanSpace.norm_sq_eq]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hlower i) (sq_nonneg _))
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hupper i) (sq_nonneg _))

theorem sqrtDamping_commutes_weight (p ρ : R → ℝ) (a t : ℝ) :
    AndersonAC.S6.sqrtDamping p * AndersonAC.S6.exponentialWeight a t ρ =
      AndersonAC.S6.exponentialWeight a t ρ * AndersonAC.S6.sqrtDamping p := by
  simp only [AndersonAC.S6.sqrtDamping, AndersonAC.S6.exponentialWeight, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem damping_weight_transfer (a t c K : ℝ) (p ρ : R → ℝ)
    (v w : EuclideanSpace ℂ R) (hc : 0 < c) (hK : c ≤ K)
    (hlower : ∀ i, c ≤ p i) (hupper : ∀ i, p i ≤ K)
    (hv : v = Matrix.toEuclideanLin (AndersonAC.S6.sqrtDamping p) w)
    (hweighted : ‖Matrix.toEuclideanLin (AndersonAC.S6.exponentialWeight a t ρ) w‖ ≤ 2 * ‖w‖) :
    ‖Matrix.toEuclideanLin (AndersonAC.S6.exponentialWeight a t ρ) v‖ ≤
      (2 * Real.sqrt (K / c)) * ‖v‖ := by
  let E := AndersonAC.S6.exponentialWeight a t ρ
  let D := AndersonAC.S6.sqrtDamping p
  let ew := Matrix.toEuclideanLin E w
  have hKpos : 0 < K := hc.trans_le hK
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hlow : Real.sqrt c * ‖w‖ ≤ ‖v‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg w)) (norm_nonneg v)).mp
    rw [mul_pow, Real.sq_sqrt hc.le, hv]
    exact (sqrtDamping_two_sided_sq c K p w hc.le hlower hupper).1
  have hup : ‖Matrix.toEuclideanLin D ew‖ ≤ Real.sqrt K * ‖ew‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg K) (norm_nonneg ew))).mp
    rw [mul_pow, Real.sq_sqrt hKpos.le]
    exact (sqrtDamping_two_sided_sq c K p ew hc.le hlower hupper).2
  have hcomm : Matrix.toEuclideanLin E v = Matrix.toEuclideanLin D ew := by
    rw [hv]
    change Matrix.toEuclideanLin E (Matrix.toEuclideanLin D w) =
      Matrix.toEuclideanLin D (Matrix.toEuclideanLin E w)
    have hm := sqrtDamping_commutes_weight p ρ a t
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using
      congrArg (fun A => Matrix.toEuclideanLin A w) hm.symm
  have hw : ‖w‖ ≤ ‖v‖ / Real.sqrt c := by
    apply (le_div_iff₀ hsc).mpr
    simpa only [mul_comm] using hlow
  rw [hcomm]
  calc
    ‖Matrix.toEuclideanLin D ew‖ ≤ Real.sqrt K * ‖ew‖ := hup
    _ ≤ Real.sqrt K * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hweighted (Real.sqrt_nonneg K)
    _ ≤ Real.sqrt K * (2 * (‖v‖ / Real.sqrt c)) := by
      gcongr
    _ = (2 * Real.sqrt (K / c)) * ‖v‖ := by
      rw [Real.sqrt_div hKpos.le]
      ring

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.sqrtDamping_mass
#print axioms AndersonAC.SolS6.sqrtDamping_two_sided_sq
#print axioms AndersonAC.SolS6.sqrtDamping_commutes_weight
#print axioms AndersonAC.SolS6.damping_weight_transfer
