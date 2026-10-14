import AndersonAC.S6.Definitions
import AndersonAC.S6.LocalizationInputs

/-! Sparse hopping estimates for the collapsed-distance exponential weight. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem exp_difference_bound (x y : ℝ) (_hy : 0 ≤ y) (hx : |x| ≤ y) :
    |Real.exp x - 1| ≤ Real.exp y - 1 := by
  obtain ⟨hlower, hupper⟩ := abs_le.mp hx
  have hu := Real.exp_le_exp.mpr hupper
  have hl := Real.exp_le_exp.mpr hlower
  have h1 := Real.add_one_le_exp y
  have h2 := Real.add_one_le_exp (-y)
  apply abs_le.mpr
  constructor <;> linarith

theorem exp_scaled_bound (a t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (a * t) - 1 ≤ (Real.exp a - 1) * t := by
  have h := convexOn_exp.2 (x := 0) (y := a)
    (Set.mem_univ _) (Set.mem_univ _) (sub_nonneg.mpr ht1) ht (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm t a] at h
  nlinarith

theorem exponential_weight_inverse (a t : ℝ) (ρ : R → ℝ) :
    AndersonAC.S6.exponentialWeight a t ρ * AndersonAC.S6.exponentialWeight (-a) t ρ = 1 ∧
    AndersonAC.S6.exponentialWeight (-a) t ρ * AndersonAC.S6.exponentialWeight a t ρ = 1 := by
  constructor <;> ext i j <;> by_cases hij : i = j
  · subst j
    simp [AndersonAC.S6.exponentialWeight, ← Complex.exp_add, neg_mul]
  · simp [AndersonAC.S6.exponentialWeight, Matrix.diagonal_mul_diagonal, hij]
  · subst j
    simp [AndersonAC.S6.exponentialWeight, ← Complex.exp_add, neg_mul]
  · simp [AndersonAC.S6.exponentialWeight, Matrix.diagonal_mul_diagonal, hij]

theorem weighted_conjugation_entry (a t : ℝ) (ρ : R → ℝ) (H : Matrix R R ℂ) (i j : R) :
    (AndersonAC.S6.exponentialWeight a t ρ * H *
      AndersonAC.S6.exponentialWeight (-a) t ρ - H) i j =
        ((Real.exp (a * t * (ρ i - ρ j)) : ℂ) - 1) * H i j := by
  simp only [AndersonAC.S6.exponentialWeight, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply]
  have hx : a * t * ρ i + -a * t * ρ j = a * t * (ρ i - ρ j) := by ring
  rw [sub_mul, one_mul]
  congr 1
  calc
    (Real.exp (a * t * ρ i) : ℂ) * H i j * (Real.exp (-a * t * ρ j) : ℂ) =
        ((Real.exp (a * t * ρ i) * Real.exp (-a * t * ρ j) : ℝ) : ℂ) * H i j := by
      push_cast
      ring
    _ = _ := by rw [← Real.exp_add, hx]

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.exp_scaled_bound
#print axioms AndersonAC.SolS6.weighted_conjugation_entry
#print axioms AndersonAC.SolS6.exp_difference_bound
#print axioms AndersonAC.SolS6.exponential_weight_inverse
