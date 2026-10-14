import AndersonAC.S6.Supported
import AndersonAC.S6.CoreAlgebra

/-! Corollary 6.3: exponential decay of the completed scaled resolvent change. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem scattering_scaled_entry_norm (t : ℝ) (p : R → ℝ) (dh ds : Matrix R R ℂ)
    (hrelation : ds = (2 * Complex.I * (Real.sqrt t : ℂ)) •
      (AndersonAC.S6.sqrtDamping p * dh * AndersonAC.S6.sqrtDamping p)) (i j : R) :
    ‖ds i j‖ = 2 * Real.sqrt t * Real.sqrt (p i) * Real.sqrt (p j) * ‖dh i j‖ := by
  rw [hrelation]
  simp only [Matrix.smul_apply, smul_eq_mul, AndersonAC.S6.sqrtDamping,
    Matrix.diagonal_mul, Matrix.mul_diagonal, norm_mul,
    Complex.norm_ofNat, Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

theorem sqrt_exponential_decay (x L a t ρ : ℝ) (hL : 0 ≤ L)
    (hx : x ≤ L ^ 2 * Real.exp (-2 * a * t * ρ)) :
    Real.sqrt x ≤ L * Real.exp (-a * t * ρ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hL (Real.exp_pos _).le, ?_⟩
  have he : (Real.exp (-a * t * ρ)) ^ 2 = Real.exp (-2 * a * t * ρ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he] using hx

end AndersonAC.SolS6

namespace AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem core_decay (t c a L : ℝ) (p : R → ℝ) (ρ : R → ℝ)
    (C : Matrix R B ℂ) (dh ds : Matrix R R ℂ)
    (ht : 0 < t) (hc : 0 < c) (hL : 0 ≤ L) (hp : ∀ i, c ≤ p i)
    (hD : ‖ds‖ ≤ 2) (hleft : rangeProjection C * ds = ds) (hs : ds.IsSymm)
    (hrelation : ds = (2 * Complex.I * (Real.sqrt t : ℂ)) •
      (sqrtDamping p * dh * sqrtDamping p))
    (hdecay : ∀ i, projectionWeight C i ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i)) :
    Planned.core_decay t c a L p ρ C dh ds ht hc hL hp hD hleft hs hrelation hdecay := by
  intro i j
  have hpoint := (supported_change_bounds C ds hD hleft hs).2.1 i j
  rw [Real.sqrt_mul (projection_coordinate C i).1] at hpoint
  have hi := AndersonAC.SolS6.sqrt_exponential_decay _ L a t (ρ i) hL (hdecay i)
  have hj := AndersonAC.SolS6.sqrt_exponential_decay _ L a t (ρ j) hL (hdecay j)
  have he : Real.exp (-a * t * ρ i) * Real.exp (-a * t * ρ j) =
      Real.exp (-a * t * (ρ i + ρ j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb : ‖ds i j‖ ≤ 2 * L ^ 2 * Real.exp (-a * t * (ρ i + ρ j)) := by
    calc ‖ds i j‖ ≤ 2 * (Real.sqrt (projectionWeight C i) * Real.sqrt (projectionWeight C j)) := hpoint
      _ ≤ 2 * ((L * Real.exp (-a * t * ρ i)) * (L * Real.exp (-a * t * ρ j))) := by
        gcongr
      _ = _ := by rw [show (L * Real.exp (-a * t * ρ i)) * (L * Real.exp (-a * t * ρ j)) =
          L ^ 2 * (Real.exp (-a * t * ρ i) * Real.exp (-a * t * ρ j)) by ring, he]; ring
  have hpl : c ≤ Real.sqrt (p i) * Real.sqrt (p j) := by
    calc c = Real.sqrt c * Real.sqrt c := (Real.mul_self_sqrt hc.le).symm
      _ ≤ Real.sqrt (p i) * Real.sqrt (p j) := by gcongr <;> apply hp
  have heq := AndersonAC.SolS6.scattering_scaled_entry_norm t p dh ds hrelation i j
  have hlower : 2 * Real.sqrt t * c * ‖dh i j‖ ≤ ‖ds i j‖ := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hpl
      (mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg (dh i j)))]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hfinal : ‖dh i j‖ * (c * Real.sqrt t) ≤
      L ^ 2 * Real.exp (-a * t * (ρ i + ρ j)) := by linarith
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (mul_pos hc hst)).mpr hfinal

end AndersonAC.S6
#print axioms AndersonAC.SolS6.scattering_scaled_entry_norm
#print axioms AndersonAC.SolS6.sqrt_exponential_decay
#print axioms AndersonAC.S6.core_decay
