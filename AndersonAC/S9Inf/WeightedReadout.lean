import AndersonAC.S9Inf.WeightedLattice

/-! Weighted operator norm control bounds each Green coefficient. -/

noncomputable section

open OAI.Anderson
open scoped ENNReal

namespace AndersonAC.SolS9Inf

theorem scalarGreen_weight_bound {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (hz : 0 < z.im) (w : Site d → ℝ) (M b : ℝ) (hM : 0 ≤ M)
    (hw : ∀ x, |w x| ≤ M) (hp : ∀ x, 0 < w x) (hb : 0 ≤ b)
    (hr : WeightRatioBound w b) (hsmall : 2 * (d : ℝ) * b ≤ z.im / 2)
    (x y : Site d) (hwy : w y = 1) :
    w x * ‖scalarGreen coupling ω x y z‖ ≤ 2 / z.im := by
  let W := diagonalRealL2 w M hM hw
  let D := latticeDefect w b hb hr
  have hcomm := lattice_weighted_equation coupling ω z w M b hM hw hp hb hr
  have hD : ‖D‖ ≤ z.im / 2 := (norm_latticeDefect_le w b hb hr).trans hsmall
  have hWbasis : W (basis y) = basis y := by
    classical
    apply lp.ext
    funext u
    by_cases hu : u = y
    · subst u
      simp [W, basis, hwy]
    · simp [W, basis, lp.single_apply, Pi.single_apply, hu]
  have hbound := weighted_green_estimate (hamiltonian coupling ω)
    (hamiltonian_isSelfAdjoint coupling ω) z hz W D hcomm hD (basis y)
  rw [hWbasis] at hbound
  have hnormbasis : ‖basis y‖ = 1 := by simp [basis]
  rw [hnormbasis, mul_one] at hbound
  calc
    w x * ‖scalarGreen coupling ω x y z‖ =
        ‖(W (green (hamiltonian coupling ω) z (basis y))) x‖ := by
      simp only [W, diagonalRealL2_apply, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (hp x), scalarGreen, inner_basis_left]
    _ ≤ ‖W (green (hamiltonian coupling ω) z (basis y))‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ x
    _ ≤ 2 / z.im := hbound

end AndersonAC.SolS9Inf
