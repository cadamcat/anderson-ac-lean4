import AndersonAC.S78Var.WardRows
import AndersonAC.S78.Definitions

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem delta_entry_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (h h' : Matrix ι ι ℂ) (ζ : ι → ℂ) (t : ℝ)
    (_ht : 0 < t)
    (hsym_h : h.transpose = h)
    (Rh Rh' : ℝ) (_hRh : 0 ≤ Rh) (hRh' : 0 ≤ Rh')
    (hrow : ∀ i, AndersonAC.S78.rowTwo h i ≤ Rh)
    (hrow' : ∀ i, AndersonAC.S78.rowTwo h' i ≤ Rh')
    (hΔ : ∀ i j, (h' - h) i j
      = (Real.sqrt t : ℂ) * ∑ k, h' i k * ζ k * h k j) :
    ∀ i j, ‖(h' - h) i j‖ ≤ Real.sqrt (Rh' * Rh) * ‖ζ‖ * Real.sqrt t := by
  classical
  intro i j
  have hs : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
  rw [hΔ i j, norm_mul, hs]
  have hsum_le : ‖∑ k, h' i k * ζ k * h k j‖
      ≤ ‖ζ‖ * (Real.sqrt Rh' * Real.sqrt Rh) := by
    calc ‖∑ k, h' i k * ζ k * h k j‖
        ≤ ∑ k, ‖h' i k * ζ k * h k j‖ := norm_sum_le Finset.univ _
      _ = ∑ k, (‖h' i k‖ * ‖h k j‖ * ‖ζ k‖) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [norm_mul, norm_mul]
          ring
      _ ≤ ∑ k, (‖h' i k‖ * ‖h k j‖ * ‖ζ‖) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact norm_le_pi_norm ζ k
      _ = ‖ζ‖ * ∑ k, (‖h' i k‖ * ‖h k j‖) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ ‖ζ‖ * (Real.sqrt Rh' * Real.sqrt Rh) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
            (fun k => ‖h' i k‖) (fun k => ‖h k j‖)
          have hrow'_eq : ∑ k, ‖h' i k‖ ^ 2 = AndersonAC.S78.rowTwo h' i := rfl
          have hcol_eq : ∑ k, ‖h k j‖ ^ 2 = AndersonAC.S78.rowTwo h j := by
            have hsymm : ∀ k, h k j = h j k := by
              intro k
              have h := congrFun (congrFun hsym_h j) k
              simpa [Matrix.transpose_apply] using h
            simp only [AndersonAC.S78.rowTwo]
            apply Finset.sum_congr rfl
            intro k _
            rw [hsymm k]
          rw [hrow'_eq, hcol_eq] at hcs
          calc ∑ k, ‖h' i k‖ * ‖h k j‖
              ≤ Real.sqrt (AndersonAC.S78.rowTwo h' i)
                * Real.sqrt (AndersonAC.S78.rowTwo h j) := hcs
            _ ≤ Real.sqrt Rh' * Real.sqrt Rh := by
                apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
                · exact Real.sqrt_le_sqrt (hrow' i)
                · exact Real.sqrt_le_sqrt (hrow j)
  calc Real.sqrt t * ‖∑ k, h' i k * ζ k * h k j‖
      ≤ Real.sqrt t * (‖ζ‖ * (Real.sqrt Rh' * Real.sqrt Rh)) := by
        apply mul_le_mul_of_nonneg_left hsum_le (Real.sqrt_nonneg _)
    _ = Real.sqrt (Rh' * Rh) * ‖ζ‖ * Real.sqrt t := by
        rw [Real.sqrt_mul hRh']
        ring

end AndersonAC.SolS78Var
