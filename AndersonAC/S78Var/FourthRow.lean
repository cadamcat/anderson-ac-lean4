import AndersonAC.S78Var.DeltaRows

open scoped BigOperators
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem fourth_row_from_entry_and_two {ι : Type} [Fintype ι]
    (a : Matrix ι ι ℂ) (i : ι) (U V : ℝ)
    (_hU : 0 ≤ U) (hentry : ∀ j, ‖a i j‖ ≤ U) (hrow : AndersonAC.S78.rowTwo a i ≤ V) :
    AndersonAC.S78.rowFour a i ≤ U ^ 2 * V := by
  classical
  simp only [AndersonAC.S78.rowFour, AndersonAC.S78.rowTwo] at hrow ⊢
  calc ∑ j, ‖a i j‖ ^ 4
      = ∑ j, (‖a i j‖ ^ 2 * ‖a i j‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ ∑ j, (U ^ 2 * ‖a i j‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (hentry j) 2
    _ = U ^ 2 * ∑ j, ‖a i j‖ ^ 2 := by rw [← Finset.mul_sum]
    _ ≤ U ^ 2 * V := by
        apply mul_le_mul_of_nonneg_left hrow (sq_nonneg _)

theorem fourth_root_row_bound {ι : Type} [Fintype ι]
    (a : Matrix ι ι ℂ) (i : ι) (t ρ E D : ℝ)
    (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hentry : ∀ j, ‖a i j‖ ≤ E * Real.sqrt t * ρ)
    (hrow : Real.sqrt (AndersonAC.S78.rowTwo a i) ≤ D * ρ) :
    (AndersonAC.S78.rowFour a i) ^ (1 / 4 : ℝ) ≤
      Real.sqrt (E * D) * t ^ (1 / 4 : ℝ) * ρ := by
  have htwo0 : 0 ≤ AndersonAC.S78.rowTwo a i := by unfold AndersonAC.S78.rowTwo; positivity
  have htwo : AndersonAC.S78.rowTwo a i ≤ (D * ρ) ^ 2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrow 2
    rwa [Real.sq_sqrt htwo0] at hh
  have hfour := fourth_row_from_entry_and_two a i (E * Real.sqrt t * ρ)
    ((D * ρ) ^ 2) (by positivity) hentry htwo
  have he : (Real.sqrt (E * D) * t ^ (1 / 4 : ℝ) * ρ) ^ 4 =
      (E * Real.sqrt t * ρ) ^ 2 * (D * ρ) ^ 2 := by
    have htp : (t ^ (1 / 4 : ℝ)) ^ 4 = t := by
      simpa only [Nat.cast_ofNat, one_div] using Real.rpow_inv_natCast_pow ht (by norm_num : (4 : ℕ) ≠ 0)
    rw [mul_pow, mul_pow, htp, show Real.sqrt (E * D) ^ 4 = (E * D) ^ 2 by
      rw [show Real.sqrt (E * D) ^ 4 = (Real.sqrt (E * D) ^ 2) ^ 2 by ring,
        Real.sq_sqrt (mul_nonneg hE hD)]]
    simp only [mul_pow, Real.sq_sqrt ht]
    ring
  have hn : 0 ≤ Real.sqrt (E * D) * t ^ (1 / 4 : ℝ) * ρ := by positivity
  calc (AndersonAC.S78.rowFour a i) ^ (1 / 4 : ℝ)
      ≤ ((Real.sqrt (E * D) * t ^ (1 / 4 : ℝ) * ρ) ^ 4) ^ (1 / 4 : ℝ) := by
        apply Real.rpow_le_rpow (by unfold AndersonAC.S78.rowFour; positivity)
        · exact hfour.trans_eq he.symm
        · norm_num
    _ = _ := by
      simpa only [Nat.cast_ofNat, one_div] using Real.pow_rpow_inv_natCast hn (by norm_num : (4 : ℕ) ≠ 0)

end AndersonAC.SolS78Var
