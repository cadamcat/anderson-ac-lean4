import AndersonAC.S78.Definitions

open scoped BigOperators
open AndersonAC.S78
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

theorem fourth_row_from_entry_and_two_proof {ι : Type} [Fintype ι]
    (a : Matrix ι ι ℂ) (i : ι) (U V : ℝ)
    (hU : 0 ≤ U) (hentry : ∀ j, ‖a i j‖ ≤ U)
    (hrow : rowTwo a i ≤ V) : rowFour a i ≤ U ^ 2 * V := by
  classical
  change (∑ j, ‖a i j‖ ^ 4) ≤ U ^ 2 * V
  calc
    (∑ j, ‖a i j‖ ^ 4) ≤ ∑ j, U ^ 2 * ‖a i j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hx : 0 ≤ ‖a i j‖ := norm_nonneg _
      have hdiff : 0 ≤ U - ‖a i j‖ := sub_nonneg.mpr (hentry j)
      have hsum : 0 ≤ U + ‖a i j‖ := add_nonneg hU hx
      have hsq : ‖a i j‖ ^ 2 ≤ U ^ 2 := by
        have hprod := mul_nonneg hdiff hsum
        nlinarith
      calc
        ‖a i j‖ ^ 4 = ‖a i j‖ ^ 2 * ‖a i j‖ ^ 2 := by ring
        _ ≤ U ^ 2 * ‖a i j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = U ^ 2 * rowTwo a i := by
      change (∑ j, U ^ 2 * ‖a i j‖ ^ 2) =
        U ^ 2 * (∑ j, ‖a i j‖ ^ 2)
      rw [Finset.mul_sum]
    _ ≤ U ^ 2 * V := mul_le_mul_of_nonneg_left hrow (sq_nonneg U)

end AndersonAC.SolS78
