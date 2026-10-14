import Mathlib
import AndersonAC.S78Var.RowEstimates

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem neumann_bound {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Matrix ι ι ℂ) (hK : ‖K‖ ≤ 1 / 2) :
    ∃ L : Matrix ι ι ℂ, (1 - K) * L = 1 ∧ L * (1 - K) = 1 ∧
      ‖L‖ ≤ 2 ∧ ‖L - 1‖ ≤ 2 * ‖K‖ := by
  classical
  have hK1 : ‖K‖ < 1 := lt_of_le_of_lt hK (by norm_num)
  have hIs : IsUnit (1 - K) := isUnit_one_sub_of_norm_lt_one hK1
  have hdet : IsUnit (1 - K).det := (Matrix.isUnit_iff_isUnit_det _).mp hIs
  let L := (1 - K)⁻¹
  have hLR : (1 - K) * L = 1 := Matrix.mul_nonsing_inv _ hdet
  have hRL : L * (1 - K) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hL_eq : L = 1 + K * L := by
    have h : L - K * L = 1 := by
      calc L - K * L = (1 - K) * L := by noncomm_ring
        _ = 1 := hLR
    calc L = (L - K * L) + K * L := by abel
      _ = 1 + K * L := by rw [h]
  have h1le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
    have hperm : (1 : Matrix ι ι ℂ) = (1 : Equiv.Perm ι).permMatrix ℂ :=
      (Matrix.permMatrix_one).symm
    rw [hperm]
    exact Matrix.permMatrix_l2_opNorm_le _
  have htri : ‖L‖ ≤ 1 + ‖K‖ * ‖L‖ := by
    calc ‖L‖ = ‖1 + K * L‖ := by rw [← hL_eq]
      _ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖K * L‖ := norm_add_le _ _
      _ ≤ 1 + ‖K‖ * ‖L‖ := by
        apply add_le_add h1le
        exact Matrix.l2_opNorm_mul _ _
  have hbound : ‖K‖ * ‖L‖ ≤ (1 / 2) * ‖L‖ :=
    mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  have hL2 : ‖L‖ ≤ 2 := by linarith [htri, hbound]
  refine ⟨L, hLR, hRL, hL2, ?_⟩
  have hsub : L - 1 = K * L := by
    calc L - 1 = (1 + K * L) - 1 := by rw [← hL_eq]
      _ = K * L := by abel
  calc ‖L - 1‖ = ‖K * L‖ := by rw [hsub]
    _ ≤ ‖K‖ * ‖L‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖K‖ * 2 := by
      apply mul_le_mul_of_nonneg_left hL2 (norm_nonneg _)
    _ = 2 * ‖K‖ := by ring

end AndersonAC.SolS78Var
