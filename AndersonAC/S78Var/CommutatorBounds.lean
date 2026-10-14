import AndersonAC.S78Var.FormEstimates

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem commutator_transport {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h h' : Matrix ι ι ℂ) (z : ι → ℂ)
    (hh : IsUnit h.det) (hnew : IsUnit (h⁻¹ - Matrix.diagonal z).det)
    (heq : h' = (h⁻¹ - Matrix.diagonal z)⁻¹)
    (d : ℝ) (hd : 0 ≤ d) (hd2 : d ≤ 1 / 2)
    (hK : ‖h * Matrix.diagonal z‖ ≤ d) (hK' : ‖Matrix.diagonal z * h‖ ≤ d) :
    ∃ L R A B : Matrix ι ι ℂ,
      (∀ f, comm h' f = L * comm h f * R) ∧
      (∀ f, comm h f = A * comm h' f * B) ∧
      ‖L - 1‖ ≤ 2 * d ∧ ‖R - 1‖ ≤ 2 * d ∧
      ‖A - 1‖ ≤ d ∧ ‖B - 1‖ ≤ d := by
  obtain ⟨L, hKL, hLK, _, hL⟩ := neumann_bound (h * Matrix.diagonal z) (hK.trans hd2)
  obtain ⟨R, hKR, hRK, _, hR⟩ := neumann_bound (Matrix.diagonal z * h) (hK'.trans hd2)
  have hLe : (1 - h * Matrix.diagonal z)⁻¹ = L := Matrix.inv_eq_left_inv hLK
  have hRe : (1 - Matrix.diagonal z * h)⁻¹ = R := Matrix.inv_eq_left_inv hRK
  have hcomm : ∀ f, comm h' f = L * comm h f * R := by
    intro f
    have he := AndersonAC.SolS78.reset_commutator_proof h z f hh hnew
    dsimp only at he
    simpa only [comm, ← heq, hLe, hRe] using he
  refine ⟨L, R, 1 - h * Matrix.diagonal z, 1 - Matrix.diagonal z * h,
    hcomm, ?_, hL.trans (mul_le_mul_of_nonneg_left hK (by norm_num)),
    hR.trans (mul_le_mul_of_nonneg_left hK' (by norm_num)), ?_, ?_⟩
  · intro f
    rw [hcomm f]
    simp only [← Matrix.mul_assoc]
    rw [hKL, one_mul]
    rw [Matrix.mul_assoc, hRK, mul_one]
  · simpa only [sub_sub_cancel_left, norm_neg] using hK
  · simpa only [sub_sub_cancel_left, norm_neg] using hK'

end AndersonAC.SolS78Var
