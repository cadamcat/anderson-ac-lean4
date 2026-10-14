import AndersonAC.S78Var.ResolventAlgebra

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem normalized_delta_entries {ι : Type} [Fintype ι] [DecidableEq ι]
    (G G' : Matrix ι ι ℂ) (ζ : ι → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hRes : G' - G = G' * ((t : ℂ) • Matrix.diagonal ζ) * G) :
    ∀ i j, (((Real.sqrt t : ℂ) • G' - (Real.sqrt t : ℂ) • G) i j) =
      (Real.sqrt t : ℂ) * ∑ k, ((Real.sqrt t : ℂ) • G') i k * ζ k *
        (((Real.sqrt t : ℂ) • G) k j) := by
  have hs2 : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  intro i j
  have hsub : (Real.sqrt t : ℂ) • G' - (Real.sqrt t : ℂ) • G =
      (Real.sqrt t : ℂ) • (G' - G) := (smul_sub _ _ _).symm
  rw [hsub, hRes]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc _ = (Real.sqrt t : ℂ) * (t : ℂ) * (G' i k * ζ k * G k j) := by ring
    _ = _ := by rw [← hs2]; ring

end AndersonAC.SolS78Var
