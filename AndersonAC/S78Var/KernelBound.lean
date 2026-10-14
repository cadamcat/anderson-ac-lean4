import AndersonAC.S78Var.FourthRow

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

/-- Schur row-sum bound for symmetric matrices: ‖A‖ ≤ max row ℓ1. -/
theorem schur_bound_symmetric {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hsym : A.transpose = A)
    (R : ℝ) (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) :
    ‖A‖ ≤ R := by
  classical
  change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A‖ ≤ R
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hcol : ∀ j, ∑ i, ‖A i j‖ ≤ R := by
    intro j
    have he : ∀ i, A i j = A j i := fun i => congrFun (congrFun hsym j) i
    simpa only [he] using hrow j
  have hentry : ∀ i, ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A x) i‖ ^ 2 ≤
      R * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
    intro i
    have hn : ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
      change ‖∑ j, A i j * x j‖ ≤ _
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun j => A i j * x j)
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun j => Real.sqrt ‖A i j‖) (fun j => Real.sqrt ‖A i j‖ * ‖x j‖)
    have he : ∀ j, Real.sqrt ‖A i j‖ * (Real.sqrt ‖A i j‖ * ‖x j‖) =
        ‖A i j‖ * ‖x j‖ := fun j => by rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    simp only [he, mul_pow, Real.sq_sqrt (norm_nonneg _)] at hcs
    have hsum : 0 ≤ ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by positivity
    have hh := hn.trans hcs
    have hh2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hsum] at hh2
    exact hh2.trans (mul_le_mul_of_nonneg_right (hrow i) hsum)
  calc ∑ i, ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A x) i‖ ^ 2
      ≤ ∑ i, R * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := Finset.sum_le_sum fun i _ => hentry i
    _ = R * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
    _ ≤ R * ∑ j, R * ‖x j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    _ = R ^ 2 * ∑ j, ‖x j‖ ^ 2 := by rw [← Finset.mul_sum]; ring
theorem kernel_difference_bound {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h h' : Matrix ι ι ℂ) (hsym : h.transpose = h) (hsym' : h'.transpose = h')
    (Rh Rh' V : ℝ) (hRh : 0 ≤ Rh) (hRh' : 0 ≤ Rh') (hV : 0 ≤ V)
    (hrow : ∀ i, AndersonAC.S78.rowTwo h i ≤ Rh)
    (hrow' : ∀ i, AndersonAC.S78.rowTwo h' i ≤ Rh')
    (hdelta : ∀ i, Real.sqrt (AndersonAC.S78.rowTwo (h' - h) i) ≤ V) :
    AndersonAC.S78.matrixNorm (AndersonAC.S78.squareKernel h' - AndersonAC.S78.squareKernel h)
      ≤ V * (Real.sqrt Rh' + Real.sqrt Rh) := by
  classical
  change ‖AndersonAC.S78.squareKernel h' - AndersonAC.S78.squareKernel h‖ ≤ _
  have hsymdiff : (AndersonAC.S78.squareKernel h' - AndersonAC.S78.squareKernel h).transpose =
      AndersonAC.S78.squareKernel h' - AndersonAC.S78.squareKernel h := by
    ext i j
    have he : h j i = h i j := congrFun (congrFun hsym i) j
    have he' : h' j i = h' i j := congrFun (congrFun hsym' i) j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, AndersonAC.S78.squareKernel, he, he']
  apply schur_bound_symmetric _ hsymdiff _ (by positivity)
  intro i
  have hcs (a : Matrix ι ι ℂ) (R : ℝ) (hb : AndersonAC.S78.rowTwo a i ≤ R) :
      ∑ j, ‖(h' - h) i j‖ * ‖a i j‖ ≤ V * Real.sqrt R := by
    have he := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun j => ‖(h' - h) i j‖) (fun j => ‖a i j‖)
    exact he.trans (mul_le_mul (hdelta i) (Real.sqrt_le_sqrt hb)
      (Real.sqrt_nonneg _) hV)
  calc ∑ j, ‖(AndersonAC.S78.squareKernel h' - AndersonAC.S78.squareKernel h) i j‖
      ≤ ∑ j, ‖(h' - h) i j‖ * (‖h' i j‖ + ‖h i j‖) := by
        apply Finset.sum_le_sum
        intro j _
        change ‖(h' i j) ^ 2 - (h i j) ^ 2‖ ≤ _
        rw [show (h' i j) ^ 2 - (h i j) ^ 2 = (h' i j - h i j) * (h' i j + h i j) by ring, norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = (∑ j, ‖(h' - h) i j‖ * ‖h' i j‖) + ∑ j, ‖(h' - h) i j‖ * ‖h i j‖ := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ V * Real.sqrt Rh' + V * Real.sqrt Rh := add_le_add (hcs h' Rh' (hrow' i)) (hcs h Rh (hrow i))
    _ = _ := by ring

end AndersonAC.SolS78Var
