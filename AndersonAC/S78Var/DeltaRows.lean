import AndersonAC.S78Var.RowEstimates

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

theorem delta_sqrt_rowTwo_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (h h' : Matrix ι ι ℂ) (ζ : ι → ℂ) (t : ℝ)
    (ht : 0 < t)
    (hsym_h : h.transpose = h)
    (Lh : ℝ) (hLh : 0 ≤ Lh)
    (hOp : ‖h‖ ≤ Lh)
    (Rh' : ℝ) (hRh' : 0 ≤ Rh')
    (hrow' : ∀ i, AndersonAC.S78.rowTwo h' i ≤ Rh')
    (hΔ : ∀ i j, (h' - h) i j
      = (Real.sqrt t : ℂ) * ∑ k, h' i k * ζ k * h k j) :
    ∀ i, Real.sqrt (AndersonAC.S78.rowTwo (h' - h) i)
      ≤ Lh * Real.sqrt Rh' * ‖ζ‖ * Real.sqrt t := by
  classical
  intro i
  let w : ι → ℂ := fun k => h' i k * ζ k
  have hw_sq : ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖ζ‖ ^ 2 * Rh' := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [PiLp.toLp_apply, w]
    calc ∑ k, ‖h' i k * ζ k‖ ^ 2
        = ∑ k, (‖h' i k‖ ^ 2 * ‖ζ k‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [norm_mul, mul_pow]
      _ ≤ ∑ k, (‖h' i k‖ ^ 2 * ‖ζ‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm ζ k) 2
      _ = (∑ k, ‖h' i k‖ ^ 2) * ‖ζ‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ Rh' * ‖ζ‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          calc ∑ k, ‖h' i k‖ ^ 2 = AndersonAC.S78.rowTwo h' i := rfl
            _ ≤ Rh' := hrow' i
      _ = ‖ζ‖ ^ 2 * Rh' := by ring
  have hvec_eq : (w ᵥ* h) = h *ᵥ w := by
    funext j
    simp only [Matrix.vecMul_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hsymm : h k j = h j k := by
      have h := congrFun (congrFun hsym_h j) k
      simpa [Matrix.transpose_apply] using h
    rw [hsymm]
    ring
  have hop : ‖WithLp.toLp 2 (h *ᵥ w)‖ ≤ Lh * ‖WithLp.toLp 2 w‖ := by
    have hle : ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) h)
        (WithLp.toLp 2 w)‖ ≤ ‖h‖ * ‖WithLp.toLp 2 w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have heq : ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) h)
        (WithLp.toLp 2 w) = WithLp.toLp 2 (h *ᵥ w) := rfl
    rw [heq] at hle
    calc ‖WithLp.toLp 2 (h *ᵥ w)‖ ≤ ‖h‖ * ‖WithLp.toLp 2 w‖ := hle
      _ ≤ Lh * ‖WithLp.toLp 2 w‖ :=
        mul_le_mul_of_nonneg_right hOp (norm_nonneg _)
  have hfun_j : ∀ j, (h' - h) i j = (Real.sqrt t : ℂ) * ((w ᵥ* h) j) := by
    intro j
    simp only [w, Matrix.vecMul_apply_eq_sum]
    rw [hΔ i j]
  have hrow_eq : AndersonAC.S78.rowTwo (h' - h) i
      = t * ‖WithLp.toLp 2 (h *ᵥ w)‖ ^ 2 := by
    simp only [AndersonAC.S78.rowTwo]
    have hstep : ∀ j, ‖(h' - h) i j‖ ^ 2
        = (‖(Real.sqrt t : ℂ)‖ * ‖(w ᵥ* h) j‖) ^ 2 := by
      intro j
      rw [hfun_j j, norm_mul]
    simp only [hstep]
    have hs2 : ‖(Real.sqrt t : ℂ)‖ ^ 2 = t := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht.le]
    calc ∑ j, (‖(Real.sqrt t : ℂ)‖ * ‖(w ᵥ* h) j‖) ^ 2
        = ∑ j, (t * ‖(w ᵥ* h) j‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_pow, hs2]
      _ = t * ∑ j, ‖(w ᵥ* h) j‖ ^ 2 := by rw [Finset.mul_sum]
      _ = t * ‖WithLp.toLp 2 (w ᵥ* h)‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
      _ = t * ‖WithLp.toLp 2 (h *ᵥ w)‖ ^ 2 := by rw [hvec_eq]
  rw [hrow_eq, Real.sqrt_mul ht.le, Real.sqrt_sq (norm_nonneg _)]
  calc Real.sqrt t * ‖WithLp.toLp 2 (h *ᵥ w)‖
      ≤ Real.sqrt t * (Lh * ‖WithLp.toLp 2 w‖) := by
        apply mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt t * (Lh * (‖ζ‖ * Real.sqrt Rh')) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hLh
        have hsq : ‖WithLp.toLp 2 w‖ ^ 2 ≤ (‖ζ‖ * Real.sqrt Rh') ^ 2 := by
          calc ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖ζ‖ ^ 2 * Rh' := hw_sq
            _ = (‖ζ‖ * Real.sqrt Rh') ^ 2 := by
                rw [mul_pow, Real.sq_sqrt hRh']
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
    _ = Lh * Real.sqrt Rh' * ‖ζ‖ * Real.sqrt t := by ring

end AndersonAC.SolS78Var
