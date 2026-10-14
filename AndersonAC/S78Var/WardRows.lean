import AndersonAC.S78Var.ResolventAlgebra
import AndersonAC.S78.Definitions
import AndersonAC.Blueprint.FiniteInputs

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78Var

/-- Diagonal of Ward identity gives row bound. -/
theorem ward_rowTwo_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (t : ℝ) (r : ι → ℂ) (c Cg : ℝ)
    (ht : 0 < t) (hc : 0 < c)
    (hlow : ∀ k, c ≤ (r k).im)
    (hWard : (t : ℂ) • (G * Matrix.diagonal (fun k => ((r k).im : ℂ)) *
      G.conjTranspose) = AndersonAC.Blueprint.matrixImag G)
    (i : ι) (hIm : (G i i).im ≤ Cg) :
    AndersonAC.S78.rowTwo ((Real.sqrt t : ℂ) • G) i ≤ Cg / c := by
  classical
  -- Compute (G*D*Gᴴ) i i as single sum
  have hGH : ∀ k, G.conjTranspose k i = star (G i k) := fun k => by
    simp [Matrix.conjTranspose_apply]
  have hGD : ∀ k, (G * Matrix.diagonal (fun k => ((r k).im : ℂ))) i k
      = G i k * ((r k).im : ℂ) := fun k => Matrix.mul_diagonal _ _ _ _
  have hprod : (G * Matrix.diagonal (fun k => ((r k).im : ℂ)) * G.conjTranspose) i i
      = ∑ k, G i k * ((r k).im : ℂ) * star (G i k) := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [hGD k, hGH k]
  have hentry := congrFun (congrFun hWard i) i
  simp only [Matrix.smul_apply, hprod, AndersonAC.Blueprint.matrixImag,
    Matrix.sub_apply, Matrix.conjTranspose_apply] at hentry
  -- hentry : ↑t * ∑ ... = (2*I)⁻¹ * (Gii - star Gii)
  have hsum_eq : (∑ k, G i k * ((r k).im : ℂ) * star (G i k))
      = ((∑ k, (r k).im * ‖G i k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : G i k * ((r k).im : ℂ) * star (G i k)
        = ((r k).im : ℂ) * (G i k * star (G i k)) := by ring
    rw [h1, RCLike.star_def, RCLike.mul_conj]
    simp [Complex.ofReal_mul, Complex.ofReal_pow]
  have hLHS : (t : ℂ) * (∑ k, G i k * ((r k).im : ℂ) * star (G i k))
      = ((t * ∑ k, (r k).im * ‖G i k‖ ^ 2 : ℝ) : ℂ) := by
    rw [hsum_eq, Complex.ofReal_mul]
  have hRHS : ((2 * Complex.I)⁻¹ : ℂ) * (G i i - star (G i i))
      = (((G i i).im : ℝ) : ℂ) := by
    have hz : G i i - star (G i i)
        = (2 * Complex.I) * (((G i i).im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
      ring
    rw [hz]
    field_simp
  -- Combine: hentry says ↑t * ∑ = RHS? Actually hentry has • not *? Fix:
  have hentry2 : (t : ℂ) * (∑ k, G i k * ((r k).im : ℂ) * star (G i k))
      = ((2 * Complex.I)⁻¹ : ℂ) * (G i i - star (G i i)) := by
    simpa [smul_eq_mul] using hentry
  rw [hLHS, hRHS] at hentry2
  have hre : t * ∑ k, (r k).im * ‖G i k‖ ^ 2 = (G i i).im := by
    exact Complex.ofReal_injective hentry2
  have hsum_le : (∑ k, ‖G i k‖ ^ 2) ≤ Cg / (t * c) := by
    have hlow_sum : c * ∑ k, ‖G i k‖ ^ 2 ≤ ∑ k, (r k).im * ‖G i k‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hlow k) (sq_nonneg _)
    have ht_sum : t * (c * ∑ k, ‖G i k‖ ^ 2) ≤ Cg := by
      calc t * (c * ∑ k, ‖G i k‖ ^ 2)
          ≤ t * ∑ k, (r k).im * ‖G i k‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left hlow_sum ht.le
        _ = (G i i).im := hre
        _ ≤ Cg := hIm
    have htc : 0 < t * c := mul_pos ht hc
    rw [← mul_assoc, mul_comm (t * c)] at ht_sum
    exact (le_div_iff₀ htc).mpr ht_sum
  have hnorm : ‖(Real.sqrt t : ℂ)‖ ^ 2 = t := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht.le]
  have hrow_eq : AndersonAC.S78.rowTwo ((Real.sqrt t : ℂ) • G) i
      = t * ∑ j, ‖G i j‖ ^ 2 := by
    simp only [AndersonAC.S78.rowTwo, Matrix.smul_apply, norm_smul, mul_pow]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hnorm])]
    rw [← Finset.mul_sum]
  rw [hrow_eq]
  calc t * ∑ j, ‖G i j‖ ^ 2 = t * ∑ j, ‖G i j‖ ^ 2 := rfl
    _ ≤ t * (Cg / (t * c)) := by
        apply mul_le_mul_of_nonneg_left hsum_le ht.le
    _ = Cg / c := by
        field_simp

end AndersonAC.SolS78Var
