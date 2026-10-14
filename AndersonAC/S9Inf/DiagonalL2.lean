import OAI.MathematicalPhysics.Anderson.Certificates

/-! Bounded diagonal multipliers on a discrete ℓ² space. -/

noncomputable section

open scoped lp ENNReal

namespace AndersonAC.SolS9Inf

variable {ι : Type*}

def diagonalL2Linear (w : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, ‖w i‖ ≤ M) : ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(ι, ℂ) where
  toFun v := ⟨fun i => w i * v i,
    ((lp.memℓp v).const_mul (M : ℂ)).mono' (fun i => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _))⟩
  map_add' v u := by ext i; exact mul_add _ _ _
  map_smul' c v := by ext i; exact mul_left_comm _ _ _

theorem diagonalL2Linear_norm_le (w : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, ‖w i‖ ≤ M) (v : ℓ²(ι, ℂ)) :
    ‖diagonalL2Linear w M hM hw v‖ ≤ M * ‖v‖ := by
  have h : ‖diagonalL2Linear w M hM hw v‖ ≤ ‖(M : ℂ) • v‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro i
    change ‖w i * v i‖ ≤ ‖(M : ℂ) * v i‖
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _)
  calc
    _ ≤ ‖(M : ℂ) • v‖ := h
    _ = ‖(M : ℂ)‖ * ‖v‖ := lp.norm_const_smul (c := (M : ℂ))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) v
    _ = M * ‖v‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]

def diagonalL2 (w : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, ‖w i‖ ≤ M) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  (diagonalL2Linear w M hM hw).mkContinuous M (diagonalL2Linear_norm_le w M hM hw)

@[simp] theorem diagonalL2_apply (w : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, ‖w i‖ ≤ M) (v : ℓ²(ι, ℂ)) (i : ι) :
    diagonalL2 w M hM hw v i = w i * v i := rfl

theorem norm_diagonalL2_le (w : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, ‖w i‖ ≤ M) : ‖diagonalL2 w M hM hw‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  exact diagonalL2Linear_norm_le w M hM hw v

def diagonalRealL2 (w : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, |w i| ≤ M) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  diagonalL2 (fun i => (w i : ℂ)) M hM
    (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hw i)

@[simp] theorem diagonalRealL2_apply (w : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, |w i| ≤ M) (v : ℓ²(ι, ℂ)) (i : ι) :
    diagonalRealL2 w M hM hw v i = (w i : ℂ) * v i := rfl

theorem norm_diagonalRealL2_le (w : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, |w i| ≤ M) : ‖diagonalRealL2 w M hM hw‖ ≤ M :=
  norm_diagonalL2_le _ M hM _

end AndersonAC.SolS9Inf
