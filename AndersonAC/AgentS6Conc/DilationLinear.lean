import AndersonAC.AgentS6Conc.VectorDilation

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS6Conc

open AndersonAC.S45

def vectorDilationLinear (D : ℕ) :
    EuclideanSpace ℂ (Fin D) →ₗ[ℝ]
      Matrix (Fin (Fintype.card (Unit ⊕ Fin D))) (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ where
  toFun := vectorDilation
  map_add' y z := by
    have hcol : vecColumn (y + z) = vecColumn y + vecColumn z := by
      ext i j
      simp [vecColumn]
    have hrow : vecRow (y + z) = vecRow y + vecRow z := by
      unfold vecRow
      rw [hcol, Matrix.conjTranspose_add]
    have hdil : dilation (vecRow (y + z)) = dilation (vecRow y) + dilation (vecRow z) := by
      rw [hrow]
      ext i j
      cases i <;> cases j <;> simp [dilation, Matrix.fromBlocks]
    unfold vectorDilation
    rw [hdil]
    ext i j
    rfl
  map_smul' a y := by
    have hcol : vecColumn (a • y) = (a : ℂ) • vecColumn y := by
      ext i j
      simp [vecColumn]
    have hrow : vecRow (a • y) = (a : ℂ) • vecRow y := by
      unfold vecRow
      rw [hcol, Matrix.conjTranspose_smul]
      simp
    have hdil : dilation (vecRow (a • y)) = (a : ℂ) • dilation (vecRow y) := by
      rw [hrow]
      ext i j
      cases i <;> cases j <;> simp [dilation, Matrix.fromBlocks]
    unfold vectorDilation
    rw [hdil]
    ext i j
    rfl

noncomputable def vectorDilationCLM (D : ℕ) :
    EuclideanSpace ℂ (Fin D) →L[ℝ]
      Matrix (Fin (Fintype.card (Unit ⊕ Fin D))) (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ :=
  (vectorDilationLinear D).mkContinuous 1 (by
    intro y
    change ‖vectorDilation y‖ ≤ 1 * ‖y‖
    rw [vectorDilation_norm]
    simp)

theorem vectorDilationCLM_apply {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) :
    vectorDilationCLM D y = vectorDilation y := rfl

end AndersonAC.AgentS6Conc

end
