import AndersonAC.AgentS6Conc.Support
import AndersonAC.AgentS6Conc.Dilation
import AndersonAC.S45.MatrixConcentrationProof

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS6Conc

open AndersonAC.S45

def vecRow {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) : Matrix Unit (Fin D) ℂ :=
  (vecColumn y)ᴴ

theorem vecRow_norm {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) :
    ‖vecRow y‖ = ‖y‖ := by
  rw [vecRow, Matrix.l2_opNorm_conjTranspose, vecColumn_norm]

noncomputable def dilationIndex (D : ℕ) : (Unit ⊕ Fin D) ≃ Fin (Fintype.card (Unit ⊕ Fin D)) :=
  Fintype.equivFin (Unit ⊕ Fin D)

def vectorDilation {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) :
    Matrix (Fin (Fintype.card (Unit ⊕ Fin D))) (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ :=
  reindex (dilationIndex D) (dilationIndex D) (dilation (vecRow y))

theorem vectorDilation_norm {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) :
    ‖vectorDilation y‖ = ‖y‖ := by
  rw [vectorDilation, AndersonAC.AgentS45.norm_reindex]
  exact (dilation_facts (vecRow y)).2.2.1.trans (vecRow_norm y)

theorem vectorDilation_hermitian {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) :
    (vectorDilation y).IsHermitian := by
  have h := (dilation_facts (vecRow y)).1
  change (dilation (vecRow y)).submatrix (dilationIndex D).symm (dilationIndex D).symm |>.IsHermitian
  exact h.submatrix _

theorem vectorDilation_square_le {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) :
    (vectorDilation y ^ 2 ≤ (‖y‖ ^ 2 : ℝ) •
      (1 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D))) (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ)) := by
  let e := dilationIndex D
  let B := vecRow y
  let M := dilation B
  have hfact := dilation_facts B
  have hbound : (‖B‖ ^ 2 : ℝ) • (1 : CMat (Unit ⊕ Fin D)) - M ^ 2 |>.PosSemidef := by
    exact hfact.2.2.2
  have hsub := hbound.submatrix e.symm
  have hnorm : ‖B‖ = ‖y‖ := vecRow_norm y
  have hsq : (reindex e e M) ^ 2 = reindex e e (M ^ 2) := by
    rw [pow_two, pow_two]
    simp only [reindex_apply, submatrix_mul_equiv]
  have hEq : ((‖y‖ ^ 2 : ℝ) •
        (1 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D))) (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ) -
        (reindex e e M) ^ 2) =
      ((‖B‖ ^ 2 : ℝ) • (1 : CMat (Unit ⊕ Fin D)) - M ^ 2).submatrix e.symm e.symm := by
    rw [hsq, hnorm]
    ext i j
    simp [reindex_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [Matrix.le_iff]
  change ((‖y‖ ^ 2 : ℝ) •
      (1 : Matrix (Fin (Fintype.card (Unit ⊕ Fin D))) (Fin (Fintype.card (Unit ⊕ Fin D))) ℂ) -
      (reindex e e M) ^ 2).PosSemidef
  rw [hEq]
  exact hsub

end AndersonAC.AgentS6Conc

end
