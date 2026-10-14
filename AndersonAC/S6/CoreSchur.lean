import AndersonAC.S6.CoreAlgebra
import AndersonAC.S6.Scattering
import AndersonAC.S2.Ward

/-! Invertibility and the survivor inverse of a true core completion. -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
open AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem damped_det_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (t : ℝ) (ht : 0 < t)
    (r : ι → ℂ) (hp : ∀ i, 0 < (r i).im) : IsUnit (dampedMatrix M t r).det := by
  exact (Matrix.isUnit_iff_isUnit_det _).mp (AndersonAC.S2.damped_invertible M hM ht r hp)

theorem real_map_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    (A.map Complex.ofReal)⁻¹ = A⁻¹.map Complex.ofReal := by
  apply Matrix.inv_eq_right_inv
  change Complex.ofRealHom.mapMatrix A * Complex.ofRealHom.mapMatrix A⁻¹ = 1
  rw [← map_mul, Matrix.mul_nonsing_inv A hA, map_one]

def completedAmbient (N : Matrix (B ⊕ R) (B ⊕ R) ℝ) (t : ℝ) (r : (B ⊕ R) → ℂ) :
    Matrix (B ⊕ R) (B ⊕ R) ℂ :=
  N.map Complex.ofReal - (t : ℂ) • Matrix.diagonal (Sum.elim (fun _ => 0) (r ∘ Sum.inr))

theorem completed_schur_unit_and_inverse (N : Matrix (B ⊕ R) (B ⊕ R) ℝ)
    (hN : N.IsSymm) (t : ℝ) (ht : 0 < t) (r : (B ⊕ R) → ℂ)
    (hp : ∀ i : R, 0 < (r (Sum.inr i)).im) (hterminal : IsUnit (trueCoreMatrix N).det) :
    IsUnit (completedAmbient N t r).det ∧
      survivorBlock ((completedAmbient N t r)⁻¹) = completedInverse N t r := by
  let A : Matrix B B ℂ := (trueCoreMatrix N).map Complex.ofReal
  let B' : Matrix B R ℂ := (N.submatrix Sum.inl Sum.inr).map Complex.ofReal
  let C : Matrix R B ℂ := (N.submatrix Sum.inr Sum.inl).map Complex.ofReal
  let D : Matrix R R ℂ := dampedMatrix (N.submatrix Sum.inr Sum.inr) t (r ∘ Sum.inr)
  let E : Matrix R R ℂ := dampedMatrix (realSurvivor N) t (r ∘ Sum.inr)
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr hterminal |>.map Complex.ofRealHom.mapMatrix
  letI : Invertible A := hA.invertible
  have hAi : ⅟A = (trueCoreMatrix N)⁻¹.map Complex.ofReal := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact real_map_inverse _ hterminal
  have hschur : D - C * ⅟A * B' = E := by
    rw [hAi]
    dsimp [D, C, B', E, dampedMatrix, realSurvivor]
    have hprod :
        (N.submatrix Sum.inr Sum.inl).map Complex.ofReal *
          (trueCoreMatrix N)⁻¹.map Complex.ofReal *
          (N.submatrix Sum.inl Sum.inr).map Complex.ofReal =
        (N.submatrix Sum.inr Sum.inl * (trueCoreMatrix N)⁻¹ *
          N.submatrix Sum.inl Sum.inr).map Complex.ofReal := by
      change (N.submatrix Sum.inr Sum.inl).map Complex.ofRealHom *
          (trueCoreMatrix N)⁻¹.map Complex.ofRealHom *
          (N.submatrix Sum.inl Sum.inr).map Complex.ofRealHom =
        (N.submatrix Sum.inr Sum.inl * (trueCoreMatrix N)⁻¹ *
          N.submatrix Sum.inl Sum.inr).map Complex.ofRealHom
      simp only [Matrix.map_mul]
    rw [hprod]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Complex.ofReal_sub]
    ring
  have hE : IsUnit E := (Matrix.isUnit_iff_isUnit_det _).mpr
    (damped_det_unit (realSurvivor N) (realSurvivor_symmetric N hN) t ht (r ∘ Sum.inr) hp)
  have hS : IsUnit (D - C * ⅟A * B') := hschur.symm ▸ hE
  letI : Invertible (D - C * ⅟A * B') := hS.invertible
  have hblocks : completedAmbient N t r = Matrix.fromBlocks A B' C D := by
    ext i j
    cases i <;> cases j <;>
      simp [completedAmbient, A, B', C, D, trueCoreMatrix, dampedMatrix, Matrix.diagonal_apply, Matrix.one_apply]
  have hfull : IsUnit (Matrix.fromBlocks A B' C D) :=
    (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁).mpr hS
  letI : Invertible (Matrix.fromBlocks A B' C D) := hfull.invertible
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mp (hblocks.symm ▸ hfull), ?_⟩
  rw [hblocks, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
  change ⅟(D - C * ⅟A * B') = E⁻¹
  rw [Matrix.invOf_eq_nonsing_inv, hschur]

theorem completed_core_perturbation (M N : Matrix (B ⊕ R) (B ⊕ R) ℝ)
    (t : ℝ) (r : (B ⊕ R) → ℂ) (hchange : CoreDiagonalChange M N) :
    completedAmbient N t r = dampedMatrix M t r + Matrix.fromBlocks
      (Matrix.diagonal (fun b => ((N (Sum.inl b) (Sum.inl b) - M (Sum.inl b) (Sum.inl b) : ℝ) : ℂ) +
        (t : ℂ) * r (Sum.inl b))) 0 0 0 := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i = j
      · subst j
        simp [completedAmbient, dampedMatrix]
      · have h := hchange (Sum.inl i) (Sum.inl j) (Or.inl (by simpa using hij))
        simp [completedAmbient, dampedMatrix, hij, h]
    | inr j =>
      have h := hchange (Sum.inl i) (Sum.inr j) (Or.inr (Or.inr ⟨j, rfl⟩))
      simp [completedAmbient, dampedMatrix, h, Matrix.diagonal_apply]
  | inr i =>
    have h := hchange (Sum.inr i) j (Or.inr (Or.inl ⟨i, rfl⟩))
    cases j <;> simp [completedAmbient, dampedMatrix, h, Matrix.diagonal_apply]

end AndersonAC.SolS6
#print axioms AndersonAC.SolS6.damped_det_unit
#print axioms AndersonAC.SolS6.real_map_inverse
#print axioms AndersonAC.SolS6.completed_schur_unit_and_inverse
#print axioms AndersonAC.SolS6.completed_core_perturbation
