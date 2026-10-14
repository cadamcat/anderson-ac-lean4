import AndersonAC.S6.Definitions

/-! Physical core-completion algebra before the projection estimates. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem scattering_survivor_block (t : ℝ) (r : (B ⊕ R) → ℂ)
    (g : Matrix (B ⊕ R) (B ⊕ R) ℂ) :
    AndersonAC.S6.survivorBlock (AndersonAC.S6.scattering t r g) =
      AndersonAC.S6.scattering t (r ∘ Sum.inr) (AndersonAC.S6.survivorBlock g) := by
  ext i j
  simp only [AndersonAC.S6.scattering, AndersonAC.S6.scatteringOfDamping,
    AndersonAC.S6.sqrtDamping, AndersonAC.S6.imagDamping, AndersonAC.S6.survivorBlock,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply]
  simp [Matrix.one_apply]

theorem scattering_difference (t : ℝ) (r : R → ℂ) (g h : Matrix R R ℂ) :
    AndersonAC.S6.scattering t r g - AndersonAC.S6.scattering t r h =
      (2 * Complex.I * (t : ℂ)) •
        (AndersonAC.S6.sqrtDamping (AndersonAC.S6.imagDamping r) * (g - h) *
          AndersonAC.S6.sqrtDamping (AndersonAC.S6.imagDamping r)) := by
  simp only [AndersonAC.S6.scattering, AndersonAC.S6.scatteringOfDamping,
    Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  abel

theorem scattering_difference_scaled (t : ℝ) (ht : 0 ≤ t) (r : R → ℂ) (g h : Matrix R R ℂ) :
    AndersonAC.S6.scattering t r g - AndersonAC.S6.scattering t r h =
      (2 * Complex.I * (Real.sqrt t : ℂ)) •
        (AndersonAC.S6.sqrtDamping (AndersonAC.S6.imagDamping r) *
          AndersonAC.S6.scaledInverse t (g - h) *
          AndersonAC.S6.sqrtDamping (AndersonAC.S6.imagDamping r)) := by
  rw [scattering_difference]
  simp only [AndersonAC.S6.scaledInverse, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  have hsq : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    norm_cast
    nlinarith [Real.sq_sqrt ht]
  calc
    2 * Complex.I * (t : ℂ) = 2 * Complex.I * ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) := by rw [hsq]
    _ = _ := by ring

theorem realSurvivor_symmetric (N : Matrix (B ⊕ R) (B ⊕ R) ℝ) (hN : N.IsSymm) :
    (AndersonAC.S6.realSurvivor N).IsSymm := by
  let A := N.submatrix Sum.inl Sum.inl
  let C := N.submatrix Sum.inr Sum.inl
  let D := N.submatrix Sum.inr Sum.inr
  have hA : A.IsSymm := by apply Matrix.IsSymm.ext; intro i j; exact hN.apply _ _
  have hD : D.IsSymm := by apply Matrix.IsSymm.ext; intro i j; exact hN.apply _ _
  have hCt : N.submatrix Sum.inl Sum.inr = Cᵀ := by
    ext i j
    exact (hN.apply (Sum.inl i) (Sum.inr j)).symm
  have hAi : A⁻¹.IsSymm := hA.inv
  change (D - C * A⁻¹ * N.submatrix Sum.inl Sum.inr).IsSymm
  rw [hCt]
  change (D - C * A⁻¹ * Cᵀ)ᵀ = D - C * A⁻¹ * Cᵀ
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    hD.eq, hAi.eq]
  simp only [Matrix.mul_assoc]

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.scattering_survivor_block
#print axioms AndersonAC.SolS6.scattering_difference
#print axioms AndersonAC.SolS6.scattering_difference_scaled
#print axioms AndersonAC.SolS6.realSurvivor_symmetric
