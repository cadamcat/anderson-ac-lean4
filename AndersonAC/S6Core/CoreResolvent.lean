import AndersonAC.S6.Definitions

noncomputable section

open scoped Matrix

namespace AndersonAC.SolS6

theorem coreResolvent_proof :
    ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
      (g : Matrix (B ⊕ R) (B ⊕ R) ℂ) (V : Matrix B B ℂ),
      IsUnit g.det → IsUnit V.det →
      IsUnit (g⁻¹ + Matrix.fromBlocks V 0 0 0).det →
      IsUnit (1 + V * AndersonAC.S6.coreBlock g).det ∧
      AndersonAC.S6.survivorBlock
          ((g⁻¹ + Matrix.fromBlocks V 0 0 0)⁻¹) -
          AndersonAC.S6.survivorBlock g =
        -(AndersonAC.S6.crossBlock g *
          (1 + V * AndersonAC.S6.coreBlock g)⁻¹ * V *
          g.submatrix Sum.inl Sum.inr) := by
  intro B R _ _ _ _ g V hg hV hnew
  let a : Matrix B B ℂ := AndersonAC.S6.coreBlock g
  let b : Matrix B R ℂ := g.submatrix Sum.inl Sum.inr
  let c : Matrix R B ℂ := AndersonAC.S6.crossBlock g
  let d : Matrix R R ℂ := AndersonAC.S6.survivorBlock g
  let P : Matrix (B ⊕ R) (B ⊕ R) ℂ := Matrix.fromBlocks V 0 0 0
  let Q : Matrix (B ⊕ R) (B ⊕ R) ℂ := g⁻¹ + P
  let A : Matrix B B ℂ := 1 + a * V
  let H : Matrix B B ℂ := 1 + V * a
  let D : Matrix (B ⊕ R) (B ⊕ R) ℂ := Matrix.fromBlocks A 0 (c * V) 1

  have hgblocks : g = Matrix.fromBlocks a b c d := by
    ext i j
    cases i <;> cases j <;>
      simp [a, b, c, d, AndersonAC.S6.coreBlock,
        AndersonAC.S6.crossBlock, AndersonAC.S6.survivorBlock]

  have hDrepr : D = 1 + g * P := by
    rw [hgblocks]
    ext i j
    cases i <;> cases j <;>
      simp [D, P, A, a, c, Matrix.fromBlocks_multiply, Matrix.one_apply]

  have hQfactor : Q = g⁻¹ * D := by
    calc
      Q = g⁻¹ + P := rfl
      _ = g⁻¹ * (1 + g * P) := by
        rw [Matrix.mul_add]
        simp [Matrix.nonsing_inv_mul_cancel_left g P hg]
      _ = g⁻¹ * D := by rw [← hDrepr]

  have hDfactor : D = g * Q := by
    calc
      D = 1 + g * P := hDrepr
      _ = g * (g⁻¹ + P) := by
        rw [Matrix.mul_add]
        simp [Matrix.mul_nonsing_inv g hg]
      _ = g * Q := rfl

  have hQunit : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 hnew
  have hgunit : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hg
  have hDunit : IsUnit D := by
    rw [hDfactor]
    exact hgunit.mul hQunit

  have hAunit : IsUnit A := by
    have hblock : IsUnit (Matrix.fromBlocks A 0 (c * V) (1 : Matrix R R ℂ)) := by
      simpa [D] using hDunit
    exact (Matrix.isUnit_fromBlocks_zero₁₂).mp hblock |>.1

  have hHdet : IsUnit H.det := by
    have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
    have hdet : H.det = A.det := by
      dsimp [H, A]
      exact Matrix.det_one_add_mul_comm V a
    rw [hdet]
    exact hAdet

  have hHunit : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).2 hHdet
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDunit
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit

  have hDinv : D⁻¹ = Matrix.fromBlocks A⁻¹ 0 (-(c * V * A⁻¹)) 1 := by
    simpa [D] using
      (Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff A (c * V)
        (1 : Matrix R R ℂ)
        (show IsUnit A ↔ IsUnit (1 : Matrix R R ℂ) from
          ⟨fun _ => isUnit_one, fun _ => hAunit⟩))

  have hQinvRight : Q * (D⁻¹ * g) = 1 := by
    calc
      Q * (D⁻¹ * g) = (g⁻¹ * D) * (D⁻¹ * g) := by rw [hQfactor]
      _ = g⁻¹ * (D * D⁻¹) * g := by simp [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv D hDdet]
        simp [Matrix.nonsing_inv_mul g hg]

  have hQinv : Q⁻¹ = D⁻¹ * g := by
    calc
      Q⁻¹ = Q⁻¹ * 1 := by simp
      _ = Q⁻¹ * (Q * (D⁻¹ * g)) := by rw [hQinvRight]
      _ = (Q⁻¹ * Q) * (D⁻¹ * g) := by rw [Matrix.mul_assoc]
      _ = D⁻¹ * g := by rw [Matrix.nonsing_inv_mul Q hnew]; simp

  have hsurvivor :
      AndersonAC.S6.survivorBlock (D⁻¹ * g) = -(c * V * A⁻¹) * b + d := by
    rw [hDinv, hgblocks]
    ext i j
    simp [AndersonAC.S6.survivorBlock, Matrix.fromBlocks_multiply,
      Matrix.mul_assoc, Matrix.one_mul]

  have hcomm : H⁻¹ * V = V * A⁻¹ := by
    have hmul : H * V = V * A := by
      dsimp [H, A]
      noncomm_ring
    calc
      H⁻¹ * V = H⁻¹ * (H * (V * A⁻¹)) := by
        congr 1
        calc
          V = (H * V) * A⁻¹ := by
            rw [hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAdet]
            simp
          _ = H * (V * A⁻¹) := by simp [Matrix.mul_assoc]
      _ = V * A⁻¹ := by
        calc
          H⁻¹ * (H * (V * A⁻¹)) = (H⁻¹ * H) * (V * A⁻¹) := by
            rw [← Matrix.mul_assoc]
          _ = V * A⁻¹ := by
            rw [Matrix.nonsing_inv_mul H hHdet]
            simp

  have hterm : c * H⁻¹ * V * b = (c * V * A⁻¹) * b := by
    calc
      c * H⁻¹ * V * b = c * (H⁻¹ * V) * b := by simp [Matrix.mul_assoc]
      _ = c * (V * A⁻¹) * b := by rw [hcomm]
      _ = (c * V * A⁻¹) * b := by simp [Matrix.mul_assoc]

  constructor
  · exact hHdet
  · rw [hQinv, hsurvivor]
    rw [hterm]
    simp [d, AndersonAC.S6.survivorBlock, Matrix.neg_mul]

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.coreResolvent_proof
