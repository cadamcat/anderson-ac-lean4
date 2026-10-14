import AndersonAC.S45.Definitions

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS6Conc

open AndersonAC.S45

private theorem posSemidef_fromBlocks_diag {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (A : CMat P) (D : CMat H)
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (fromBlocks A 0 0 D : Matrix (P ⊕ H) (P ⊕ H) ℂ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.fromBlocks hA.1 (by simp) hD.1, ?_⟩
  intro x
  have hsplit : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    rw [Matrix.fromBlocks_mulVec]
    simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  rw [hsplit]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

/-- Hermitian dilation, with both the exact norm and the square bound needed by
the concentration bridge. -/
theorem dilation_facts {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (B : Matrix P H ℂ) :
    (dilation B).IsHermitian ∧
      dilation B ^ 2 = fromBlocks (B * Bᴴ) 0 0 (Bᴴ * B) ∧
      ‖dilation B‖ = ‖B‖ ∧
      ((‖B‖ ^ 2 : ℝ) • (1 : CMat (P ⊕ H)) - dilation B ^ 2).PosSemidef := by
  let D : CMat (P ⊕ H) := dilation B
  let A : CMat P := B * Bᴴ
  let C : CMat H := Bᴴ * B
  let Q : CMat (P ⊕ H) := fromBlocks A 0 0 C
  have hHerm : D.IsHermitian := by
    change (fromBlocks (0 : Matrix P P ℂ) B Bᴴ 0)ᴴ = fromBlocks 0 B Bᴴ 0
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  have hSq : D ^ 2 = Q := by
    change (fromBlocks (0 : Matrix P P ℂ) B Bᴴ 0) ^ 2 = _
    rw [pow_two, Matrix.fromBlocks_multiply]
    simp [A, C, Q]
  have hApsd : A.PosSemidef := by
    exact Matrix.posSemidef_self_mul_conjTranspose B
  have hCpsd : C.PosSemidef := by
    exact Matrix.posSemidef_conjTranspose_mul_self B
  have hQpsd : Q.PosSemidef := by
    simpa [Q] using posSemidef_fromBlocks_diag A C hApsd hCpsd
  have hAnorm : ‖A‖ = ‖B‖ ^ 2 := by
    calc
      ‖A‖ = ‖(Bᴴ)ᴴ * Bᴴ‖ := by simp [A]
      _ = ‖Bᴴ‖ * ‖Bᴴ‖ := Matrix.l2_opNorm_conjTranspose_mul_self _
      _ = ‖B‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose]; ring
  have hCnorm : ‖C‖ = ‖B‖ ^ 2 := by
    change ‖Bᴴ * B‖ = ‖B‖ ^ 2
    calc
      ‖Bᴴ * B‖ = ‖B‖ * ‖B‖ := Matrix.l2_opNorm_conjTranspose_mul_self B
      _ = ‖B‖ ^ 2 := by ring
  have hAord : A ≤ (‖B‖ ^ 2 : ℝ) • (1 : CMat P) := by
    have hnorm : ‖A‖ ≤ ‖B‖ ^ 2 := hAnorm.le
    have h := (CStarAlgebra.norm_le_iff_le_algebraMap A (sq_nonneg ‖B‖) hApsd.nonneg).mp hnorm
    simpa [Algebra.algebraMap_eq_smul_one] using h
  have hCord : C ≤ (‖B‖ ^ 2 : ℝ) • (1 : CMat H) := by
    have hnorm : ‖C‖ ≤ ‖B‖ ^ 2 := hCnorm.le
    have h := (CStarAlgebra.norm_le_iff_le_algebraMap C (sq_nonneg ‖B‖) hCpsd.nonneg).mp hnorm
    simpa [Algebra.algebraMap_eq_smul_one] using h
  have hblockB : (‖B‖ ^ 2 : ℝ) • (1 : CMat (P ⊕ H)) - Q =
      fromBlocks ((‖B‖ ^ 2 : ℝ) • (1 : CMat P) - A) 0 0
        ((‖B‖ ^ 2 : ℝ) • (1 : CMat H) - C) := by
    ext i j <;> cases i <;> cases j <;>
      simp [Q, A, C, Matrix.fromBlocks, Matrix.one_apply]
  have hQordB : Q ≤ (‖B‖ ^ 2 : ℝ) • (1 : CMat (P ⊕ H)) := by
    rw [Matrix.le_iff, hblockB]
    apply posSemidef_fromBlocks_diag
    · simpa only [Matrix.le_iff] using hAord
    · simpa only [Matrix.le_iff] using hCord
  have hQnorm : ‖Q‖ ≤ ‖B‖ ^ 2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap Q (sq_nonneg ‖B‖) hQpsd.nonneg).2
    simpa [Algebra.algebraMap_eq_smul_one] using hQordB
  have hDsqEq : D ^ 2 = Dᴴ * D := by rw [pow_two, hHerm.eq]
  have hDnormsq : ‖D‖ ^ 2 = ‖Q‖ := by
    calc
      ‖D‖ ^ 2 = ‖D‖ * ‖D‖ := by ring
      _ = ‖Dᴴ * D‖ := (Matrix.l2_opNorm_conjTranspose_mul_self D).symm
      _ = ‖D ^ 2‖ := congrArg norm hDsqEq.symm
      _ = ‖Q‖ := by rw [hSq]
  have hDupper : ‖D‖ ≤ ‖B‖ := by
    nlinarith [hDnormsq, hQnorm, norm_nonneg D, norm_nonneg B]
  let rD : ℝ := ‖D‖ ^ 2
  have hQordD : Q ≤ rD • (1 : CMat (P ⊕ H)) := by
    have hQnormleD : ‖Q‖ ≤ ‖D‖ ^ 2 := by rw [hDnormsq]
    have h := (CStarAlgebra.norm_le_iff_le_algebraMap Q (sq_nonneg ‖D‖) hQpsd.nonneg).mp hQnormleD
    simpa [rD, Algebra.algebraMap_eq_smul_one] using h
  have hQdiffD : (rD • (1 : CMat (P ⊕ H)) - Q).PosSemidef := by
    simpa only [Matrix.le_iff] using hQordD
  have hbottom : (rD • (1 : CMat H) - C).PosSemidef := by
    have h := hQdiffD.submatrix (Sum.inr : H → P ⊕ H)
    have hEq : (rD • (1 : CMat (P ⊕ H)) - Q).submatrix Sum.inr Sum.inr =
        rD • (1 : CMat H) - C := by
      ext i j
      simp [Q, Matrix.fromBlocks, Matrix.one_apply]
    rw [hEq] at h
    exact h
  have hCordD : C ≤ rD • (1 : CMat H) := by
    rw [Matrix.le_iff]
    exact hbottom
  have hCnormD : ‖C‖ ≤ rD := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap C (sq_nonneg ‖D‖) hCpsd.nonneg).2
    simpa [rD, Algebra.algebraMap_eq_smul_one] using hCordD
  have hDlower : ‖B‖ ≤ ‖D‖ := by
    rw [hCnorm] at hCnormD
    nlinarith [hCnormD, norm_nonneg B, norm_nonneg D]
  have hDorder : ((‖B‖ ^ 2 : ℝ) • (1 : CMat (P ⊕ H)) - D ^ 2).PosSemidef := by
    rw [Matrix.le_iff] at hQordB
    simpa [hSq, D, Q] using hQordB
  refine ⟨by simpa [D] using hHerm, ?_, ?_, hDorder⟩
  · simpa [D, A, C, Q] using hSq
  · exact le_antisymm hDupper hDlower

end AndersonAC.AgentS6Conc

end
