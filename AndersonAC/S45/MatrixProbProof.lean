import AndersonAC.S45.Definitions
import AndersonAC.S45.HelperStatements2

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

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

theorem dilation_square_proof {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (B : Matrix P H ℂ) :
    (dilation B).IsHermitian ∧
      dilation B ^ 2 = fromBlocks (B * Bᴴ) 0 0 (Bᴴ * B) ∧
      ‖dilation B‖ = ‖B‖ := by
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
    ext i j <;> cases i <;> cases j <;> simp [Q, A, C, Matrix.fromBlocks, Matrix.one_apply]
  have hQordB : Q ≤ (‖B‖ ^ 2 : ℝ) • (1 : CMat (P ⊕ H)) := by
    rw [Matrix.le_iff, hblockB]
    apply posSemidef_fromBlocks_diag
    · simpa only [Matrix.le_iff] using hAord
    · simpa only [Matrix.le_iff] using hCord
  have hQnorm : ‖Q‖ ≤ ‖B‖ ^ 2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap Q (sq_nonneg ‖B‖) hQpsd.nonneg).2
    simpa [Algebra.algebraMap_eq_smul_one] using hQordB
  have hDsqEq : D ^ 2 = Dᴴ * D := by
    rw [pow_two, hHerm.eq]
  have hDnormsq : ‖D‖ ^ 2 = ‖Q‖ := by
    calc
      ‖D‖ ^ 2 = ‖D‖ * ‖D‖ := by ring
      _ = ‖Dᴴ * D‖ := (Matrix.l2_opNorm_conjTranspose_mul_self D).symm
      _ = ‖D ^ 2‖ := congrArg norm hDsqEq.symm
      _ = ‖Q‖ := by rw [hSq]
  have hDupper : ‖D‖ ≤ ‖B‖ := by nlinarith [hDnormsq, hQnorm, norm_nonneg D, norm_nonneg B]
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
  refine ⟨by simpa [D] using hHerm, ?_, ?_⟩
  · simpa [D, A, C, Q] using hSq
  · exact le_antisymm hDupper hDlower

theorem predictable_stopping_proof {Ω P : Type*} [MeasurableSpace Ω]
    [Fintype P] [DecidableEq P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (Y : ℕ → Ω → CMat P)
    (v : ℕ → Ω → ℝ) (J V : ℝ) (s : ℕ → Ω → ℝ)
    (hY : MatrixDiffHyp μ ℱ Y v J V)
    (hs : ∀ k, StronglyMeasurable[ℱ k] (s k))
    (h01 : ∀ k ω, s k ω = 0 ∨ s k ω = 1) :
    MatrixDiffHyp μ ℱ
      (fun k ω => if k = 0 then 0 else s (k - 1) ω • Y k ω)
      (fun k ω => s k ω * v k ω) J V := by
  let Y' : ℕ → Ω → CMat P := fun k ω => if k = 0 then 0 else s (k - 1) ω • Y k ω
  let v' : ℕ → Ω → ℝ := fun k ω => s k ω * v k ω
  have hs_norm (k : ℕ) : ∀ ω, ‖s k ω‖ ≤ 1 := by
    intro ω
    rcases h01 k ω with h | h <;> simp [h]
  have hs_nn (k : ℕ) (ω : Ω) : 0 ≤ s k ω := by
    rcases h01 k ω with h | h <;> simp [h]
  have hs_idem (k : ℕ) (ω : Ω) : (s k ω) ^ 2 = s k ω := by
    rcases h01 k ω with h | h <;> simp [h]
  have hsucc (k : ℕ) (ω : Ω) : Y' (k + 1) ω = s k ω • Y (k + 1) ω := by
    simp [Y']
  have hstopInt (k : ℕ) : Integrable (Y' k) μ := by
    by_cases hk : k = 0
    · simp [Y', hk]
    · have hsmeas : AEStronglyMeasurable (s (k - 1)) μ :=
        ((hs (k - 1)).mono (ℱ.le (k - 1))).aestronglyMeasurable
      have hbound : ∀ᵐ ω ∂μ, ‖s (k - 1) ω‖ ≤ 1 := ae_of_all _ (hs_norm (k - 1))
      have hm := (hY.integrable k).bdd_smul 1 hsmeas hbound
      refine hm.congr ?_
      filter_upwards with ω
      simp [Y', hk]
  have hstopSqInt (k : ℕ) : Integrable (fun ω => (Y' k ω) ^ 2) μ := by
    by_cases hk : k = 0
    · simp [Y', hk]
    · have hsmeas : AEStronglyMeasurable (s (k - 1)) μ :=
        ((hs (k - 1)).mono (ℱ.le (k - 1))).aestronglyMeasurable
      have hbound : ∀ᵐ ω ∂μ, ‖s (k - 1) ω‖ ≤ 1 := ae_of_all _ (hs_norm (k - 1))
      have hmul := (hY.square_integrable k).bdd_smul 1 hsmeas hbound
      refine hmul.congr ?_
      filter_upwards with ω
      rcases h01 (k - 1) ω with hs0 | hs1
      · simp [Y', hk, hs0]
      · simp [Y', hk, hs1]
  have hstopAdapted : StronglyAdapted ℱ Y' := by
    intro k
    by_cases hk : k = 0
    · simpa [Y', hk] using
        (stronglyMeasurable_const : StronglyMeasurable[ℱ k] (fun _ : Ω => (0 : CMat P)))
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hsmeas : StronglyMeasurable[ℱ k] (s (k - 1)) :=
        (hs (k - 1)).mono (ℱ.mono (by omega))
      have hymeas : StronglyMeasurable[ℱ k] (Y k) := hY.adapted k
      have hprod := hsmeas.smul hymeas
      have hfun : (s (k - 1) • Y k : Ω → CMat P) =
          fun ω => s (k - 1) ω • Y k ω := rfl
      simpa [Y', hk, ← hfun] using hprod
  refine ⟨hstopAdapted, hstopInt, hstopSqInt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    filter_upwards [hY.hermitian k] with ω hω
    simp only [Nat.succ_ne_zero, Nat.succ_sub_one]
    rcases h01 k ω with hs0 | hs1
    · simp [hs0]
    · simpa [hs1] using hω
  · intro k
    have hprodInt : Integrable (fun ω => s k ω • Y (k + 1) ω) μ := by
      have hbound : ∀ᵐ ω ∂μ, ‖s k ω‖ ≤ 1 := ae_of_all _ (hs_norm k)
      exact (hY.integrable (k + 1)).bdd_smul 1
        ((hs k).mono (ℱ.le k)).aestronglyMeasurable hbound
    have hce := condExp_smul_of_aestronglyMeasurable_left (m := ℱ k)
      (hs k).aestronglyMeasurable hprodInt (hY.integrable (k + 1))
    filter_upwards [hce, hY.centered k] with ω hce hcent
    change μ[fun ω => Y' (k + 1) ω | ℱ k] ω = 0
    rw [show (fun ω => Y' (k + 1) ω) = fun ω => s k ω • Y (k + 1) ω from funext (hsucc k)]
    change μ[s k • Y (k + 1) | ℱ k] ω = 0
    rw [hce]
    change s k ω • μ[Y (k + 1) | ℱ k] ω = 0
    rw [hcent]
    simp
  · intro k
    filter_upwards [hY.jump k] with ω hω
    simp only [Nat.succ_ne_zero, Nat.succ_sub_one]
    rcases h01 k ω with hs0 | hs1
    · simp [hs0]
      have hJnn : 0 ≤ J := by
        have hex : ∃ ω, ‖Y (k + 1) ω‖ ≤ J := hY.jump k |>.exists
        rcases hex with ⟨ω, hω⟩
        exact (norm_nonneg _).trans hω
      exact hJnn
    · simpa [hs1] using hω
  · intro k
    exact (hs k).mul (hY.predictable k)
  · intro k
    filter_upwards [hY.variance_nonneg k] with ω hv
    rcases h01 k ω with hs0 | hs1
    · simp [hs0]
    · simpa [hs1] using hv
  · intro k
    have hprodInt : Integrable (fun ω => s k ω • (Y (k + 1) ω) ^ 2) μ := by
      have hbound : ∀ᵐ ω ∂μ, ‖s k ω‖ ≤ 1 := ae_of_all _ (hs_norm k)
      exact (hY.square_integrable (k + 1)).bdd_smul 1
        ((hs k).mono (ℱ.le k)).aestronglyMeasurable hbound
    have hce := condExp_smul_of_aestronglyMeasurable_left (m := ℱ k)
      (hs k).aestronglyMeasurable hprodInt (hY.square_integrable (k + 1))
    filter_upwards [hce, hY.variance k] with ω hce hvar
    have hsq : (fun ω => (Y' (k + 1) ω) ^ 2) =
        fun ω => s k ω • (Y (k + 1) ω) ^ 2 := by
      funext ω
      rw [hsucc]
      rcases h01 k ω with hs0 | hs1
      · simp [hs0]
      · simp [hs1]
    rw [hsq]
    change μ[s k • (fun ω => (Y (k + 1) ω) ^ 2) | ℱ k] ω ≤ (s k ω * v k ω) • 1
    rw [hce]
    rcases h01 k ω with hs0 | hs1
    · simp [hs0]
    · simpa [hs1] using hvar
  · intro n
    have hvnn : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ v k ω := by
      exact ae_all_iff.2 (fun k => hY.variance_nonneg k)
    filter_upwards [hvnn, hY.total_variance n] with ω hv htotal
    calc
      (∑ k ∈ Finset.range n, v' k ω) ≤ ∑ k ∈ Finset.range n, v k ω := by
        apply Finset.sum_le_sum
        intro k hk
        rcases h01 k ω with hs0 | hs1
        · simp [v', hs0, hv k]
        · simp [v', hs1]
      _ ≤ V := htotal


private noncomputable def matrixAdjointCLM {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] :
    Matrix P H ℂ →L[ℝ] Matrix H P ℂ := by
  let e : Matrix P H ℂ →ₗ[ℝ] Matrix H P ℂ :=
    { toFun := fun A => Aᴴ
      map_add' := by intro A B; ext i j; simp [Matrix.conjTranspose]
      map_smul' := by intro c A; ext i j; simp [Matrix.conjTranspose] }
  exact e.mkContinuous 1 (by
    intro A
    simpa [e] using (Matrix.l2_opNorm_conjTranspose A).le)

@[simp] private theorem matrixAdjointCLM_apply {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (A : Matrix P H ℂ) :
    matrixAdjointCLM A = Aᴴ := by
  simp [matrixAdjointCLM, LinearMap.mkContinuous_apply]

private theorem matrixAdjointCLM_norm {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (A : Matrix P H ℂ) :
    ‖matrixAdjointCLM A‖ = ‖A‖ := by
  rw [matrixAdjointCLM_apply, Matrix.l2_opNorm_conjTranspose]

private theorem matrix_mul_bilinear {P H K : Type*}
    [Fintype P] [Fintype H] [Fintype K]
    [DecidableEq P] [DecidableEq H] [DecidableEq K] :
    IsBoundedBilinearMap ℝ
      (fun p : Matrix P H ℂ × Matrix H K ℂ => p.1 * p.2) where
  add_left := by intro A A' B; simp [Matrix.add_mul]
  smul_left := by intro c A B; simp [Matrix.smul_mul]
  add_right := by intro A B B'; simp [Matrix.mul_add]
  smul_right := by intro c A B; simp [Matrix.mul_smul]
  bound := by
    refine ⟨1, by norm_num, fun A B => ?_⟩
    simpa using (Matrix.l2_opNorm_mul A B)

private noncomputable def matrixMulCLM {P H K : Type*}
    [Fintype P] [Fintype H] [Fintype K]
    [DecidableEq P] [DecidableEq H] [DecidableEq K] :
    Matrix P H ℂ →L[ℝ] Matrix H K ℂ →L[ℝ] Matrix P K ℂ :=
  (matrix_mul_bilinear (P := P) (H := H) (K := K)).toContinuousLinearMap

private noncomputable def matrixMulCLMFlip {P H K : Type*}
    [Fintype P] [Fintype H] [Fintype K]
    [DecidableEq P] [DecidableEq H] [DecidableEq K] :
    Matrix H K ℂ →L[ℝ] Matrix P H ℂ →L[ℝ] Matrix P K ℂ :=
  (matrix_mul_bilinear (P := P) (H := H) (K := K)).symm.toContinuousLinearMap

private lemma integrable_matrix_mul {Ω P H K : Type*} [MeasurableSpace Ω]
    [Fintype P] [Fintype H] [Fintype K]
    [DecidableEq P] [DecidableEq H] [DecidableEq K]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : Ω → Matrix P H ℂ) (g : Ω → Matrix H K ℂ) (C D : ℝ) (hD : 0 ≤ D)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) (hgb : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ D) :
    Integrable (fun ω => f ω * g ω) μ := by
  have hcont := (matrix_mul_bilinear (P := P) (H := H) (K := K)).continuous
  refine Integrable.of_bound (hcont.comp_aestronglyMeasurable (hf.prodMk hg)) (C * D) ?_
  filter_upwards [hfb, hgb] with ω hωf hωg
  calc
    ‖f ω * g ω‖ ≤ ‖f ω‖ * ‖g ω‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ C * D := by
      calc
        ‖f ω‖ * ‖g ω‖ ≤ ‖f ω‖ * D := mul_le_mul_of_nonneg_left hωg (norm_nonneg _)
        _ ≤ C * D := mul_le_mul_of_nonneg_right hωf hD


set_option maxHeartbeats 0 in
theorem conditionalCenteringFixed_proof : ConditionalCenteringFixed := by
  intro Ω P H m mΩ instP instH instDP instDH μ hμ hm B J hB hJ hbound
  let b : Ω → Matrix P H ℂ := fun ω => μ[B | m] ω
  let adj : Matrix P H ℂ →L[ℝ] Matrix H P ℂ := matrixAdjointCLM
  let Bs : Ω → Matrix H P ℂ := fun ω => adj (B ω)
  let bs : Ω → Matrix H P ℂ := fun ω => adj (b ω)
  have hBint : Integrable B μ := Integrable.of_bound hB J hbound
  have hbBound : ∀ᵐ ω ∂μ, ‖b ω‖ ≤ J := by
    simpa [b] using
      (ae_bdd_norm_condExp_of_ae_bdd_norm (m := m) hbound)
  have hbSM : StronglyMeasurable[m] b := by
    simpa [b] using (stronglyMeasurable_condExp (m := m) (f := B))
  have hbAEM : AEStronglyMeasurable b μ :=
    (hbSM.mono hm).aestronglyMeasurable
  have hBsAEM : AEStronglyMeasurable Bs μ := by
    simpa [Bs, adj] using adj.continuous.comp_aestronglyMeasurable hB
  have hbsSM : StronglyMeasurable[m] bs := by
    simpa [bs, adj] using adj.continuous.comp_stronglyMeasurable hbSM
  have hbsAEM : AEStronglyMeasurable bs μ :=
    (hbsSM.mono hm).aestronglyMeasurable
  have hBsBound : ∀ᵐ ω ∂μ, ‖Bs ω‖ ≤ J := by
    filter_upwards [hbound] with ω hω
    change ‖adj (B ω)‖ ≤ J
    rw [matrixAdjointCLM_norm]
    exact hω
  have hbsBound : ∀ᵐ ω ∂μ, ‖bs ω‖ ≤ J := by
    filter_upwards [hbBound] with ω hω
    change ‖adj (b ω)‖ ≤ J
    rw [matrixAdjointCLM_norm]
    exact hω
  have hBsInt : Integrable Bs μ := by
    simpa [Bs, adj] using adj.integrable_comp hBint
  have hbInt : Integrable b μ := by
    simpa [b] using (integrable_condExp : Integrable (μ[B | m]) μ)
  have hbsInt : Integrable bs μ := by
    simpa [bs, adj] using adj.integrable_comp hbInt
  have hstarCE : μ[Bs | m] =ᵐ[μ] bs := by
    have hleft : (fun ω => adj (B ω)) = (⇑adj ∘ B) := by funext ω; rfl
    have hright : (⇑adj ∘ μ[B | m]) = (fun ω => adj (μ[B | m] ω)) := by
      funext ω
      rfl
    have h₁ : μ[(fun ω => adj (B ω)) | m] =ᵐ[μ] μ[⇑adj ∘ B | m] :=
      condExp_congr_ae (m := m) (EventuallyEq.of_eq hleft)
    have h₂ := (ContinuousLinearMap.comp_condExp_comm (m := m) hBint adj).symm
    have h₃ : (⇑adj ∘ μ[B | m]) =ᵐ[μ] (fun ω => adj (μ[B | m] ω)) :=
      EventuallyEq.of_eq hright
    simpa [Bs, bs, b] using h₁.trans (h₂.trans h₃)
  have hBBsInt : Integrable (fun ω => B ω * Bs ω) μ :=
    integrable_matrix_mul B Bs J J hJ hB hBsAEM hbound hBsBound
  have hBbsInt : Integrable (fun ω => B ω * bs ω) μ :=
    integrable_matrix_mul B bs J J hJ hB hbsAEM hbound hbsBound
  have hbBsInt : Integrable (fun ω => b ω * Bs ω) μ :=
    integrable_matrix_mul b Bs J J hJ hbAEM hBsAEM hbBound hBsBound
  have hbsBInt : Integrable (fun ω => bs ω * B ω) μ :=
    integrable_matrix_mul bs B J J hJ hbsAEM hB hbsBound hbound
  have hBsBInt : Integrable (fun ω => Bs ω * B ω) μ :=
    integrable_matrix_mul Bs B J J hJ hBsAEM hB hBsBound hbound
  have hbsbInt : Integrable (fun ω => bs ω * b ω) μ :=
    integrable_matrix_mul bs b J J hJ hbsAEM hbAEM hbsBound hbBound
  have hbbStarInt : Integrable (fun ω => b ω * bs ω) μ :=
    integrable_matrix_mul b bs J J hJ hbAEM hbsAEM hbBound hbsBound
  have hbbStarSM : StronglyMeasurable[m] (fun ω => b ω * bs ω) := by
    exact (matrix_mul_bilinear (P := P) (H := H) (K := P)).continuous
      |>.comp_stronglyMeasurable (hbSM.prodMk hbsSM)
  have hbsbSM : StronglyMeasurable[m] (fun ω => bs ω * b ω) := by
    exact (matrix_mul_bilinear (P := H) (H := P) (K := H)).continuous
      |>.comp_stronglyMeasurable (hbsSM.prodMk hbSM)
  have hbbStarCE : μ[(fun ω => b ω * bs ω) | m] =ᵐ[μ] fun ω => b ω * bs ω := by
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm hbbStarSM hbbStarInt)
  have hbsbCE : μ[(fun ω => bs ω * b ω) | m] =ᵐ[μ] fun ω => bs ω * b ω := by
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm hbsbSM hbsbInt)
  have hpullBbs :
      μ[(fun ω => B ω * bs ω) | m] =ᵐ[μ] fun ω => b ω * bs ω := by
    have h := condExp_stronglyMeasurable_bilin_of_bound
      (matrixMulCLMFlip (P := P) (H := H) (K := P)) hm hbsSM hBint J hbsBound
    simpa [matrixMulCLMFlip, matrix_mul_bilinear, bs, adj, b] using h
  have hpullbBs :
      μ[(fun ω => b ω * Bs ω) | m] =ᵐ[μ] fun ω => b ω * μ[Bs | m] ω := by
    have h := condExp_stronglyMeasurable_bilin_of_bound
      (matrixMulCLM (P := P) (H := H) (K := P)) hm hbSM hBsInt J hbBound
    simpa [matrixMulCLM, matrix_mul_bilinear] using h
  have hpullBsb :
      μ[(fun ω => Bs ω * b ω) | m] =ᵐ[μ] fun ω => μ[Bs | m] ω * b ω := by
    have h := condExp_stronglyMeasurable_bilin_of_bound
      (matrixMulCLMFlip (P := H) (H := P) (K := H)) hm hbSM hBsInt J hbBound
    simpa [matrixMulCLMFlip, matrix_mul_bilinear] using h
  have hpullbsB :
      μ[(fun ω => bs ω * B ω) | m] =ᵐ[μ] fun ω => bs ω * μ[B | m] ω := by
    have h := condExp_stronglyMeasurable_bilin_of_bound
      (matrixMulCLM (P := H) (H := P) (K := H)) hm hbsSM hBint J hbsBound
    simpa [matrixMulCLM, matrix_mul_bilinear] using h
  have hpullbBs' :
      μ[(fun ω => b ω * Bs ω) | m] =ᵐ[μ] fun ω => b ω * bs ω := by
    filter_upwards [hpullbBs, hstarCE] with ω h1 h2
    rw [h1, h2]
  have hpullBsb' :
      μ[(fun ω => Bs ω * b ω) | m] =ᵐ[μ] fun ω => bs ω * b ω := by
    filter_upwards [hpullBsb, hstarCE] with ω h1 h2
    rw [h1, h2]
  have hpullbsB' :
      μ[(fun ω => bs ω * B ω) | m] =ᵐ[μ] fun ω => bs ω * b ω := by
    filter_upwards [hpullbsB] with ω h1
    simpa [b] using h1
  have hD : ∀ᵐ ω ∂μ, ‖B ω - b ω‖ ≤ 2 * J := by
    filter_upwards [hbound, hbBound] with ω hBω hbω
    calc
      ‖B ω - b ω‖ ≤ ‖B ω‖ + ‖b ω‖ := norm_sub_le _ _
      _ ≤ J + J := add_le_add hBω hbω
      _ = 2 * J := by ring
  have hDae : AEStronglyMeasurable (fun ω => B ω - b ω) μ := hB.sub hbAEM
  have hDstarAEM : AEStronglyMeasurable (fun ω => adj (B ω - b ω)) μ :=
    adj.continuous.comp_aestronglyMeasurable hDae
  have hDstarBound : ∀ᵐ ω ∂μ, ‖adj (B ω - b ω)‖ ≤ 2 * J := by
    filter_upwards [hD] with ω hω
    rw [matrixAdjointCLM_norm]
    exact hω
  have hDprodInt : Integrable
      (fun ω => (B ω - b ω) * adj (B ω - b ω)) μ :=
    integrable_matrix_mul (fun ω => B ω - b ω) (fun ω => adj (B ω - b ω))
      (2 * J) (2 * J) (by positivity) hDae hDstarAEM hD hDstarBound
  have hDprodInt' : Integrable
      (fun ω => adj (B ω - b ω) * (B ω - b ω)) μ :=
    integrable_matrix_mul (fun ω => adj (B ω - b ω)) (fun ω => B ω - b ω)
      (2 * J) (2 * J) (by positivity) hDstarAEM hDae hDstarBound hD
  let A₁ : Ω → Matrix P P ℂ := fun ω => B ω * Bs ω
  let C₁ : Ω → Matrix P P ℂ := fun ω => B ω * bs ω
  let D₁ : Ω → Matrix P P ℂ := fun ω => b ω * Bs ω
  let E₁ : Ω → Matrix P P ℂ := fun ω => b ω * bs ω
  have hpoint₁ : (fun ω => (B ω - b ω) * (B ω - b ω)ᴴ) =
      fun ω => (A₁ ω - C₁ ω) - D₁ ω + E₁ ω := by
    funext ω
    simp [A₁, C₁, D₁, E₁, Bs, bs, adj, matrixAdjointCLM_apply,
      Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hAC₁ : Integrable (fun ω => A₁ ω - C₁ ω) μ := hBBsInt.sub hBbsInt
  have hACD₁ : Integrable (fun ω => (A₁ ω - C₁ ω) - D₁ ω) μ := hAC₁.sub hbBsInt
  have hsum₁ : (fun ω => (A₁ ω - C₁ ω) - D₁ ω + E₁ ω) =
      (fun ω => (A₁ ω - C₁ ω) - D₁ ω) + (fun ω => b ω * bs ω) := by
    funext ω
    rfl
  have hlin₁ : μ[(fun ω => (A₁ ω - C₁ ω) - D₁ ω + E₁ ω) | m] =ᵐ[μ]
      (fun ω => μ[A₁ | m] ω - μ[C₁ | m] ω - μ[D₁ | m] ω + μ[E₁ | m] ω) := by
    have hsub₁raw := condExp_sub hBBsInt hBbsInt m
    have hsub₂raw := condExp_sub hAC₁ hbBsInt m
    have hfunSub₁ : (fun ω => A₁ ω - C₁ ω) =
        (fun ω => B ω * Bs ω) - (fun ω => B ω * bs ω) := by
      funext ω
      rfl
    have hsub₁ : μ[(fun ω => A₁ ω - C₁ ω) | m] =ᵐ[μ]
        fun ω => μ[A₁ | m] ω - μ[C₁ | m] ω := by
      exact (condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ)
        (EventuallyEq.of_eq hfunSub₁)).trans hsub₁raw
    have hfunSub₂ : (fun ω => A₁ ω - C₁ ω - D₁ ω) =
        (fun ω => A₁ ω - C₁ ω) - (fun ω => b ω * Bs ω) := by
      funext ω
      rfl
    have hsub₂ : μ[(fun ω => A₁ ω - C₁ ω - D₁ ω) | m] =ᵐ[μ]
        fun ω => μ[(fun ω => A₁ ω - C₁ ω) | m] ω - μ[D₁ | m] ω := by
      exact (condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ)
        (EventuallyEq.of_eq hfunSub₂)).trans hsub₂raw
    have hadd := condExp_add hACD₁ hbbStarInt m
    have hCEsum := condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ) (EventuallyEq.of_eq hsum₁)
    filter_upwards [hsub₁, hsub₂, hadd, hCEsum] with ω h1 h2 h3 hsum
    calc
      μ[fun ω => (A₁ ω - C₁ ω) - D₁ ω + E₁ ω | m] ω =
          μ[(fun ω => (A₁ ω - C₁ ω) - D₁ ω) + (fun ω => b ω * bs ω) | m] ω := hsum
      _ = (μ[fun ω => (A₁ ω - C₁ ω) - D₁ ω | m] + μ[fun ω => b ω * bs ω | m]) ω := h3
      _ = μ[A₁ | m] ω - μ[C₁ | m] ω - μ[D₁ | m] ω + μ[E₁ | m] ω := by
        change μ[fun ω => A₁ ω - C₁ ω - D₁ ω | m] ω +
          μ[fun ω => b ω * bs ω | m] ω = _
        rw [h2, h1]
  have hcov₁ : μ[(fun ω => (B ω - b ω) * (B ω - b ω)ᴴ) | m] =ᵐ[μ]
      fun ω => μ[(fun ω => B ω * (B ω)ᴴ) | m] ω - b ω * (b ω)ᴴ := by
    filter_upwards [condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ) (EventuallyEq.of_eq hpoint₁), hlin₁,
      hpullBbs, hpullbBs', hbbStarCE] with ω hpoint hlin hcross₁ hcross₂ hbb
    rw [hpoint, hlin, hcross₁, hcross₂, hbb]
    simp [A₁, Bs, bs, adj, matrixAdjointCLM_apply]
  let A₂ : Ω → Matrix H H ℂ := fun ω => Bs ω * B ω
  let C₂ : Ω → Matrix H H ℂ := fun ω => Bs ω * b ω
  let D₂ : Ω → Matrix H H ℂ := fun ω => bs ω * B ω
  let E₂ : Ω → Matrix H H ℂ := fun ω => bs ω * b ω
  have hpoint₂ : (fun ω => (B ω - b ω)ᴴ * (B ω - b ω)) =
      fun ω => (A₂ ω - C₂ ω) - D₂ ω + E₂ ω := by
    funext ω
    simp [A₂, C₂, D₂, E₂, Bs, bs, adj, matrixAdjointCLM_apply,
      Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hBsBInt₂ : Integrable A₂ μ := by simpa [A₂] using hBsBInt
  have hBs_bInt : Integrable C₂ μ := by
    exact integrable_matrix_mul Bs b J J hJ hBsAEM hbAEM hBsBound hbBound
  have hAC₂ : Integrable (fun ω => A₂ ω - C₂ ω) μ := hBsBInt₂.sub hBs_bInt
  have hACD₂ : Integrable (fun ω => (A₂ ω - C₂ ω) - D₂ ω) μ := hAC₂.sub hbsBInt
  have hsum₂ : (fun ω => (A₂ ω - C₂ ω) - D₂ ω + E₂ ω) =
      (fun ω => (A₂ ω - C₂ ω) - D₂ ω) + (fun ω => bs ω * b ω) := by
    funext ω
    rfl
  have hlin₂ : μ[(fun ω => (A₂ ω - C₂ ω) - D₂ ω + E₂ ω) | m] =ᵐ[μ]
      (fun ω => μ[A₂ | m] ω - μ[C₂ | m] ω - μ[D₂ | m] ω + μ[E₂ | m] ω) := by
    have hsub₁raw := condExp_sub hBsBInt₂ hBs_bInt m
    have hsub₂raw := condExp_sub hAC₂ hbsBInt m
    have hfunSub₁ : (fun ω => A₂ ω - C₂ ω) =
        (fun ω => Bs ω * B ω) - (fun ω => Bs ω * b ω) := by
      funext ω
      rfl
    have hsub₁ : μ[(fun ω => A₂ ω - C₂ ω) | m] =ᵐ[μ]
        fun ω => μ[A₂ | m] ω - μ[C₂ | m] ω := by
      exact (condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ)
        (EventuallyEq.of_eq hfunSub₁)).trans hsub₁raw
    have hfunSub₂ : (fun ω => A₂ ω - C₂ ω - D₂ ω) =
        (fun ω => A₂ ω - C₂ ω) - (fun ω => bs ω * B ω) := by
      funext ω
      rfl
    have hsub₂ : μ[(fun ω => A₂ ω - C₂ ω - D₂ ω) | m] =ᵐ[μ]
        fun ω => μ[(fun ω => A₂ ω - C₂ ω) | m] ω - μ[D₂ | m] ω := by
      exact (condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ)
        (EventuallyEq.of_eq hfunSub₂)).trans hsub₂raw
    have hadd := condExp_add hACD₂ hbsbInt m
    have hCEsum := condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ) (EventuallyEq.of_eq hsum₂)
    filter_upwards [hsub₁, hsub₂, hadd, hCEsum] with ω h1 h2 h3 hsum
    calc
      μ[fun ω => (A₂ ω - C₂ ω) - D₂ ω + E₂ ω | m] ω =
          μ[(fun ω => (A₂ ω - C₂ ω) - D₂ ω) + (fun ω => bs ω * b ω) | m] ω := hsum
      _ = (μ[fun ω => (A₂ ω - C₂ ω) - D₂ ω | m] + μ[fun ω => bs ω * b ω | m]) ω := h3
      _ = μ[A₂ | m] ω - μ[C₂ | m] ω - μ[D₂ | m] ω + μ[E₂ | m] ω := by
        change μ[fun ω => A₂ ω - C₂ ω - D₂ ω | m] ω +
          μ[fun ω => bs ω * b ω | m] ω = _
        rw [h2, h1]
  have hcov₂ : μ[(fun ω => (B ω - b ω)ᴴ * (B ω - b ω)) | m] =ᵐ[μ]
      fun ω => μ[(fun ω => (B ω)ᴴ * B ω) | m] ω - (b ω)ᴴ * b ω := by
    filter_upwards [condExp_congr_ae (m := m) (m₀ := mΩ) (μ := μ) (EventuallyEq.of_eq hpoint₂), hlin₂,
      hpullBsb', hpullbsB', hbsbCE] with ω hpoint hlin hcross₁ hcross₂ hbb
    rw [hpoint, hlin, hcross₁, hcross₂, hbb]
    simp [A₂, Bs, bs, adj, matrixAdjointCLM_apply]
  exact ⟨hD, hcov₁, hcov₂⟩


set_option maxHeartbeats 0 in
theorem matrix_zero_variance_proof {Ω P : Type*} [MeasurableSpace Ω]
    [Fintype P] [DecidableEq P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : ℕ → Ω → CMat P) (v : ℕ → Ω → ℝ) (J : ℝ)
    (hY : MatrixDiffHyp μ ℱ Y v J 0) :
    ∀ᵐ ω ∂μ, ∀ n, partialSum Y n ω = 0 := by
  have hvAll : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ v k ω :=
    ae_all_iff.2 (fun k => hY.variance_nonneg k)
  have hvZero (k : ℕ) : ∀ᵐ ω ∂μ, v k ω = 0 := by
    filter_upwards [hvAll, hY.total_variance (k + 1)] with ω hv htotal
    have hmem : k ∈ Finset.range (k + 1) := by simp
    have hle : v k ω ≤ ∑ j ∈ Finset.range (k + 1), v j ω :=
      Finset.single_le_sum (fun j _ => hv j) hmem
    have hsum : 0 ≤ ∑ j ∈ Finset.range (k + 1), v j ω :=
      Finset.sum_nonneg fun j _ => hv j
    have hsum0 : ∑ j ∈ Finset.range (k + 1), v j ω ≤ 0 := by simpa using htotal
    linarith [hv k, hle, hsum, hsum0]
  have hDiffZero (k : ℕ) : ∀ᵐ ω ∂μ, Y (k + 1) ω = 0 := by
    let F : Ω → CMat P := fun ω => (Y (k + 1) ω) ^ 2
    have hFint : Integrable F μ := by simpa [F] using hY.square_integrable (k + 1)
    have hVarZero : ∀ᵐ ω ∂μ, μ[F | ℱ k] ω ≤ 0 := by
      filter_upwards [hY.variance k, hvZero k] with ω hvar hv
      simpa [F, hv] using hvar
    have hNegPSD : ∀ᵐ ω ∂μ, (-(μ[F | ℱ k] ω)).PosSemidef := by
      filter_upwards [hVarZero] with ω hvar
      simpa using (Matrix.le_iff.mp hvar)
    let traceRe : CMat P →ₗ[ℝ] ℝ :=
      (Complex.reCLM.toLinearMap).comp (Matrix.traceLinearMap P ℝ ℂ)
    let traceReCLM : CMat P →L[ℝ] ℝ :=
      ⟨traceRe, traceRe.continuous_of_finiteDimensional⟩
    have hTraceCE : ∀ᵐ ω ∂μ, traceReCLM (μ[F | ℱ k] ω) ≤ 0 := by
      filter_upwards [hNegPSD] with ω hpsd
      have htr : 0 ≤ (Matrix.trace (-(μ[F | ℱ k] ω))).re :=
        (Complex.nonneg_iff.mp hpsd.trace_nonneg).1
      have htr' : 0 ≤ - (Matrix.trace (μ[F | ℱ k] ω)).re := by simpa using htr
      have hle : (Matrix.trace (μ[F | ℱ k] ω)).re ≤ 0 := neg_nonneg.mp htr'
      simpa [traceReCLM, traceRe, Matrix.traceLinearMap] using hle
    have hHerm : ∀ᵐ ω ∂μ, (Y (k + 1) ω).IsHermitian := hY.hermitian k
    have hTraceFNonneg : ∀ᵐ ω ∂μ, 0 ≤ traceReCLM (F ω) := by
      filter_upwards [hHerm] with ω hH
      have hpsd : (F ω).PosSemidef := by
        simpa [F, pow_two, hH.eq] using
          (Matrix.posSemidef_conjTranspose_mul_self (Y (k + 1) ω))
      have htr : 0 ≤ (Matrix.trace (F ω)).re := (Complex.nonneg_iff.mp hpsd.trace_nonneg).1
      simpa [traceReCLM, traceRe, Matrix.traceLinearMap] using htr
    have hFCEint : Integrable (μ[F | ℱ k]) μ := integrable_condExp
    have hMean : (∫ ω, traceReCLM (μ[F | ℱ k] ω) ∂μ) =
        ∫ ω, traceReCLM (F ω) ∂μ := by
      have hIntCE : (∫ ω, μ[F | ℱ k] ω ∂μ) = ∫ ω, F ω ∂μ :=
        integral_condExp (m := ℱ k) (m₀ := ‹MeasurableSpace Ω›) (μ := μ) (f := F) (ℱ.le k)
      calc
        _ = traceReCLM (∫ ω, μ[F | ℱ k] ω ∂μ) := traceReCLM.integral_comp_comm hFCEint
        _ = traceReCLM (∫ ω, F ω ∂μ) := by rw [hIntCE]
        _ = _ := (traceReCLM.integral_comp_comm hFint).symm
    have hTraceFInt : Integrable (fun ω => traceReCLM (F ω)) μ :=
      traceReCLM.integrable_comp hFint
    have hTraceCELe : ∫ ω, traceReCLM (μ[F | ℱ k] ω) ∂μ ≤ 0 :=
      integral_nonpos_of_ae hTraceCE
    have hTraceFLe : ∫ ω, traceReCLM (F ω) ∂μ ≤ 0 := by
      rw [← hMean]
      exact hTraceCELe
    have hTraceFNonnegInt : 0 ≤ ∫ ω, traceReCLM (F ω) ∂μ :=
      integral_nonneg_of_ae hTraceFNonneg
    have hTraceFZero : (∫ ω, traceReCLM (F ω) ∂μ) = 0 :=
      (le_antisymm hTraceFNonnegInt hTraceFLe).symm
    have hTraceFZeroAE : (fun ω => traceReCLM (F ω)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hTraceFNonneg hTraceFInt).mp hTraceFZero
    have hTraceZero : ∀ᵐ ω ∂μ, Matrix.trace (F ω) = 0 := by
      filter_upwards [hTraceFZeroAE, hHerm] with ω hRe hH
      have hpsd : (F ω).PosSemidef := by
        simpa [F, pow_two, hH.eq] using
          (Matrix.posSemidef_conjTranspose_mul_self (Y (k + 1) ω))
      have him : 0 = (Matrix.trace (F ω)).im :=
        (Complex.nonneg_iff.mp hpsd.trace_nonneg).2
      apply Complex.ext
      · simpa [traceReCLM, traceRe, Matrix.traceLinearMap] using hRe
      · exact him.symm
    filter_upwards [hTraceZero, hHerm] with ω htr hH
    have hpsd : (F ω).PosSemidef := by
      simpa [F, pow_two, hH.eq] using
        (Matrix.posSemidef_conjTranspose_mul_self (Y (k + 1) ω))
    have hFzero : F ω = 0 := hpsd.trace_eq_zero_iff.mp htr
    have hnormsq : ‖Y (k + 1) ω‖ ^ 2 = 0 := by
      calc
        ‖Y (k + 1) ω‖ ^ 2 = ‖Y (k + 1) ω‖ * ‖Y (k + 1) ω‖ := by ring
        _ = ‖(Y (k + 1) ω)ᴴ * Y (k + 1) ω‖ :=
          (Matrix.l2_opNorm_conjTranspose_mul_self _).symm
        _ = ‖F ω‖ := by
          rw [hH.eq]
          change ‖Y (k + 1) ω * Y (k + 1) ω‖ = ‖(Y (k + 1) ω) ^ 2‖
          rw [pow_two]
        _ = 0 := by simp [hFzero]
    have hnorm0 : ‖Y (k + 1) ω‖ = 0 := by nlinarith [norm_nonneg (Y (k + 1) ω)]
    exact norm_eq_zero.mp hnorm0
  have hAllDiffZero : ∀ᵐ ω ∂μ, ∀ k, Y (k + 1) ω = 0 :=
    ae_all_iff.2 hDiffZero
  filter_upwards [hAllDiffZero] with ω hω
  intro n
  simp [partialSum, hω]


set_option maxHeartbeats 0 in
theorem uniform_slot_square_proof {Ω P : Type*} [MeasurableSpace Ω]
    [Fintype P] [DecidableEq P] (M : ℕ) (hM : 0 < M)
    (μ : Fin M → Measure Ω) (hμ : ∀ x, IsProbabilityMeasure (μ x))
    (B : Fin M → Ω → CMat P) (J σ : ℝ)
    (hB : ∀ x, AEStronglyMeasurable (B x) (μ x))
    (hbound : ∀ x ω, ‖B x ω‖ ≤ J)
    (hstack : ∀ ω : Fin M → Ω,
      (∑ x, (B x (ω x)) ^ 2) ≤ σ • (1 : CMat P)) :
    (1 / (M : ℝ)) • (∑ x, ∫ ω, (B x ω) ^ 2 ∂(μ x)) ≤
      (σ / M) • (1 : CMat P) := by
  let ν : Measure (Fin M → Ω) := Measure.pi μ
  letI : ∀ x : Fin M, IsProbabilityMeasure (μ x) := hμ
  letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let F : (Fin M → Ω) → CMat P := fun ω =>
    σ • (1 : CMat P) - ∑ x, (B x (ω x)) ^ 2
  have hB2AEM (x : Fin M) : AEStronglyMeasurable (fun ω => (B x ω) ^ 2) (μ x) := by
    exact (by fun_prop : Continuous (fun A : CMat P => A ^ 2)).comp_aestronglyMeasurable (hB x)
  have hB2Bound (x : Fin M) (ω : Ω) : ‖(B x ω) ^ 2‖ ≤ J ^ 2 := by
    calc
      ‖(B x ω) ^ 2‖ = ‖B x ω * B x ω‖ := by rw [pow_two]
      _ ≤ ‖B x ω‖ * ‖B x ω‖ := norm_mul_le _ _
      _ ≤ J ^ 2 := by nlinarith [hbound x ω, norm_nonneg (B x ω)]
  have hB2Int (x : Fin M) : Integrable (fun ω => (B x ω) ^ 2) (μ x) :=
    Integrable.of_bound (hB2AEM x) (J ^ 2) (ae_of_all _ (hB2Bound x))
  have hProductPreserving (x : Fin M) : MeasurePreserving (Function.eval x) ν (μ x) := by
    dsimp [ν]
    exact measurePreserving_eval μ x
  have hB2ProductAEM (x : Fin M) :
      AEStronglyMeasurable (fun ω : Fin M → Ω => (B x (ω x)) ^ 2) ν := by
    exact (hB2AEM x).comp_quasiMeasurePreserving (hProductPreserving x).quasiMeasurePreserving
  have hB2ProductBound (x : Fin M) :
      ∀ᵐ ω ∂ν, ‖(B x (ω x)) ^ 2‖ ≤ J ^ 2 :=
    ae_of_all _ (fun ω => hB2Bound x (ω x))
  have hB2ProductInt (x : Fin M) :
      Integrable (fun ω : Fin M → Ω => (B x (ω x)) ^ 2) ν :=
    Integrable.of_bound (hB2ProductAEM x) (J ^ 2) (hB2ProductBound x)
  have hStackInt : Integrable (fun ω : Fin M → Ω => ∑ x, (B x (ω x)) ^ 2) ν := by
    exact integrable_finsetSum Finset.univ (fun x _ => hB2ProductInt x)
  have hFInt : Integrable F ν := by
    dsimp [F]
    exact (integrable_const (σ • (1 : CMat P))).sub hStackInt
  have hFPSD (ω : Fin M → Ω) : (F ω).PosSemidef := by
    change (σ • (1 : CMat P) - ∑ x, (B x (ω x)) ^ 2).PosSemidef
    exact Matrix.le_iff.mp (hstack ω)
  have hFnonneg : ∀ ω, 0 ≤ F ω := fun ω => (hFPSD ω).nonneg
  have hIntegralPSD : (∫ ω, F ω ∂ν).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    exact integral_nonneg_of_ae (ae_of_all _ hFnonneg)
  have hStackIntegral :
      (∫ ω : Fin M → Ω, (∑ x, (B x (ω x)) ^ 2) ∂ν) =
        ∑ x, ∫ ω, (B x ω) ^ 2 ∂(μ x) := by
    calc
      _ = ∑ x, ∫ ω : Fin M → Ω, (B x (ω x)) ^ 2 ∂ν :=
        integral_finsetSum Finset.univ (fun x _ => hB2ProductInt x)
      _ = ∑ x, ∫ ω, (B x ω) ^ 2 ∂(μ x) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hmap := (hProductPreserving x).map_eq
        have hB2MapAEM : AEStronglyMeasurable (fun ω => (B x ω) ^ 2)
            (Measure.map (fun f : Fin M → Ω => f x) ν) := by
          rw [hmap]
          exact hB2AEM x
        calc
          ∫ ω : Fin M → Ω, (B x (ω x)) ^ 2 ∂ν =
              ∫ ω, (B x ω) ^ 2 ∂Measure.map (fun f : Fin M → Ω => f x) ν := by
                exact (integral_map (μ := ν) (φ := fun f : Fin M → Ω => f x)
                  (measurable_pi_apply x).aemeasurable hB2MapAEM).symm
          _ = ∫ ω, (B x ω) ^ 2 ∂(μ x) := by rw [hmap]
  have hIntegralEq :
      (∫ ω, F ω ∂ν) = (σ • (1 : CMat P)) -
        (∑ x, ∫ ω, (B x ω) ^ 2 ∂(μ x)) := by
    dsimp [F]
    rw [integral_sub (integrable_const _) hStackInt, hStackIntegral]
    simp
  have hSumOrder :
      (∑ x, ∫ ω, (B x ω) ^ 2 ∂(μ x)) ≤ σ • (1 : CMat P) := by
    rw [Matrix.le_iff]
    rw [← hIntegralEq]
    exact hIntegralPSD
  calc
    (1 / (M : ℝ)) • (∑ x, ∫ ω, (B x ω) ^ 2 ∂(μ x)) ≤
        (1 / (M : ℝ)) • (σ • (1 : CMat P)) :=
      smul_le_smul_of_nonneg_left hSumOrder (by positivity)
    _ = (σ / M) • (1 : CMat P) := by
      rw [smul_smul]
      congr 1
      ring

end AndersonAC.AgentS45
