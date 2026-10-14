import AndersonAC.S6.HelperStatements

/-! Supported change bounds for Lemma 6.1.
Conjugated right projection, pointwise and row bounds,
HS squared ≤ 4 * core dimension. Imports only the proved
`Projection.lean` (via `HelperStatements`, no planning theorems). -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator InnerProduct

namespace AndersonAC.S6Change

variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem rangeProj_idem (C : Matrix R B ℂ) :
    AndersonAC.S6.rangeProjection C * AndersonAC.S6.rangeProjection C =
      AndersonAC.S6.rangeProjection C := by
  have h : IsStarProjection (AndersonAC.S6.matrixRange C).starProjection :=
    isStarProjection_starProjection
  have hP : IsIdempotentElem ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).symm
      (AndersonAC.S6.matrixRange C).starProjection) :=
    h.isIdempotentElem.map (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).symm
  simpa [AndersonAC.S6.rangeProjection] using hP.eq

theorem rangeProj_herm (C : Matrix R B ℂ) :
    (AndersonAC.S6.rangeProjection C).IsHermitian := by
  have h : IsStarProjection (AndersonAC.S6.matrixRange C).starProjection :=
    isStarProjection_starProjection
  have hP : IsSelfAdjoint ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).symm
      (AndersonAC.S6.matrixRange C).starProjection) :=
    IsSelfAdjoint.map (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).symm h.isSelfAdjoint
  simpa [AndersonAC.S6.rangeProjection] using hP.isHermitian

theorem rangeProj_mapstar_eq_transpose (C : Matrix R B ℂ) :
    (AndersonAC.S6.rangeProjection C).map star =
      (AndersonAC.S6.rangeProjection C)ᵀ := by
  have hH := rangeProj_herm C
  have h1 : (AndersonAC.S6.rangeProjection C)ᴴᵀ =
      (AndersonAC.S6.rangeProjection C).map star :=
    Matrix.conjTranspose_transpose _
  rw [hH.eq] at h1
  exact h1.symm

theorem supported_factor (C : Matrix R B ℂ) (D : Matrix R R ℂ)
    (hleft : AndersonAC.S6.rangeProjection C * D = D) (hs : D.IsSymm) :
    D = AndersonAC.S6.rangeProjection C * D *
      (AndersonAC.S6.rangeProjection C).map star := by
  have hQ := rangeProj_mapstar_eq_transpose C
  have hT : Dᵀ = D := hs
  have hDQ : D * (AndersonAC.S6.rangeProjection C).map star = D := by
    rw [hQ]
    have htr : (AndersonAC.S6.rangeProjection C * D)ᵀ = Dᵀ := by
      rw [hleft]
    rw [Matrix.transpose_mul] at htr
    rw [hT] at htr
    exact htr
  calc D = (AndersonAC.S6.rangeProjection C * D) *
        (AndersonAC.S6.rangeProjection C).map star := by
        rw [hleft]
        exact hDQ.symm
    _ = AndersonAC.S6.rangeProjection C * D *
        (AndersonAC.S6.rangeProjection C).map star := rfl

theorem rangeProj_norm_le_one (C : Matrix R B ℂ) :
    ‖AndersonAC.S6.rangeProjection C‖ ≤ 1 := by
  have hle : ‖(AndersonAC.S6.matrixRange C).starProjection‖ ≤ 1 :=
    Submodule.starProjection_norm_le _
  have heq : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C)‖ =
      ‖AndersonAC.S6.rangeProjection C‖ :=
    Matrix.l2_opNorm_toEuclideanCLM _
  have hPi : (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C) =
      (AndersonAC.S6.matrixRange C).starProjection := by
    simp [AndersonAC.S6.rangeProjection]
  rw [hPi] at heq
  linarith

theorem clm_apply_entry (A : Matrix R R ℂ) (i j : R) :
    ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) A
      (EuclideanSpace.single j 1)) i = A i j := by
  have h : ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) A : EuclideanSpace ℂ R →ₗ[ℂ] _) =
      Matrix.toEuclideanLin A :=
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A
  have h2 : ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) A
      (EuclideanSpace.single j 1)) i =
      (Matrix.toEuclideanLin A (EuclideanSpace.single j 1)) i := by
    rw [← h]; rfl
  rw [h2]
  exact AndersonAC.SolS6.matrix_single_apply A j i

theorem proj_clm_eq (C : Matrix R B ℂ) :
    (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C) =
      (AndersonAC.S6.matrixRange C).starProjection := by
  simp [AndersonAC.S6.rangeProjection]

theorem proj_clm_contract (C : Matrix R B ℂ) (y : EuclideanSpace ℂ R) :
    ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C) y‖ ≤ ‖y‖ := by
  rw [proj_clm_eq]
  exact Submodule.norm_starProjection_apply_le _ y

theorem proj_col_norm_sq (C : Matrix R B ℂ) (j : R) :
    ∑ i, ‖AndersonAC.S6.rangeProjection C i j‖ ^ 2 =
      AndersonAC.S6.projectionWeight C j := by
  have hc := AndersonAC.SolS6.projection_weight_eq C j
  have hP := proj_clm_eq (R := R) (B := B) C
  have hn : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C)
        (EuclideanSpace.single j 1)‖ ^ 2 =
        ∑ i, ‖AndersonAC.S6.rangeProjection C i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext i
    rw [clm_apply_entry]
  rw [hP] at hn
  linarith

theorem conj_col_norm_sq (C : Matrix R B ℂ) (j : R) :
    ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      ((AndersonAC.S6.rangeProjection C).map star)
      (EuclideanSpace.single j 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C j := by
  have hcol : ∑ i, ‖((AndersonAC.S6.rangeProjection C).map star) i j‖ ^ 2 =
      ∑ i, ‖AndersonAC.S6.rangeProjection C i j‖ ^ 2 := by
    congr 1
    funext i
    simp only [Matrix.map_apply, RCLike.star_def, RCLike.norm_conj]
  have h1 : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ ^ 2 =
        ∑ i, ‖((AndersonAC.S6.rangeProjection C).map star) i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext i
    have h : ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)) i =
        ((AndersonAC.S6.rangeProjection C).map star) i j :=
      clm_apply_entry _ i j
    rw [h]
  have h2 := proj_col_norm_sq C j
  linarith

theorem sqRow_eq_clm_norm (D : Matrix R R ℂ) (hs : D.IsSymm) (i : R) :
    AndersonAC.S6.sqRow D i =
      ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2 := by
  have hcol : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2 =
        ∑ j, ‖D j i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext j
    rw [clm_apply_entry]
  unfold AndersonAC.S6.sqRow
  rw [hcol]
  congr 1
  funext j
  have hij : D i j = D j i := by
    have hT : Dᵀ = D := hs
    have hcon := congrFun (congrFun hT i) j
    simpa [Matrix.transpose_apply] using hcon.symm
  rw [hij]

theorem finrank_range_le_b (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ) :
    Module.finrank ℂ (AndersonAC.S6.matrixRange C) ≤ b := by
  have h : AndersonAC.S6.matrixRange C =
      LinearMap.range (Matrix.toEuclideanLin C) := rfl
  rw [h]
  calc Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C))
      ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin b)) :=
        LinearMap.finrank_range_le _
    _ = b := finrank_euclideanSpace_fin

theorem sum_weights_eq_finrank (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ) :
    ∑ i, AndersonAC.S6.projectionWeight C i =
      (Module.finrank ℂ (AndersonAC.S6.matrixRange C) : ℝ) := by
  classical
  have hw : ∀ i : Fin n, AndersonAC.S6.projectionWeight C i =
      ‖(AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
        (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    have h1 := AndersonAC.SolS6.projection_weight_eq C i
    have h2 : (AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1) =
        (((AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1) :
          AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ (Fin n)) := rfl
    calc AndersonAC.S6.projectionWeight C i
        = ‖(AndersonAC.S6.matrixRange C).starProjection
          (EuclideanSpace.single i 1)‖ ^ 2 := h1
      _ = ‖(((AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1) :
          AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ (Fin n))‖ ^ 2 := by rw [h2]
      _ = ‖(AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1)‖ ^ 2 := rfl
  have hsum : ∀ i : Fin n, AndersonAC.S6.projectionWeight C i =
      ∑ k : Fin (Module.finrank ℂ (AndersonAC.S6.matrixRange C)),
        ‖inner ℂ
          (((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
            AndersonAC.S6.matrixRange C) :
            EuclideanSpace ℂ (Fin n)))
          (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    rw [hw i]
    have hP := (stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C)).sum_sq_norm_inner_right
      ((AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
        (EuclideanSpace.single i 1))
    rw [← hP]
    congr 1
    funext k
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k)
      (EuclideanSpace.single i 1)]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  have hinner : ∀ k : Fin (Module.finrank ℂ (AndersonAC.S6.matrixRange C)),
      ∑ i : Fin n, ‖inner ℂ
        (((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
          AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ (Fin n)))
        (EuclideanSpace.single i 1)‖ ^ 2 = 1 := by
    intro k
    set u : EuclideanSpace ℂ (Fin n) :=
      ((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
        AndersonAC.S6.matrixRange C) :
        EuclideanSpace ℂ (Fin n)) with hu
    have hu_norm : ‖u‖ = 1 := by
      have h1 : ‖(stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
          AndersonAC.S6.matrixRange C)‖ = 1 :=
        Orthonormal.norm_eq_one
          (stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C)).orthonormal k
      calc ‖u‖ = ‖(stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
          AndersonAC.S6.matrixRange C)‖ := rfl
        _ = 1 := h1
    have hparse : ∑ i : Fin n, ‖inner ℂ u
        (EuclideanSpace.basisFun (Fin n) ℂ i)‖ ^ 2 = 1 := by
      have h := (EuclideanSpace.basisFun (Fin n) ℂ).sum_sq_norm_inner_left u
      rw [hu_norm] at h
      simpa using h
    have heq : ∀ i : Fin n, inner ℂ u (EuclideanSpace.single i 1) =
        inner ℂ u (EuclideanSpace.basisFun (Fin n) ℂ i) := by
      intro i
      rw [EuclideanSpace.basisFun_apply]
    simp_rw [heq]
    exact hparse
  simp_rw [hinner]
  simp

theorem row_bound_aux (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ)
    (D : Matrix (Fin n) (Fin n) ℂ)
    (hDnorm : ‖D‖ ≤ 2)
    (hleft : AndersonAC.S6.rangeProjection C * D = D)
    (hs : D.IsSymm) (i : Fin n) :
    AndersonAC.S6.sqRow D i ≤ 4 * AndersonAC.S6.projectionWeight C i := by
  have hQeq : (AndersonAC.S6.rangeProjection C).map star =
      (AndersonAC.S6.rangeProjection C)ᵀ :=
    rangeProj_mapstar_eq_transpose C
  have hT : Dᵀ = D := hs
  have hDQ : D * (AndersonAC.S6.rangeProjection C).map star = D := by
    rw [hQeq]
    have htr : (AndersonAC.S6.rangeProjection C * D)ᵀ = Dᵀ := by rw [hleft]
    rw [Matrix.transpose_mul] at htr
    rw [hT] at htr
    exact htr
  have hFactor : D = AndersonAC.S6.rangeProjection C * D *
      (AndersonAC.S6.rangeProjection C).map star := by
    calc D = (AndersonAC.S6.rangeProjection C * D) *
          (AndersonAC.S6.rangeProjection C).map star := by
          rw [hleft]; exact hDQ.symm
      _ = _ := rfl
  have hCLM : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C) *
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D *
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star) := by
    calc (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        = (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C * D *
            (AndersonAC.S6.rangeProjection C).map star) := by rw [← hFactor]
      _ = _ := by rw [map_mul, map_mul]
  have hApply : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
      (EuclideanSpace.single i 1) =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C)
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1))) := by
    conv_lhs => rw [hCLM]
    simp [ContinuousLinearMap.mul_def]
  have hQnorm : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C i :=
    conj_col_norm_sq C i
  have hDle : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1))‖ ≤
      2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖ := by
    have hle : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1))‖ ≤
        ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D‖ *
          ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have heq : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D‖ = ‖D‖ :=
      Matrix.l2_opNorm_toEuclideanCLM D
    rw [heq] at hle
    calc ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1))‖
        ≤ ‖D‖ * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ := hle
      _ ≤ 2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ :=
        mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
  have hPle : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C)
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)))‖ ≤
      ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1))‖ :=
    proj_clm_contract C _
  have hDnorm_le : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
      (EuclideanSpace.single i 1)‖ ≤
      2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖ := by
    rw [hApply]
    calc ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C)
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
            ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
              ((AndersonAC.S6.rangeProjection C).map star)
              (EuclideanSpace.single i 1)))‖
        ≤ ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
            ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
              ((AndersonAC.S6.rangeProjection C).map star)
              (EuclideanSpace.single i 1))‖ := hPle
      _ ≤ 2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ := hDle
  have hsq : AndersonAC.S6.sqRow D i =
      ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2 :=
    sqRow_eq_clm_norm D hs i
  rw [hsq]
  have hsq2 : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2 ≤
      (2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖) ^ 2 := by
    have hnn : 0 ≤ ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ := norm_nonneg _
    have hle := mul_self_le_mul_self hnn hDnorm_le
    simpa [pow_two] using hle
  calc ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2
      ≤ (2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1)‖) ^ 2 := hsq2
    _ = 4 * (‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1)‖ ^ 2) := by ring
    _ = 4 * AndersonAC.S6.projectionWeight C i := by rw [hQnorm]

theorem proj_clm_norm_sq (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ) (i : Fin n) :
    ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C)
      (EuclideanSpace.single i 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C i := by
  have hP : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C) =
      (AndersonAC.S6.matrixRange C).starProjection :=
    proj_clm_eq C
  rw [hP]
  exact (AndersonAC.SolS6.projection_weight_eq C i).symm

theorem single_inner_eq' (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    inner ℂ (EuclideanSpace.single i (1 : ℂ)) v = v i := by
  rw [EuclideanSpace.inner_single_left]
  simp

theorem pointwise_bound_aux (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ)
    (D : Matrix (Fin n) (Fin n) ℂ)
    (hDnorm : ‖D‖ ≤ 2)
    (hleft : AndersonAC.S6.rangeProjection C * D = D)
    (hs : D.IsSymm) (i j : Fin n) :
    ‖D i j‖ ≤ 2 * Real.sqrt
      (AndersonAC.S6.projectionWeight C i * AndersonAC.S6.projectionWeight C j) := by
  have hQeq : (AndersonAC.S6.rangeProjection C).map star =
      (AndersonAC.S6.rangeProjection C)ᵀ :=
    rangeProj_mapstar_eq_transpose C
  have hT : Dᵀ = D := hs
  have hDQ : D * (AndersonAC.S6.rangeProjection C).map star = D := by
    rw [hQeq]
    have htr : (AndersonAC.S6.rangeProjection C * D)ᵀ = Dᵀ := by rw [hleft]
    rw [Matrix.transpose_mul] at htr
    rw [hT] at htr
    exact htr
  have hFactor : D = AndersonAC.S6.rangeProjection C * D *
      (AndersonAC.S6.rangeProjection C).map star := by
    calc D = (AndersonAC.S6.rangeProjection C * D) *
          (AndersonAC.S6.rangeProjection C).map star := by
          rw [hleft]; exact hDQ.symm
      _ = _ := rfl
  have hCLM : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C) *
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D *
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star) := by
    calc (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        = (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C * D *
            (AndersonAC.S6.rangeProjection C).map star) := by rw [← hFactor]
      _ = _ := by rw [map_mul, map_mul]
  have hPclm : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C) =
      (AndersonAC.S6.matrixRange C).starProjection :=
    proj_clm_eq C
  have hDij : D i j =
      inner ℂ ((AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1))
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))) := by
    have h1 : D i j =
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          (EuclideanSpace.single j 1)) i :=
      (clm_apply_entry D i j).symm
    have hApp : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          (EuclideanSpace.single j 1) =
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C)
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
            ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
              ((AndersonAC.S6.rangeProjection C).map star)
              (EuclideanSpace.single j 1))) := by
      conv_lhs => rw [hCLM]
      simp [ContinuousLinearMap.mul_def]
    rw [h1, hApp, hPclm]
    have h3 : (((AndersonAC.S6.matrixRange C).starProjection
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)))) i) =
        inner ℂ (EuclideanSpace.single i 1)
          ((AndersonAC.S6.matrixRange C).starProjection
            ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
              ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
                ((AndersonAC.S6.rangeProjection C).map star)
                (EuclideanSpace.single j 1)))) :=
      (single_inner_eq' n _ i).symm
    rw [h3]
    exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm
  have hPi_norm_i : ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C i :=
    (AndersonAC.SolS6.projection_weight_eq C i).symm
  have hQnorm : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C j :=
    conj_col_norm_sq C j
  have hwi : 0 ≤ AndersonAC.S6.projectionWeight C i :=
    (AndersonAC.S6.projection_coordinate C i).1
  have hcs : ‖D i j‖ ≤
      ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ *
      ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1))‖ := by
    rw [hDij]
    exact norm_inner_le_norm _ _
  have hy_le : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1))‖ ≤
      2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ := by
    have hle : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))‖ ≤
        ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D‖ *
          ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have heq : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D‖ = ‖D‖ :=
      Matrix.l2_opNorm_toEuclideanCLM D
    rw [heq] at hle
    calc ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))‖
        ≤ ‖D‖ * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)‖ := hle
      _ ≤ 2 * ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)‖ :=
        mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
  have hPi_eq : ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ =
      Real.sqrt (AndersonAC.S6.projectionWeight C i) := by
    have hnn : 0 ≤ ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ := norm_nonneg _
    rw [← hPi_norm_i, Real.sqrt_sq hnn]
  have hQ_eq : ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ =
      Real.sqrt (AndersonAC.S6.projectionWeight C j) := by
    have hnn : 0 ≤ ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ := norm_nonneg _
    rw [← hQnorm, Real.sqrt_sq hnn]
  calc ‖D i j‖ ≤ ‖(AndersonAC.S6.matrixRange C).starProjection
          (EuclideanSpace.single i 1)‖ *
        ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))‖ := hcs
    _ ≤ Real.sqrt (AndersonAC.S6.projectionWeight C i) * (2 *
        ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1)‖) := by
      rw [← hPi_eq]
      apply mul_le_mul_of_nonneg_left hy_le (norm_nonneg _)
    _ = 2 * (Real.sqrt (AndersonAC.S6.projectionWeight C i) *
        ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1)‖) := by ring
    _ = 2 * (Real.sqrt (AndersonAC.S6.projectionWeight C i) *
        Real.sqrt (AndersonAC.S6.projectionWeight C j)) := by rw [hQ_eq]
    _ = 2 * Real.sqrt (AndersonAC.S6.projectionWeight C i *
        AndersonAC.S6.projectionWeight C j) := by
      rw [← Real.sqrt_mul hwi]

end AndersonAC.S6Change

namespace AndersonAC.SolS6

theorem supportedChangeBound_proof :
    AndersonAC.SolS6.SupportedChangeBoundStatement := by
  intro b n C D hDnorm hleft hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AndersonAC.S6Change.supported_factor C D hleft hs
  · intro i j
    exact AndersonAC.S6Change.pointwise_bound_aux b n C D hDnorm hleft hs i j
  · intro i
    exact AndersonAC.S6Change.row_bound_aux b n C D hDnorm hleft hs i
  · -- hsSq ≤ 4 * b via row bounds + trace
    have hrow : ∀ i : Fin n, AndersonAC.S6.sqRow D i ≤
        4 * AndersonAC.S6.projectionWeight C i := fun i =>
      AndersonAC.S6Change.row_bound_aux b n C D hDnorm hleft hs i
    have hsum := AndersonAC.S6Change.sum_weights_eq_finrank b n C
    have hfr := AndersonAC.S6Change.finrank_range_le_b b n C
    have hle : (Module.finrank ℂ (AndersonAC.S6.matrixRange C) : ℝ) ≤ (b : ℝ) :=
      Nat.cast_le.mpr hfr
    have hsq_le : ∑ i : Fin n, AndersonAC.S6.sqRow D i ≤
        4 * (Module.finrank ℂ (AndersonAC.S6.matrixRange C) : ℝ) := by
      calc ∑ i : Fin n, AndersonAC.S6.sqRow D i
          ≤ ∑ i : Fin n, 4 * AndersonAC.S6.projectionWeight C i :=
            Finset.sum_le_sum (fun i _ => hrow i)
        _ = 4 * ∑ i : Fin n, AndersonAC.S6.projectionWeight C i := by
            rw [Finset.mul_sum]
        _ = 4 * (Module.finrank ℂ (AndersonAC.S6.matrixRange C) : ℝ) := by
            rw [hsum]
    calc AndersonAC.S6.hsSq D = ∑ i : Fin n, AndersonAC.S6.sqRow D i := rfl
      _ ≤ 4 * (Module.finrank ℂ (AndersonAC.S6.matrixRange C) : ℝ) := hsq_le
      _ ≤ 4 * (b : ℝ) := by
          apply mul_le_mul_of_nonneg_left hle (by norm_num)

#print axioms AndersonAC.SolS6.supportedChangeBound_proof

end AndersonAC.SolS6
