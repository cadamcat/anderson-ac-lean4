import AndersonAC.S6Change.SupportedChange
import AndersonAC.S6.Statements

/-! Generic finite-index versions of the accepted supported-change helper.
The core endpoint uses arbitrary finite B/R, including active subtypes. -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator InnerProduct

namespace AndersonAC.SolS6.Supported
open AndersonAC.S6Change
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem finrank_range_le_b (C : Matrix R B ℂ) :
    Module.finrank ℂ (AndersonAC.S6.matrixRange C) ≤ Fintype.card B := by
  have h : AndersonAC.S6.matrixRange C =
      LinearMap.range (Matrix.toEuclideanLin C) := rfl
  rw [h]
  calc Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C))
      ≤ Module.finrank ℂ (EuclideanSpace ℂ B) :=
        LinearMap.finrank_range_le _
    _ = Fintype.card B := finrank_euclideanSpace

theorem sum_weights_eq_finrank (C : Matrix R B ℂ) :
    ∑ i, AndersonAC.S6.projectionWeight C i =
      (Module.finrank ℂ (AndersonAC.S6.matrixRange C) : ℝ) := by
  classical
  have hw : ∀ i : R, AndersonAC.S6.projectionWeight C i =
      ‖(AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
        (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    have h1 := AndersonAC.SolS6.projection_weight_eq C i
    have h2 : (AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1) =
        (((AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1) :
          AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ R) := rfl
    calc AndersonAC.S6.projectionWeight C i
        = ‖(AndersonAC.S6.matrixRange C).starProjection
          (EuclideanSpace.single i 1)‖ ^ 2 := h1
      _ = ‖(((AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1) :
          AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ R)‖ ^ 2 := by rw [h2]
      _ = ‖(AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1)‖ ^ 2 := rfl
  have hsum : ∀ i : R, AndersonAC.S6.projectionWeight C i =
      ∑ k : Fin (Module.finrank ℂ (AndersonAC.S6.matrixRange C)),
        ‖inner ℂ
          (((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
            AndersonAC.S6.matrixRange C) :
            EuclideanSpace ℂ R))
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
      ∑ i : R, ‖inner ℂ
        (((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
          AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ R))
        (EuclideanSpace.single i 1)‖ ^ 2 = 1 := by
    intro k
    set u : EuclideanSpace ℂ R :=
      ((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
        AndersonAC.S6.matrixRange C) :
        EuclideanSpace ℂ R) with hu
    have hu_norm : ‖u‖ = 1 := by
      have h1 : ‖(stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
          AndersonAC.S6.matrixRange C)‖ = 1 :=
        Orthonormal.norm_eq_one
          (stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C)).orthonormal k
      calc ‖u‖ = ‖(stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
          AndersonAC.S6.matrixRange C)‖ := rfl
        _ = 1 := h1
    have hparse : ∑ i : R, ‖inner ℂ u
        (EuclideanSpace.basisFun R ℂ i)‖ ^ 2 = 1 := by
      have h := (EuclideanSpace.basisFun R ℂ).sum_sq_norm_inner_left u
      rw [hu_norm] at h
      simpa using h
    have heq : ∀ i : R, inner ℂ u (EuclideanSpace.single i 1) =
        inner ℂ u (EuclideanSpace.basisFun R ℂ i) := by
      intro i
      rw [EuclideanSpace.basisFun_apply]
    simp_rw [heq]
    exact hparse
  simp_rw [hinner]
  simp

theorem row_bound_aux (C : Matrix R B ℂ)
    (D : Matrix R R ℂ)
    (hDnorm : ‖D‖ ≤ 2)
    (hleft : AndersonAC.S6.rangeProjection C * D = D)
    (hs : D.IsSymm) (i : R) :
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
  have hCLM : (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D =
      (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C) *
      (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D *
      (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star) := by
    calc (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        = (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C * D *
            (AndersonAC.S6.rangeProjection C).map star) := by rw [← hFactor]
      _ = _ := by rw [map_mul, map_mul]
  have hApply : (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
      (EuclideanSpace.single i 1) =
      (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C)
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1))) := by
    conv_lhs => rw [hCLM]
    simp [ContinuousLinearMap.mul_def]
  have hQnorm : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C i :=
    conj_col_norm_sq C i
  have hDle : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1))‖ ≤
      2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖ := by
    have hle : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1))‖ ≤
        ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D‖ *
          ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have heq : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D‖ = ‖D‖ :=
      Matrix.l2_opNorm_toEuclideanCLM D
    rw [heq] at hle
    calc ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1))‖
        ≤ ‖D‖ * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ := hle
      _ ≤ 2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ :=
        mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
  have hPle : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C)
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)))‖ ≤
      ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1))‖ :=
    proj_clm_contract C _
  have hDnorm_le : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
      (EuclideanSpace.single i 1)‖ ≤
      2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖ := by
    rw [hApply]
    calc ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C)
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
            ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
              ((AndersonAC.S6.rangeProjection C).map star)
              (EuclideanSpace.single i 1)))‖
        ≤ ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
            ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
              ((AndersonAC.S6.rangeProjection C).map star)
              (EuclideanSpace.single i 1))‖ := hPle
      _ ≤ 2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single i 1)‖ := hDle
  have hsq : AndersonAC.S6.sqRow D i =
      ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2 :=
    sqRow_eq_clm_norm D hs i
  rw [hsq]
  have hsq2 : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2 ≤
      (2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single i 1)‖) ^ 2 := by
    have hnn : 0 ≤ ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ := norm_nonneg _
    have hle := mul_self_le_mul_self hnn hDnorm_le
    simpa [pow_two] using hle
  calc ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        (EuclideanSpace.single i 1)‖ ^ 2
      ≤ (2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1)‖) ^ 2 := hsq2
    _ = 4 * (‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single i 1)‖ ^ 2) := by ring
    _ = 4 * AndersonAC.S6.projectionWeight C i := by rw [hQnorm]

theorem proj_clm_norm_sq (C : Matrix R B ℂ) (i : R) :
    ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C)
      (EuclideanSpace.single i 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C i := by
  have hP : (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C) =
      (AndersonAC.S6.matrixRange C).starProjection :=
    proj_clm_eq C
  rw [hP]
  exact (AndersonAC.SolS6.projection_weight_eq C i).symm

theorem single_inner_eq' (v : EuclideanSpace ℂ R) (i : R) :
    inner ℂ (EuclideanSpace.single i (1 : ℂ)) v = v i := by
  rw [EuclideanSpace.inner_single_left]
  simp

theorem pointwise_bound_aux (C : Matrix R B ℂ)
    (D : Matrix R R ℂ)
    (hDnorm : ‖D‖ ≤ 2)
    (hleft : AndersonAC.S6.rangeProjection C * D = D)
    (hs : D.IsSymm) (i j : R) :
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
  have hCLM : (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D =
      (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        (AndersonAC.S6.rangeProjection C) *
      (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D *
      (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star) := by
    calc (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        = (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C * D *
            (AndersonAC.S6.rangeProjection C).map star) := by rw [← hFactor]
      _ = _ := by rw [map_mul, map_mul]
  have hPclm : (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
      (AndersonAC.S6.rangeProjection C) =
      (AndersonAC.S6.matrixRange C).starProjection :=
    proj_clm_eq C
  have hDij : D i j =
      inner ℂ ((AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1))
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))) := by
    have h1 : D i j =
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          (EuclideanSpace.single j 1)) i :=
      (clm_apply_entry D i j).symm
    have hApp : (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          (EuclideanSpace.single j 1) =
        (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          (AndersonAC.S6.rangeProjection C)
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
            ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
              ((AndersonAC.S6.rangeProjection C).map star)
              (EuclideanSpace.single j 1))) := by
      conv_lhs => rw [hCLM]
      simp [ContinuousLinearMap.mul_def]
    rw [h1, hApp, hPclm]
    have h3 : (((AndersonAC.S6.matrixRange C).starProjection
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)))) i) =
        inner ℂ (EuclideanSpace.single i 1)
          ((AndersonAC.S6.matrixRange C).starProjection
            ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
              ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
                ((AndersonAC.S6.rangeProjection C).map star)
                (EuclideanSpace.single j 1)))) :=
      (single_inner_eq' _ i).symm
    rw [h3]
    exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm
  have hPi_norm_i : ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C i :=
    (AndersonAC.SolS6.projection_weight_eq C i).symm
  have hQnorm : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ ^ 2 =
      AndersonAC.S6.projectionWeight C j :=
    conj_col_norm_sq C j
  have hwi : 0 ≤ AndersonAC.S6.projectionWeight C i :=
    (AndersonAC.S6.projection_coordinate C i).1
  have hcs : ‖D i j‖ ≤
      ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ *
      ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1))‖ := by
    rw [hDij]
    exact norm_inner_le_norm _ _
  have hy_le : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1))‖ ≤
      2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ := by
    have hle : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))‖ ≤
        ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D‖ *
          ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have heq : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D‖ = ‖D‖ :=
      Matrix.l2_opNorm_toEuclideanCLM D
    rw [heq] at hle
    calc ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))‖
        ≤ ‖D‖ * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)‖ := hle
      _ ≤ 2 * ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1)‖ :=
        mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
  have hPi_eq : ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ =
      Real.sqrt (AndersonAC.S6.projectionWeight C i) := by
    have hnn : 0 ≤ ‖(AndersonAC.S6.matrixRange C).starProjection
        (EuclideanSpace.single i 1)‖ := norm_nonneg _
    rw [← hPi_norm_i, Real.sqrt_sq hnn]
  have hQ_eq : ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ =
      Real.sqrt (AndersonAC.S6.projectionWeight C j) := by
    have hnn : 0 ≤ ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
        ((AndersonAC.S6.rangeProjection C).map star)
        (EuclideanSpace.single j 1)‖ := norm_nonneg _
    rw [← hQnorm, Real.sqrt_sq hnn]
  calc ‖D i j‖ ≤ ‖(AndersonAC.S6.matrixRange C).starProjection
          (EuclideanSpace.single i 1)‖ *
        ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) D
          ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
            ((AndersonAC.S6.rangeProjection C).map star)
            (EuclideanSpace.single j 1))‖ := hcs
    _ ≤ Real.sqrt (AndersonAC.S6.projectionWeight C i) * (2 *
        ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1)‖) := by
      rw [← hPi_eq]
      apply mul_le_mul_of_nonneg_left hy_le (norm_nonneg _)
    _ = 2 * (Real.sqrt (AndersonAC.S6.projectionWeight C i) *
        ‖(Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ))
          ((AndersonAC.S6.rangeProjection C).map star)
          (EuclideanSpace.single j 1)‖) := by ring
    _ = 2 * (Real.sqrt (AndersonAC.S6.projectionWeight C i) *
        Real.sqrt (AndersonAC.S6.projectionWeight C j)) := by rw [hQ_eq]
    _ = 2 * Real.sqrt (AndersonAC.S6.projectionWeight C i *
        AndersonAC.S6.projectionWeight C j) := by
      rw [← Real.sqrt_mul hwi]

end AndersonAC.SolS6.Supported

namespace AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem supported_change_bounds (C : Matrix R B ℂ) (D : Matrix R R ℂ)
    (hD : ‖D‖ ≤ 2) (hleft : rangeProjection C * D = D) (hs : D.IsSymm) :
    Planned.supported_change_bounds C D hD hleft hs := by
  refine ⟨AndersonAC.S6Change.supported_factor C D hleft hs,
    AndersonAC.SolS6.Supported.pointwise_bound_aux C D hD hleft hs,
    AndersonAC.SolS6.Supported.row_bound_aux C D hD hleft hs, ?_⟩
  have hsum := AndersonAC.SolS6.Supported.sum_weights_eq_finrank C
  have hfr := AndersonAC.SolS6.Supported.finrank_range_le_b C
  have hle : (Module.finrank ℂ (matrixRange C) : ℝ) ≤ (Fintype.card B : ℝ) :=
    Nat.cast_le.mpr hfr
  calc hsSq D = ∑ i, sqRow D i := rfl
    _ ≤ ∑ i, 4 * projectionWeight C i :=
      Finset.sum_le_sum fun i _ => AndersonAC.SolS6.Supported.row_bound_aux C D hD hleft hs i
    _ = 4 * (Module.finrank ℂ (matrixRange C) : ℝ) := by rw [← Finset.mul_sum, hsum]
    _ ≤ 4 * (Fintype.card B : ℝ) := mul_le_mul_of_nonneg_left hle (by norm_num)

end AndersonAC.S6
#print axioms AndersonAC.S6.supported_change_bounds
