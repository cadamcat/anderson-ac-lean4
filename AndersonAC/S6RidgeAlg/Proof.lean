import AndersonAC.S6.Definitions
import AndersonAC.S6.Projection
import AndersonAC.S6Change.SupportedChange

/-! Ridge algebra for the section integration. This file does not import the
planning statements module. -/

noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
  MatrixOrder ComplexOrder

namespace AndersonAC.SolS6

variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

private lemma ridge_scalar_one_posDef (ι : Type*) [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (hτ : 0 < τ) :
    ((τ : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
  rw [Matrix.smul_one_eq_diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast hτ

private lemma ridgeGram_posDef (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) :
    (AndersonAC.S6.ridgeGram C τ).PosDef := by
  unfold AndersonAC.S6.ridgeGram AndersonAC.S6.gram
  exact Matrix.PosDef.posSemidef_add
    (Matrix.posSemidef_conjTranspose_mul_self C)
    (ridge_scalar_one_posDef B τ hτ)

private lemma ridgeGram_det_unit (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) :
    IsUnit (AndersonAC.S6.ridgeGram C τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (ridgeGram_posDef C τ hτ).isUnit

private lemma ridgeInvSqrt_hermitian (C : Matrix R B ℂ) (τ : ℝ) :
    (AndersonAC.S6.ridgeInvSqrt C τ).IsHermitian := by
  unfold AndersonAC.S6.ridgeInvSqrt
  exact (cfc_predicate (fun x : ℝ => (Real.sqrt x)⁻¹)
    (AndersonAC.S6.ridgeGram C τ)).isHermitian

private lemma ridgeInvSqrt_sq (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) :
    AndersonAC.S6.ridgeInvSqrt C τ * AndersonAC.S6.ridgeInvSqrt C τ =
      (AndersonAC.S6.ridgeGram C τ)⁻¹ := by
  let G := AndersonAC.S6.ridgeGram C τ
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  have hGpos : G.PosDef := ridgeGram_posDef C τ hτ
  have hGunit : IsUnit G := hGpos.isUnit
  have hGself : IsSelfAdjoint G := hGpos.isHermitian.isSelfAdjoint
  have hfcont : ContinuousOn f (spectrum ℝ G) :=
    G.finite_real_spectrum.continuousOn f
  have hinvcont : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ G) :=
    G.finite_real_spectrum.continuousOn _
  have hidcont : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ G) :=
    G.finite_real_spectrum.continuousOn _
  have hspectrum : ∀ x ∈ spectrum ℝ G, x ≠ 0 := by
    intro x hx
    obtain ⟨i, rfl⟩ := hGpos.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact ne_of_gt (hGpos.eigenvalues_pos i)
  have hfun : (spectrum ℝ G).EqOn (fun x => f x * f x) (fun x => x⁻¹) := by
    intro x hx
    have hxpos : 0 < x := by
      obtain ⟨i, rfl⟩ := hGpos.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
      exact hGpos.eigenvalues_pos i
    have hroot : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hxpos)
    dsimp [f]
    field_simp [hroot]
    rw [Real.sq_sqrt hxpos.le]
  calc
    AndersonAC.S6.ridgeInvSqrt C τ * AndersonAC.S6.ridgeInvSqrt C τ =
        cfc (fun x : ℝ => f x * f x) G := by
          unfold AndersonAC.S6.ridgeInvSqrt
          change cfc f G * cfc f G = cfc (fun x : ℝ => f x * f x) G
          exact (cfc_mul f f G hfcont hfcont).symm
    _ = cfc (fun x : ℝ => x⁻¹) G := cfc_congr hfun
    _ = Ring.inverse (cfc (id : ℝ → ℝ) G) := by
          simpa only [id_eq] using
            (cfc_inv (f := id) (a := G) (hf' := hspectrum)
              (hf := hidcont) (ha := hGself))
    _ = Ring.inverse G := by rw [cfc_id ℝ G hGself]
    _ = G⁻¹ := by rw [← Matrix.nonsing_inv_eq_ringInverse]

private lemma ridgeGram_posSemidef (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) :
    (AndersonAC.S6.ridgeGram C τ).PosSemidef :=
  (ridgeGram_posDef C τ hτ).posSemidef

private lemma ridge_projection_factorization (C : Matrix R B ℂ) (τ : ℝ)
    (hτ : 0 < τ) :
    AndersonAC.S6.ridgeProjection C τ =
      AndersonAC.S6.ridgeRows C τ * (AndersonAC.S6.ridgeRows C τ)ᴴ := by
  let G := AndersonAC.S6.ridgeGram C τ
  let S := AndersonAC.S6.ridgeInvSqrt C τ
  have hS : Sᴴ = S := (ridgeInvSqrt_hermitian C τ).eq
  have hSq : S * S = G⁻¹ := ridgeInvSqrt_sq C τ hτ
  unfold AndersonAC.S6.ridgeProjection AndersonAC.S6.ridgeRows
  calc
    C * G⁻¹ * Cᴴ = C * (S * S) * Cᴴ := by rw [hSq]
    _ = (C * S) * (S * Cᴴ) := by simp only [Matrix.mul_assoc]
    _ = (C * S) * (C * S)ᴴ := by rw [Matrix.conjTranspose_mul, hS]

private lemma ridge_defect_eq (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) :
    AndersonAC.S6.ridgeDefect C τ =
      (τ : ℂ) • (AndersonAC.S6.ridgeGram C τ)⁻¹ := by
  let G := AndersonAC.S6.ridgeGram C τ
  let S := AndersonAC.S6.ridgeInvSqrt C τ
  have hS : Sᴴ = S := (ridgeInvSqrt_hermitian C τ).eq
  have hSq : S * S = G⁻¹ := ridgeInvSqrt_sq C τ hτ
  have hcomm : Commute S G := by
    change Commute (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G) G
    exact (Commute.refl G).cfc_real (fun x : ℝ => (Real.sqrt x)⁻¹)
  have hdet : IsUnit G.det := ridgeGram_det_unit C τ hτ
  have hSGS : S * G * S = 1 := by
    calc
      S * G * S = (G * S) * S := by rw [hcomm.eq]
      _ = G * (S * S) := by rw [Matrix.mul_assoc]
      _ = G * G⁻¹ := by rw [hSq]
      _ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hExp : S * (G - (τ : ℂ) • (1 : Matrix B B ℂ)) * S =
      1 - (τ : ℂ) • G⁻¹ := by
    calc
      S * (G - (τ : ℂ) • (1 : Matrix B B ℂ)) * S =
          S * G * S - (S * ((τ : ℂ) • (1 : Matrix B B ℂ))) * S := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = S * G * S - (τ : ℂ) • (S * S) := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = 1 - (τ : ℂ) • G⁻¹ := by rw [hSGS, hSq]
  have hgram : AndersonAC.S6.gram C = G - (τ : ℂ) • (1 : Matrix B B ℂ) := by
    dsimp [G, AndersonAC.S6.ridgeGram]
    unfold AndersonAC.S6.gram
    abel
  change 1 - (C * S)ᴴ * (C * S) = (τ : ℂ) • G⁻¹
  calc
    1 - (C * S)ᴴ * (C * S) = 1 - (S * Cᴴ) * (C * S) := by
      rw [Matrix.conjTranspose_mul, hS]
    _ = 1 - S * (Cᴴ * C) * S := by simp only [Matrix.mul_assoc]
    _ = 1 - S * (G - (τ : ℂ) • (1 : Matrix B B ℂ)) * S := by
      rw [← hgram]
      rfl
    _ = (τ : ℂ) • G⁻¹ := by rw [hExp]; simp

private lemma ridge_projection_eq_one_sub_inv (C : Matrix R B ℂ) (τ : ℝ)
    (hτ : 0 < τ) :
    AndersonAC.S6.ridgeProjection C τ =
      1 - (τ : ℂ) • (C * Cᴴ + (τ : ℂ) • (1 : Matrix R R ℂ))⁻¹ := by
  let G := AndersonAC.S6.ridgeGram C τ
  let K := C * Cᴴ + (τ : ℂ) • (1 : Matrix R R ℂ)
  have hGdet : IsUnit G.det := ridgeGram_det_unit C τ hτ
  have hKpos : K.PosDef := by
    dsimp [K]
    exact Matrix.PosDef.posSemidef_add
      (Matrix.posSemidef_self_mul_conjTranspose C)
      (ridge_scalar_one_posDef R τ hτ)
  have hKdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det _).mp hKpos.isUnit
  have hintertwine : C * G = K * C := by
    dsimp [G, K]
    unfold AndersonAC.S6.ridgeGram AndersonAC.S6.gram
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    ext i j
    simp [smul_eq_mul]
  have hleft : K⁻¹ * (C * G) = C := by
    calc
      K⁻¹ * (C * G) = K⁻¹ * (K * C) := by rw [hintertwine]
      _ = (K⁻¹ * K) * C := by rw [Matrix.mul_assoc]
      _ = C := by rw [Matrix.nonsing_inv_mul _ hKdet, Matrix.one_mul]
  have hpush : K⁻¹ * C = C * G⁻¹ := by
    have hmul : (K⁻¹ * C) * G = C := by
      calc
        (K⁻¹ * C) * G = K⁻¹ * (C * G) := by rw [Matrix.mul_assoc]
        _ = C := hleft
    calc
      K⁻¹ * C = ((K⁻¹ * C) * G) * G⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGdet, Matrix.mul_one]
      _ = C * G⁻¹ := by rw [hmul]
  have hgram : C * Cᴴ = K - (τ : ℂ) • (1 : Matrix R R ℂ) := by
    dsimp [K]
    abel
  calc
    AndersonAC.S6.ridgeProjection C τ = C * G⁻¹ * Cᴴ := by
      rfl
    _ = (K⁻¹ * C) * Cᴴ := by rw [← hpush]
    _ = K⁻¹ * (C * Cᴴ) := by rw [Matrix.mul_assoc]
    _ = K⁻¹ * (K - (τ : ℂ) • (1 : Matrix R R ℂ)) := by rw [hgram]
    _ = 1 - (τ : ℂ) • K⁻¹ := by
      rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hKdet]
      simp [Matrix.mul_smul, Matrix.mul_one]

private lemma one_sub_ridgeProjection_posSemidef (C : Matrix R B ℂ) (τ : ℝ)
    (hτ : 0 < τ) : (1 - AndersonAC.S6.ridgeProjection C τ).PosSemidef := by
  rw [ridge_projection_eq_one_sub_inv C τ hτ]
  have hK : (C * Cᴴ + (τ : ℂ) • (1 : Matrix R R ℂ)).PosDef := by
    apply Matrix.PosDef.posSemidef_add
    · exact Matrix.posSemidef_self_mul_conjTranspose C
    · exact ridge_scalar_one_posDef R τ hτ
  have hτc : (0 : ℂ) ≤ (τ : ℂ) := by exact_mod_cast hτ.le
  simpa using hK.posSemidef.inv.smul hτc

private lemma rangeProjection_mul_C_aux (C : Matrix R B ℂ) :
    AndersonAC.S6.rangeProjection C * C = C := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same]
  apply LinearMap.ext
  intro v
  have hv : (Matrix.toEuclideanLin C) v ∈ AndersonAC.S6.matrixRange C := by
    exact ⟨v, rfl⟩
  exact (AndersonAC.SolS6.projection_apply C _).trans
    ((AndersonAC.S6.matrixRange C).starProjection_eq_self_iff.mpr hv)

private lemma ridgeProjection_le_rangeProjection (C : Matrix R B ℂ) (τ : ℝ)
    (hτ : 0 < τ) :
    (AndersonAC.S6.rangeProjection C - AndersonAC.S6.ridgeProjection C τ).PosSemidef := by
  let P := AndersonAC.S6.rangeProjection C
  let A := AndersonAC.S6.ridgeProjection C τ
  have hPid : P * P = P := AndersonAC.S6Change.rangeProj_idem C
  have hPh : P.IsHermitian := AndersonAC.S6Change.rangeProj_herm C
  have hAfactor := ridge_projection_factorization C τ hτ
  have hAh : A.IsHermitian := by
    change (AndersonAC.S6.ridgeProjection C τ).IsHermitian
    rw [hAfactor]
    exact Matrix.isHermitian_mul_conjTranspose_self _
  have hPA : P * A = A := by
    change P * (C * (AndersonAC.S6.ridgeGram C τ)⁻¹ * Cᴴ) =
      C * (AndersonAC.S6.ridgeGram C τ)⁻¹ * Cᴴ
    calc
      P * (C * (AndersonAC.S6.ridgeGram C τ)⁻¹ * Cᴴ) =
          (P * C) * (AndersonAC.S6.ridgeGram C τ)⁻¹ * Cᴴ := by
            simp only [Matrix.mul_assoc]
      _ = C * (AndersonAC.S6.ridgeGram C τ)⁻¹ * Cᴴ := by
            rw [rangeProjection_mul_C_aux]
  have hAP : A * P = A := by
    simpa [Matrix.conjTranspose_mul, hAh.eq, hPh.eq] using
      congrArg Matrix.conjTranspose hPA
  have hPAP : P * A * P = A := by
    calc
      P * A * P = (P * A) * P := rfl
      _ = A * P := by rw [hPA]
      _ = A := hAP
  have hFactor : P - A = P * (1 - A) * Pᴴ := by
    rw [hPh.eq]
    calc
      P - A = P * P - (P * A) * P := by rw [hPid, hPAP]
      _ = P * (1 - A) * P := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  rw [hFactor]
  exact (one_sub_ridgeProjection_posSemidef C τ hτ).mul_mul_conjTranspose_same P

private lemma ridge_leverage_bounds (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ)
    (i : R) :
    0 ≤ AndersonAC.S6.leverage C τ i ∧
      AndersonAC.S6.leverage C τ i ≤ AndersonAC.S6.projectionWeight C i := by
  have hA := Matrix.posSemidef_self_mul_conjTranspose (AndersonAC.S6.ridgeRows C τ)
  have hP := ridgeProjection_le_rangeProjection C τ hτ
  have hAeq := ridge_projection_factorization C τ hτ
  have hdiagA : 0 ≤ (AndersonAC.S6.ridgeProjection C τ i i).re := by
    have h := hA.diag_nonneg (i := i)
    simpa [hAeq] using (Complex.nonneg_iff.mp h).1
  have hdiagD : 0 ≤ (AndersonAC.S6.rangeProjection C i i).re -
      (AndersonAC.S6.ridgeProjection C τ i i).re := by
    have h := hP.diag_nonneg (i := i)
    have hr := (Complex.nonneg_iff.mp h).1
    simpa [Matrix.sub_apply, Complex.sub_re] using hr
  constructor
  · simpa [AndersonAC.S6.leverage] using hdiagA
  · exact sub_nonneg.mp (by simpa [AndersonAC.S6.projectionWeight,
      AndersonAC.S6.leverage] using hdiagD)

private lemma ridge_totalWeight_trace (C : Matrix R B ℂ) (τ : ℝ)
    (hτ : 0 < τ) :
    AndersonAC.S6.totalWeight (AndersonAC.S6.leverage C τ) =
      (((AndersonAC.S6.ridgeRows C τ)ᴴ * AndersonAC.S6.ridgeRows C τ).trace).re := by
  calc
    AndersonAC.S6.totalWeight (AndersonAC.S6.leverage C τ) =
        (AndersonAC.S6.ridgeProjection C τ).trace.re := by
          simp [AndersonAC.S6.totalWeight, AndersonAC.S6.leverage, Matrix.trace]
    _ = (((AndersonAC.S6.ridgeRows C τ)ᴴ * AndersonAC.S6.ridgeRows C τ).trace).re := by
          rw [ridge_projection_factorization C τ hτ, Matrix.trace_mul_comm]

private lemma rangeProjection_mul_C (C : Matrix R B ℂ) :
    AndersonAC.S6.rangeProjection C * C = C := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same]
  apply LinearMap.ext
  intro v
  have hv : (Matrix.toEuclideanLin C) v ∈ AndersonAC.S6.matrixRange C := by
    exact ⟨v, rfl⟩
  exact (AndersonAC.SolS6.projection_apply C _).trans
    ((AndersonAC.S6.matrixRange C).starProjection_eq_self_iff.mpr hv)

private lemma sum_projectionWeight_eq_finrank (C : Matrix R B ℂ) :
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
          (EuclideanSpace.single i 1) : AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ R) := rfl
    calc
      AndersonAC.S6.projectionWeight C i =
          ‖(AndersonAC.S6.matrixRange C).starProjection
            (EuclideanSpace.single i 1)‖ ^ 2 := h1
      _ = ‖(((AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1) : AndersonAC.S6.matrixRange C) :
          EuclideanSpace ℂ R)‖ ^ 2 := by rw [h2]
      _ = ‖(AndersonAC.S6.matrixRange C).orthogonalProjectionOnto
          (EuclideanSpace.single i 1)‖ ^ 2 := rfl
  have hsum : ∀ i : R, AndersonAC.S6.projectionWeight C i =
      ∑ k : Fin (Module.finrank ℂ (AndersonAC.S6.matrixRange C)),
        ‖inner ℂ
          (((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
            AndersonAC.S6.matrixRange C) : EuclideanSpace ℂ R))
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
          AndersonAC.S6.matrixRange C) : EuclideanSpace ℂ R))
        (EuclideanSpace.single i 1)‖ ^ 2 = 1 := by
    intro k
    set u : EuclideanSpace ℂ R :=
      ((stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
        AndersonAC.S6.matrixRange C) : EuclideanSpace ℂ R) with hu
    have hu_norm : ‖u‖ = 1 := by
      have h1 : ‖(stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
          AndersonAC.S6.matrixRange C)‖ = 1 :=
        Orthonormal.norm_eq_one
          (stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C)).orthonormal k
      calc
        ‖u‖ = ‖(stdOrthonormalBasis ℂ (AndersonAC.S6.matrixRange C) k :
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

private lemma matrixRange_finrank_eq_rank (C : Matrix R B ℂ) :
    Module.finrank ℂ (AndersonAC.S6.matrixRange C) = Matrix.rank C := by
  have h := Matrix.rank_eq_finrank_range_toLin C
    (EuclideanSpace.basisFun R ℂ).toBasis (EuclideanSpace.basisFun B ℂ).toBasis
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h
  exact h.symm

private lemma ridge_totalWeight_le_rank (C : Matrix R B ℂ) (τ : ℝ)
    (hτ : 0 < τ) :
    AndersonAC.S6.totalWeight (AndersonAC.S6.leverage C τ) ≤ (Matrix.rank C : ℝ) := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (ridge_leverage_bounds C τ hτ i).2)
  calc
    AndersonAC.S6.totalWeight (AndersonAC.S6.leverage C τ) ≤
        ∑ i, AndersonAC.S6.projectionWeight C i := by
          simpa [AndersonAC.S6.totalWeight] using hsum
    _ = Module.finrank ℂ (AndersonAC.S6.matrixRange C) := by
          exact_mod_cast (sum_projectionWeight_eq_finrank C)
    _ = (Matrix.rank C : ℝ) := by exact_mod_cast matrixRange_finrank_eq_rank C

theorem ridgeAlgebra_proof :
    ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
      (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ),
    AndersonAC.S6.ridgeProjection C τ =
        AndersonAC.S6.ridgeRows C τ * (AndersonAC.S6.ridgeRows C τ)ᴴ ∧
      AndersonAC.S6.ridgeDefect C τ =
        (τ : ℂ) • (AndersonAC.S6.ridgeGram C τ)⁻¹ ∧
      (AndersonAC.S6.ridgeDefect C τ).PosSemidef ∧
      (1 - AndersonAC.S6.ridgeDefect C τ).PosSemidef ∧
      (∀ i, 0 ≤ AndersonAC.S6.leverage C τ i ∧
        AndersonAC.S6.leverage C τ i ≤ AndersonAC.S6.projectionWeight C i) ∧
      AndersonAC.S6.totalWeight (AndersonAC.S6.leverage C τ) =
        (((AndersonAC.S6.ridgeRows C τ)ᴴ * AndersonAC.S6.ridgeRows C τ).trace).re ∧
      AndersonAC.S6.totalWeight (AndersonAC.S6.leverage C τ) ≤ (Matrix.rank C : ℝ) ∧
      Matrix.rank C ≤ Fintype.card B := by
  intro B R _ _ _ _ C τ hτ
  have hfactor := ridge_projection_factorization C τ hτ
  have hdefect := ridge_defect_eq C τ hτ
  have hdefect_psd : (AndersonAC.S6.ridgeDefect C τ).PosSemidef := by
    rw [hdefect]
    have hτc : (0 : ℂ) ≤ (τ : ℂ) := by exact_mod_cast hτ.le
    exact (ridgeGram_posDef C τ hτ).posSemidef.inv.smul hτc
  have hone_sub_defect : (1 - AndersonAC.S6.ridgeDefect C τ).PosSemidef := by
    simpa [AndersonAC.S6.ridgeDefect] using
      (Matrix.posSemidef_conjTranspose_mul_self (AndersonAC.S6.ridgeRows C τ))
  refine ⟨hfactor, hdefect, hdefect_psd, hone_sub_defect, ?_,
    ridge_totalWeight_trace C τ hτ, ridge_totalWeight_le_rank C τ hτ,
    Matrix.rank_le_card_width C⟩
  intro i
  exact ridge_leverage_bounds C τ hτ i

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.ridgeAlgebra_proof
