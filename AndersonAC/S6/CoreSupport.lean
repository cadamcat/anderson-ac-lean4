import AndersonAC.S6.CoreSchur
import AndersonAC.S6.Supported
import AndersonAC.S6Core.CoreResolvent

/-! The supported contraction behind Lemma 6.1. -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
open AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem matrix_one_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
  exact ContinuousLinearMap.norm_id_le

theorem coisometry_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℂ) (hS : S * Sᴴ = 1) : ‖S‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Sᴴ
  rw [Matrix.conjTranspose_conjTranspose, hS, Matrix.l2_opNorm_conjTranspose] at h
  have h1 := matrix_one_norm_le (ι := ι)
  nlinarith [norm_nonneg S]

theorem survivor_norm_le (S : Matrix (B ⊕ R) (B ⊕ R) ℂ) :
    ‖survivorBlock S‖ ≤ ‖S‖ := by
  let J : Matrix (B ⊕ R) R ℂ := Matrix.fromRows 0 1
  have hJ : Jᴴ * J = 1 := by
    simp [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hJnorm : ‖J‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self J
    rw [hJ] at h
    have h1 := matrix_one_norm_le (ι := R)
    nlinarith [norm_nonneg J]
  have hblocks : S = Matrix.fromBlocks (S.submatrix Sum.inl Sum.inl)
      (S.submatrix Sum.inl Sum.inr) (S.submatrix Sum.inr Sum.inl)
      (S.submatrix Sum.inr Sum.inr) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hcompress : Jᴴ * S * J = survivorBlock S := by
    rw [hblocks]
    simp only [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows,
      Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, zero_add, survivorBlock]
    rfl
  rw [← hcompress]
  calc ‖Jᴴ * S * J‖ ≤ ‖Jᴴ * S‖ * ‖J‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Jᴴ‖ * ‖S‖) * ‖J‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖S‖) * 1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖S‖ := by ring

theorem projection_mul_source (C : Matrix R B ℂ) : rangeProjection C * C = C := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLpLin_mul]
  change Matrix.toEuclideanLin (rangeProjection C) (Matrix.toEuclideanLin C x) = _
  rw [projection_apply]
  apply Submodule.starProjection_eq_self_iff.mpr
  exact ⟨x, rfl⟩

theorem scattering_cross_block (t : ℝ) (r : (B ⊕ R) → ℂ)
    (g : Matrix (B ⊕ R) (B ⊕ R) ℂ) :
    crossBlock (scattering t r g) = (2 * Complex.I * (t : ℂ)) •
      (sqrtDamping (imagDamping (r ∘ Sum.inr)) * crossBlock g *
        sqrtDamping (imagDamping (r ∘ Sum.inl))) := by
  ext i j
  simp [crossBlock, scattering, scatteringOfDamping, sqrtDamping, imagDamping,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.one_apply]

theorem completed_scattering_support (M N : Matrix (B ⊕ R) (B ⊕ R) ℝ)
    (t c K : ℝ) (r : (B ⊕ R) → ℂ) (ht : 0 < t) (hb : BroadBounds c K r)
    (hM : M.IsSymm) (hN : N.IsSymm) (hchange : CoreDiagonalChange M N)
    (hterminal : IsUnit (trueCoreMatrix N).det) :
    let C := crossBlock (scattering t r (activeInverse M t r))
    let ds := scattering t (r ∘ Sum.inr) (completedInverse N t r) -
      survivorBlock (scattering t r (activeInverse M t r))
    IsUnit (dampedMatrix (realSurvivor N) t (r ∘ Sum.inr)).det ∧
      ‖ds‖ ≤ 2 ∧ rangeProjection C * ds = ds ∧ ds.IsSymm := by
  let g := activeInverse M t r
  let pB := imagDamping (r ∘ Sum.inl)
  let pR := imagDamping (r ∘ Sum.inr)
  let P := sqrtDamping pB
  let Q := sqrtDamping pR
  let V : Matrix B B ℂ := Matrix.diagonal (fun b =>
    ((N (Sum.inl b) (Sum.inl b) - M (Sum.inl b) (Sum.inl b) : ℝ) : ℂ) +
      (t : ℂ) * r (Sum.inl b))
  have hp : ∀ i, 0 < (r i).im := fun i => hb.1.trans_le (hb.2 i).2.1
  have hold := damped_det_unit M hM t ht r hp
  letI : Invertible (dampedMatrix M t r) :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr hold).invertible
  have hnew := damped_det_unit (realSurvivor N) (realSurvivor_symmetric N hN)
    t ht (r ∘ Sum.inr) (fun i => hp (Sum.inr i))
  have hambient := completed_schur_unit_and_inverse N hN t ht r
    (fun i => hp (Sum.inr i)) hterminal
  have hpert : g⁻¹ + Matrix.fromBlocks V 0 0 0 = completedAmbient N t r := by
    dsimp [g, activeInverse]
    rw [Matrix.inv_inv_of_invertible]
    exact (completed_core_perturbation M N t r hchange).symm
  have hg : IsUnit g.det := by
    dsimp [g, activeInverse]
    exact Matrix.isUnit_nonsing_inv_det _ hold
  have hV : IsUnit V.det := by
    apply (Matrix.isUnit_iff_isUnit_det V).mp
    apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro b
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have him : 0 < (((N (Sum.inl b) (Sum.inl b) - M (Sum.inl b) (Sum.inl b) : ℝ) : ℂ) +
      (t : ℂ) * r (Sum.inl b)).im := by
      simpa [Complex.mul_im] using mul_pos ht (hp (Sum.inl b))
    rw [hz] at him
    simpa using him
  have hres := coreResolvent_proof B R g V hg hV (hpert.symm ▸ hambient.1)
  have hdelta : completionDelta M N t r =
      -(crossBlock g * (1 + V * coreBlock g)⁻¹ * V * g.submatrix Sum.inl Sum.inr) := by
    rw [hpert, hambient.2] at hres
    exact hres.2
  have hPunit : IsUnit P.det := by
    apply (Matrix.isUnit_iff_isUnit_det P).mp
    apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro b
    apply isUnit_iff_ne_zero.mpr
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp (Sum.inl b))).ne'
  let X : Matrix B R ℂ := -(P⁻¹ * (1 + V * coreBlock g)⁻¹ * V *
    g.submatrix Sum.inl Sum.inr * Q)
  have hfactor : scattering t (r ∘ Sum.inr) (completedInverse N t r) -
      survivorBlock (scattering t r g) = crossBlock (scattering t r g) * X := by
    rw [scattering_survivor_block, scattering_difference, scattering_cross_block]
    change (2 * Complex.I * (t : ℂ)) • (Q * completionDelta M N t r * Q) = _
    rw [hdelta]
    simp only [X, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P⁻¹, Matrix.mul_nonsing_inv P hPunit, Matrix.one_mul]
    simp only [smul_neg, Q, pR]
  have hleft : rangeProjection (crossBlock (scattering t r g)) *
      (scattering t (r ∘ Sum.inr) (completedInverse N t r) -
        survivorBlock (scattering t r g)) =
      scattering t (r ∘ Sum.inr) (completedInverse N t r) -
        survivorBlock (scattering t r g) := by
    rw [hfactor, ← Matrix.mul_assoc, projection_mul_source]
  have hsold := scattering_from_inverse (M.map Complex.ofReal) g t r (hM.map Complex.ofReal)
    (by intro i j; exact Complex.ofReal_im _) (fun i => (hp i).le)
    ⟨Matrix.mul_nonsing_inv _ hold, Matrix.nonsing_inv_mul _ hold⟩
  have hsnew := scattering_from_inverse ((realSurvivor N).map Complex.ofReal)
    (completedInverse N t r) t (r ∘ Sum.inr) ((realSurvivor_symmetric N hN).map Complex.ofReal)
    (by intro i j; exact Complex.ofReal_im _) (fun i => (hp (Sum.inr i)).le)
    ⟨Matrix.mul_nonsing_inv _ hnew, Matrix.nonsing_inv_mul _ hnew⟩
  refine ⟨hnew, ?_, hleft, ?_⟩
  · calc ‖scattering t (r ∘ Sum.inr) (completedInverse N t r) -
          survivorBlock (scattering t r g)‖ ≤
        ‖scattering t (r ∘ Sum.inr) (completedInverse N t r)‖ +
          ‖survivorBlock (scattering t r g)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (coisometry_norm_le _ hsnew.2)
        ((survivor_norm_le _).trans (coisometry_norm_le _ hsold.2))
      _ = 2 := by norm_num
  · apply hsnew.1.sub
    apply Matrix.IsSymm.ext
    intro i j
    exact hsold.1.apply (Sum.inr i) (Sum.inr j)

end AndersonAC.SolS6
#print axioms AndersonAC.SolS6.completed_scattering_support
