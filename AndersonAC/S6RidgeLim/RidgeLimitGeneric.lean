import AndersonAC.S6.Definitions
import AndersonAC.S6.Projection

/-! Ridge-limit helper: ridge projection tends to the range projection as τ → 0⁺. -/

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator ComplexOrder
open Filter

namespace AndersonAC.SolS6RidgeLim

/-- Gram matrix is positive semidefinite. -/
private lemma gram_psd (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) :
    (AndersonAC.S6.gram C).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self C

/-- `K = C * Cᴴ` is positive semidefinite. -/
private lemma K_psd (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) :
    (C * Cᴴ).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose C

/-- Scalar-plus-identity is positive definite for positive `τ`. -/
private lemma smul_one_posDef (B : Type*) [Fintype B] [DecidableEq B]
    (τ : ℝ) (hτ : 0 < τ) :
    ((τ : ℂ) • (1 : Matrix B B ℂ)).PosDef := by
  rw [Matrix.smul_one_eq_diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  simpa using hτ

/-- Ridge Gram matrix is positive definite for `τ > 0`. -/
private lemma ridgeGram_posDef (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    (AndersonAC.S6.ridgeGram C τ).PosDef := by
  unfold AndersonAC.S6.ridgeGram
  exact Matrix.PosDef.posSemidef_add (gram_psd B R C) (smul_one_posDef B τ hτ)

/-- `K + τ • 1` is positive definite for `τ > 0`. -/
private lemma Ktau_posDef (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add (K_psd B R C) (smul_one_posDef R τ hτ)

private lemma ridgeGram_isUnit_det (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    IsUnit (AndersonAC.S6.ridgeGram C τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (ridgeGram_posDef B R C τ hτ).isUnit

private lemma Ktau_isUnit_det (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    IsUnit (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ)).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Ktau_posDef B R C τ hτ).isUnit

/-- `K = C * Cᴴ` is Hermitian. -/
private lemma K_isHermitian (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) :
    (C * Cᴴ).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self C

/-- Eigenvalues of `K` are nonnegative. -/
private lemma K_eig_nonneg (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) (k : R) :
    0 ≤ (K_isHermitian B R C).eigenvalues k :=
  (Matrix.posSemidef_self_mul_conjTranspose C).eigenvalues_nonneg k

/-- Spectral decomposition of `K`. -/
private lemma K_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) :
    C * Cᴴ = ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ (K_isHermitian B R C).eigenvalues) *
      star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) := by
  have h := (K_isHermitian B R C).spectral_theorem
  rwa [Unitary.conjStarAlgAut_apply] at h

/-- `Kτ` in the eigenbasis. -/
private lemma Ktau_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) (τ : ℝ) :
    C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ) =
      ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        (Matrix.diagonal (RCLike.ofReal ∘ (K_isHermitian B R C).eigenvalues) +
          (τ : ℂ) • 1) *
        star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) := by
  have hK := K_eq B R C
  set U : Matrix (R) (R) ℂ :=
    ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) with hU
  set S : Matrix (R) (R) ℂ := star U with hS
  set D : Matrix (R) (R) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ (K_isHermitian B R C).eigenvalues) with hD
  have hU1 : U * S = 1 := Unitary.coe_mul_star_self _
  have htau : (τ : ℂ) • (1 : Matrix (R) (R) ℂ) = U * ((τ : ℂ) • 1) * S := by
    calc (τ : ℂ) • (1 : Matrix (R) (R) ℂ)
        = (τ : ℂ) • (U * S) := by rw [hU1]
      _ = U * ((τ : ℂ) • 1) * S := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  calc C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ)
      = U * D * S + U * ((τ : ℂ) • 1) * S :=
        congrArg₂ _ hK htau
    _ = U * (D + (τ : ℂ) • 1) * S := by
        simp only [← Matrix.add_mul, ← Matrix.mul_add]

/-- Diagonal `Dτ` entries are nonzero for `τ > 0`. -/
private lemma Dtau_ne (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) (k : R) :
    RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ) ≠ 0 := by
  have hNonneg := K_eig_nonneg B R C k
  have hpos : 0 < (K_isHermitian B R C).eigenvalues k + τ := by linarith
  have heq : RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ)
      = RCLike.ofReal ((K_isHermitian B R C).eigenvalues k + τ) :=
    (RCLike.ofReal_add _ _).symm
  rw [heq]
  exact (RCLike.ofReal_eq_zero (K := ℂ)).not.mpr (ne_of_gt hpos)

/-- Inverse of `Kτ` in the eigenbasis for `τ > 0`. -/
private lemma Ktau_inv_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ =
      ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun k =>
          (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹) *
        star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) := by
  have hKτ := Ktau_eq B R C τ
  set U : Matrix (R) (R) ℂ :=
    ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) with hU
  set S : Matrix (R) (R) ℂ := star U with hS
  set Dτ : Matrix (R) (R) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ (K_isHermitian B R C).eigenvalues) +
      (τ : ℂ) • 1 with hDτ
  set Dinv : Matrix (R) (R) ℂ :=
    Matrix.diagonal (fun k =>
      (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹) with hDinv
  have hU1 : U * S = 1 := Unitary.coe_mul_star_self _
  have hU2 : S * U = 1 := Unitary.coe_star_mul_self _
  have hDτ_eq : Dτ = Matrix.diagonal (fun k =>
      RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ)) := by
    rw [hDτ, Matrix.smul_one_eq_diagonal, Matrix.diagonal_add]
    rfl
  have hDD : Dτ * Dinv = 1 := by
    rw [hDτ_eq, hDinv, Matrix.diagonal_mul_diagonal]
    have : (fun k : R =>
        (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ)) *
          (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹) =
        (fun _ => (1 : ℂ)) := by
      funext k
      exact mul_inv_cancel₀ (Dtau_ne B R C τ hτ k)
    rw [this, Matrix.diagonal_one]
  have hKτX : (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ)) *
      (U * Dinv * S) = 1 := by
    rw [hKτ]
    calc (U * Dτ * S) * (U * Dinv * S)
        = (U * Dτ) * (S * ((U * Dinv) * S)) := Matrix.mul_assoc _ _ _
      _ = (U * Dτ) * (((S * U) * Dinv) * S) := by
          rw [← Matrix.mul_assoc S (U * Dinv) S, ← Matrix.mul_assoc S U Dinv]
      _ = (U * Dτ) * (Dinv * S) := by rw [hU2, Matrix.one_mul]
      _ = U * (Dτ * (Dinv * S)) := Matrix.mul_assoc _ _ _
      _ = U * ((Dτ * Dinv) * S) := by rw [← Matrix.mul_assoc Dτ Dinv S]
      _ = U * S := by rw [hDD, Matrix.one_mul]
      _ = 1 := hU1
  have hdet := Ktau_isUnit_det B R C τ hτ
  calc (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹
      = (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * 1 := by
        rw [Matrix.mul_one]
    _ = (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ *
          ((C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ)) *
            (U * Dinv * S)) := by
        rw [hKτX]
    _ = ((C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ *
            (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))) *
          (U * Dinv * S) := by
        simp only [Matrix.mul_assoc]
    _ = U * Dinv * S := by
        rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-- Intertwining: `C * Gτ = Kτ * C`. -/
private lemma intertwine (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) (τ : ℝ) :
    C * AndersonAC.S6.ridgeGram C τ =
      (C * Cᴴ + (τ : ℂ) • 1) * C := by
  unfold AndersonAC.S6.ridgeGram AndersonAC.S6.gram
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- Push-through: `Kτ⁻¹ * C = C * Gτ⁻¹` for `τ > 0`. -/
private lemma pushthrough_aux (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * C =
      C * (AndersonAC.S6.ridgeGram C τ)⁻¹ := by
  have hG := ridgeGram_isUnit_det B R C τ hτ
  have hK := Ktau_isUnit_det B R C τ hτ
  have h_inter := intertwine B R C τ
  have h1 : (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ *
      (C * AndersonAC.S6.ridgeGram C τ) = C := by
    rw [h_inter, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hK, Matrix.one_mul]
  have h2 : ((C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * C) *
      AndersonAC.S6.ridgeGram C τ = C := by
    have : (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ *
        (C * AndersonAC.S6.ridgeGram C τ) =
        ((C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * C) *
          AndersonAC.S6.ridgeGram C τ :=
      (Matrix.mul_assoc _ _ _).symm
    rw [← this, h1]
  calc (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * C
      = (((C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * C) *
          AndersonAC.S6.ridgeGram C τ) *
          (AndersonAC.S6.ridgeGram C τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
    _ = C * (AndersonAC.S6.ridgeGram C τ)⁻¹ := by rw [h2]

/-- Ridge equals `1 - τ • Kτ⁻¹` for `τ > 0`. -/
private lemma ridge_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    AndersonAC.S6.ridgeProjection C τ =
      1 - (τ : ℂ) • (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ := by
  unfold AndersonAC.S6.ridgeProjection
  have hK := Ktau_isUnit_det B R C τ hτ
  have hpt := pushthrough_aux B R C τ hτ
  have hKK : (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ *
      (C * Cᴴ) =
      1 - (τ : ℂ) • (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ := by
    have hsub : (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ)) -
        (τ : ℂ) • (1 : Matrix (R) (R) ℂ) = C * Cᴴ := by
      abel
    have h : (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ *
        ((C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ)) -
          (τ : ℂ) • (1 : Matrix (R) (R) ℂ)) =
        1 - (τ : ℂ) • (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ := by
      rw [Matrix.mul_sub,
        Matrix.nonsing_inv_mul _ hK, Matrix.mul_smul, Matrix.mul_one]
    rwa [hsub] at h
  calc C * (AndersonAC.S6.ridgeGram C τ)⁻¹ * Cᴴ
      = ((C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * C) * Cᴴ := by
        rw [← hpt]
    _ = (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ * (C * Cᴴ) :=
        Matrix.mul_assoc _ _ _
    _ = 1 - (τ : ℂ) • (C * Cᴴ + (τ : ℂ) • (1 : Matrix (R) (R) ℂ))⁻¹ :=
        hKK

/-- Ridge in the eigenbasis for `τ > 0`: diagonal `λ/(λ+τ)`. -/
private lemma ridge_diag_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    AndersonAC.S6.ridgeProjection C τ =
      ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun k =>
          RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
            (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) *
        star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) := by
  have hR := ridge_eq B R C τ hτ
  have hKinv := Ktau_inv_eq B R C τ hτ
  set U : Matrix (R) (R) ℂ :=
    ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) with hU
  set S : Matrix (R) (R) ℂ := star U with hS
  have hU1 : U * S = 1 := Unitary.coe_mul_star_self _
  have h1 : (1 : Matrix (R) (R) ℂ) = U * 1 * S := by
    calc (1 : Matrix (R) (R) ℂ) = U * S := hU1.symm
      _ = U * 1 * S := by rw [Matrix.mul_one]
  have hD : Matrix.diagonal (fun k : R =>
      RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
        (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) =
      1 - (τ : ℂ) • Matrix.diagonal (fun k =>
        (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    funext k
    have hne := Dtau_ne B R C τ hτ k
    set a : ℂ := RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ) with ha
    set lam : ℂ := RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) with hlam
    have h1a : (1 : ℂ) = a * a⁻¹ := (mul_inv_cancel₀ hne).symm
    calc lam / a = lam * a⁻¹ := by rw [div_eq_mul_inv]
      _ = (a - (τ : ℂ)) * a⁻¹ := by
          have : a - (τ : ℂ) = lam := by rw [ha]; abel
          rw [← this]
      _ = a * a⁻¹ - (τ : ℂ) * a⁻¹ := by rw [sub_mul]
      _ = 1 - (τ : ℂ) * a⁻¹ := by rw [h1a]
      _ = 1 - (τ : ℂ) • a⁻¹ := by rw [smul_eq_mul]
  calc AndersonAC.S6.ridgeProjection C τ
      = 1 - (τ : ℂ) • (C * Cᴴ + (τ : ℂ) • 1)⁻¹ := hR
    _ = U * 1 * S - (τ : ℂ) • (U *
        Matrix.diagonal (fun k =>
          (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹) * S) := by
        nth_rewrite 1 [h1]
        rw [hKinv]
    _ = U *
        (1 - (τ : ℂ) • Matrix.diagonal (fun k =>
          (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹)) * S := by
        have hdist : U * 1 * S - (τ : ℂ) • (U *
            Matrix.diagonal (fun k =>
              (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹) * S) =
            U * (1 - (τ : ℂ) • Matrix.diagonal (fun k =>
              (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹)) * S := by
          have hsmul : (τ : ℂ) • (U *
              Matrix.diagonal (fun k =>
                (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹) * S) =
              (U * ((τ : ℂ) • Matrix.diagonal (fun k =>
                (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))⁻¹))) * S := by
            rw [← Matrix.smul_mul, ← Matrix.mul_smul]
          rw [hsmul, ← Matrix.sub_mul, ← Matrix.mul_sub]
        exact hdist
    _ = U * Matrix.diagonal (fun k =>
        RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
          (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) * S := by
        rw [hD]

/-- `K` acts on eigenvectors by its eigenvalue (as linear maps). -/
private lemma K_toEuclidean_basis (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (k : R) :
    Matrix.toEuclideanLin (C * Cᴴ)
      ((K_isHermitian B R C).eigenvectorBasis k) =
      (K_isHermitian B R C).eigenvalues k •
        ((K_isHermitian B R C).eigenvectorBasis k) := by
  have hMul := (K_isHermitian B R C).mulVec_eigenvectorBasis k
  have hApply : Matrix.toEuclideanLin (C * Cᴴ)
      ((K_isHermitian B R C).eigenvectorBasis k) =
      WithLp.toLp 2 ((C * Cᴴ) *ᵥ
        WithLp.ofLp ((K_isHermitian B R C).eigenvectorBasis k)) := rfl
  rw [hApply]
  have hOfLp : WithLp.ofLp ((K_isHermitian B R C).eigenvectorBasis k) =
      ⇑((K_isHermitian B R C).eigenvectorBasis k) := rfl
  rw [hOfLp, hMul]
  simp [WithLp.toLp_smul]

/-- Eigenvectors for nonzero eigenvalues lie in the range. -/
private lemma mem_range_of_ne (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (k : R) (hne : (K_isHermitian B R C).eigenvalues k ≠ 0) :
    (K_isHermitian B R C).eigenvectorBasis k ∈ AndersonAC.S6.matrixRange C := by
  set v := (K_isHermitian B R C).eigenvectorBasis k with hv
  set lam : ℝ := (K_isHermitian B R C).eigenvalues k with hlam
  have hK : Matrix.toEuclideanLin (C * Cᴴ) v = lam • v :=
    K_toEuclidean_basis B R C k
  have hComp : Matrix.toEuclideanLin (C * Cᴴ) v =
      Matrix.toEuclideanLin C (Matrix.toEuclideanLin Cᴴ v) := by
    rw [Matrix.toLpLin_mul]
    rfl
  rw [hComp] at hK
  have hneC : (lam : ℂ) ≠ 0 :=
    (RCLike.ofReal_eq_zero (K := ℂ)).not.mpr hne
  have hReal : lam • v = (lam : ℂ) • v :=
    (RCLike.real_smul_eq_coe_smul lam v).symm
  rw [hReal] at hK
  have hInv : ((lam : ℂ))⁻¹ • ((lam : ℂ) • v) = v := by
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hneC, one_smul]
  have hV : v = Matrix.toEuclideanLin C
      (((lam : ℂ))⁻¹ • Matrix.toEuclideanLin Cᴴ v) := by
    calc v = ((lam : ℂ))⁻¹ • ((lam : ℂ) • v) := hInv.symm
      _ = ((lam : ℂ))⁻¹ • Matrix.toEuclideanLin C
          (Matrix.toEuclideanLin Cᴴ v) := by rw [← hK]
      _ = Matrix.toEuclideanLin C
          (((lam : ℂ))⁻¹ • Matrix.toEuclideanLin Cᴴ v) := by
          rw [map_smul]
  exact ⟨_, hV.symm⟩

/-- Eigenvectors for zero eigenvalues lie in the orthogonal complement. -/
private lemma mem_orthogonal_of_eq_zero (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (k : R) (hz : (K_isHermitian B R C).eigenvalues k = 0) :
    (K_isHermitian B R C).eigenvectorBasis k ∈
      (AndersonAC.S6.matrixRange C)ᗮ := by
  set v := (K_isHermitian B R C).eigenvectorBasis k with hv
  set A : EuclideanSpace ℂ (B) →ₗ[ℂ] EuclideanSpace ℂ (R) :=
    Matrix.toEuclideanLin C with hA
  have hAdj : Matrix.toEuclideanLin Cᴴ = A.adjoint :=
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint C
  have hK : Matrix.toEuclideanLin (C * Cᴴ) v = 0 := by
    have hbasis := K_toEuclidean_basis B R C k
    rw [hz] at hbasis
    simpa using hbasis
  have hKcomp : Matrix.toEuclideanLin (C * Cᴴ) v = A (A.adjoint v) := by
    rw [Matrix.toLpLin_mul, hAdj]
    rfl
  have hAdv : A.adjoint v = 0 := by
    have hww : @inner ℂ _ _ (A.adjoint v) (A.adjoint v) = 0 := by
      calc @inner ℂ _ _ (A.adjoint v) (A.adjoint v)
          = @inner ℂ _ _ (A (A.adjoint v)) v := by
            rw [LinearMap.adjoint_inner_right]
        _ = @inner ℂ _ _ (Matrix.toEuclideanLin (C * Cᴴ) v) v := by
            rw [hKcomp]
        _ = @inner ℂ _ _ (0 : EuclideanSpace ℂ (R)) v := by rw [hK]
        _ = 0 := inner_zero_left _
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp hww
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨t, ht⟩ := hu
  calc @inner ℂ _ _ v u
      = @inner ℂ _ _ v (A t) := by rw [← ht]
    _ = @inner ℂ _ _ (A.adjoint v) t := by rw [LinearMap.adjoint_inner_left]
    _ = @inner ℂ _ _ (0 : EuclideanSpace ℂ (B)) t := by rw [hAdv]
    _ = 0 := inner_zero_left _

/-- Star projection acts on eigenvectors by the support indicator. -/
private lemma starProjection_basis (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (k : R) :
    (AndersonAC.S6.matrixRange C).starProjection
      ((K_isHermitian B R C).eigenvectorBasis k) =
      (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        ((K_isHermitian B R C).eigenvectorBasis k) := by
  by_cases hz : (K_isHermitian B R C).eigenvalues k = 0
  · simp only [hz, ite_true]
    have hmem := mem_orthogonal_of_eq_zero B R C k hz
    have hzero : (AndersonAC.S6.matrixRange C).starProjection
        ((K_isHermitian B R C).eigenvectorBasis k) = 0 :=
      Submodule.eq_starProjection_of_mem_orthogonal (zero_mem _) (by simpa using hmem)
    rw [hzero, zero_smul]
  · simp only [hz, ite_false]
    have hmem := mem_range_of_ne B R C k hz
    have hself := Submodule.starProjection_eq_self_iff.mpr hmem
    rw [hself, one_smul]

/-- Range projection acts on eigenvectors (as `mulVec`). -/
private lemma P_mulVec_basis (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (k : R) :
    AndersonAC.S6.rangeProjection C *ᵥ
      (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) =
      (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) := by
  have hP : Matrix.toEuclideanLin (AndersonAC.S6.rangeProjection C)
      ((K_isHermitian B R C).eigenvectorBasis k) =
      (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        ((K_isHermitian B R C).eigenvectorBasis k) := by
    have hProj := AndersonAC.SolS6.projection_apply C
      ((K_isHermitian B R C).eigenvectorBasis k)
    rw [hProj]
    exact starProjection_basis B R C k
  have hApply : Matrix.toEuclideanLin (AndersonAC.S6.rangeProjection C)
      ((K_isHermitian B R C).eigenvectorBasis k) =
      WithLp.toLp 2 (AndersonAC.S6.rangeProjection C *ᵥ
        WithLp.ofLp ((K_isHermitian B R C).eigenvectorBasis k)) := rfl
  have hOfLp : WithLp.ofLp ((K_isHermitian B R C).eigenvectorBasis k) =
      (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) := rfl
  rw [hApply, hOfLp] at hP
  by_cases hz : (K_isHermitian B R C).eigenvalues k = 0
  · simp only [hz, ite_true, zero_smul] at hP ⊢
    have hToLp := congrArg WithLp.ofLp hP
    simpa using hToLp
  · simp only [hz, ite_false, one_smul] at hP ⊢
    have hToLp := congrArg WithLp.ofLp hP
    simpa using hToLp

/-- `Q = U*D0*S` acts on eigenvectors (as `mulVec`). -/
private lemma Q_mulVec_basis (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (k : R) :
    ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun j =>
          if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *
        star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ)) *ᵥ
      (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ)) =
      (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) := by
  have hS : (star ((K_isHermitian B R C).eigenvectorUnitary :
      Matrix (R) (R) ℂ)) *ᵥ
      (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) =
      Pi.single k 1 :=
    Matrix.IsHermitian.star_eigenvectorUnitary_mulVec (K_isHermitian B R C) k
  have hD : Matrix.diagonal (fun j =>
      if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *ᵥ
      Pi.single k (1 : ℂ) =
      (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        Pi.single k (1 : ℂ) := by
    have hDiag : Matrix.diagonal (fun j =>
        if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *ᵥ
        Pi.single k (1 : ℂ) =
        Pi.single k
          ((if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) * 1) :=
      Matrix.diagonal_mulVec_single _ k 1
    rw [hDiag, mul_one]
    have hSingle : Pi.single k
        (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) =
        (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
          Pi.single k (1 : ℂ) := by
      by_cases hz : (K_isHermitian B R C).eigenvalues k = 0
      · simp [hz]
      · simp [hz]
    exact hSingle
  have hU : (((K_isHermitian B R C).eigenvectorUnitary :
      Matrix (R) (R) ℂ)) *ᵥ
      ((if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        Pi.single k (1 : ℂ)) =
      (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) := by
    rw [Matrix.mulVec_smul]
    congr 1
    exact Matrix.IsHermitian.eigenvectorUnitary_mulVec (K_isHermitian B R C) k
  calc ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun j =>
          if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *
        star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ)) *ᵥ
      (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ))
      = (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun j =>
          if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1)) *ᵥ
        ((star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ)) *ᵥ
          (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ)) := by
        rw [Matrix.mulVec_mulVec]
    _ = (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun j =>
          if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1)) *ᵥ
        Pi.single k 1 := by rw [hS]
    _ = ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *ᵥ
        (Matrix.diagonal (fun j =>
          if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *ᵥ
          Pi.single k 1) := by rw [Matrix.mulVec_mulVec]
    _ = ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *ᵥ
        ((if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
          Pi.single k 1) := by rw [hD]
    _ = (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) •
        (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) := hU

/-- Range projection equals the spectral indicator matrix. -/
private lemma rangeProjection_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) :
    AndersonAC.S6.rangeProjection C =
      (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun j =>
          if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *
        star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ)) := by
  have hPQ : ∀ k : R,
      AndersonAC.S6.rangeProjection C *ᵥ
        (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) =
      ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
        Matrix.diagonal (fun j =>
          if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *
        star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ)) *ᵥ
        (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ)) := by
    intro k
    rw [P_mulVec_basis B R C k, Q_mulVec_basis B R C k]
  let bE : Module.Basis (R) ℂ (EuclideanSpace ℂ (R)) :=
    (K_isHermitian B R C).eigenvectorBasis.toBasis
  let e : EuclideanSpace ℂ (R) ≃ₗ[ℂ] (R → ℂ) :=
    WithLp.linearEquiv 2 ℂ (R → ℂ)
  let bF : Module.Basis (R) ℂ (R → ℂ) := bE.map e
  have hBF : ∀ k : R, bF k =
      (⇑((K_isHermitian B R C).eigenvectorBasis k) : R → ℂ) := by
    intro k
    rfl
  have hLin : Matrix.toLin' (AndersonAC.S6.rangeProjection C) =
      Matrix.toLin'
        ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
          Matrix.diagonal (fun j =>
            if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *
          star ((K_isHermitian B R C).eigenvectorUnitary :
            Matrix (R) (R) ℂ))) := by
    apply bF.ext
    intro k
    have h1 : Matrix.toLin' (AndersonAC.S6.rangeProjection C) (bF k) =
        AndersonAC.S6.rangeProjection C *ᵥ (bF k) := rfl
    have h2 : Matrix.toLin'
        ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
          Matrix.diagonal (fun j =>
            if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *
          star ((K_isHermitian B R C).eigenvectorUnitary :
            Matrix (R) (R) ℂ))) (bF k) =
        ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
          Matrix.diagonal (fun j =>
            if (K_isHermitian B R C).eigenvalues j = 0 then (0 : ℂ) else 1) *
          star ((K_isHermitian B R C).eigenvectorUnitary :
            Matrix (R) (R) ℂ)) *ᵥ (bF k)) := rfl
    rw [h1, h2, hBF k]
    exact hPQ k
  exact Matrix.toLin'.injective hLin

/-- Real scalar ridge ratio tends to the support indicator. -/
private lemma real_ratio_tendsto (lam : ℝ) (hlam : 0 ≤ lam) :
    Tendsto (fun τ : ℝ => lam / (lam + τ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (if lam = 0 then (0 : ℝ) else 1)) := by
  by_cases hz : lam = 0
  · simp only [hz, ite_true]
    have hconst : (fun τ : ℝ => (0 : ℝ) / ((0 : ℝ) + τ)) = fun _ => (0 : ℝ) := by
      funext τ
      simp
    rw [hconst]
    exact tendsto_const_nhds
  · simp only [hz, ite_false]
    have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hz)
    have hne : lam ≠ 0 := hz
    have hDen : Tendsto (fun τ : ℝ => lam + τ) (nhds (0 : ℝ)) (nhds lam) := by
      have : Tendsto (fun τ : ℝ => lam + τ) (nhds (0 : ℝ)) (nhds (lam + 0)) :=
        tendsto_const_nhds.add tendsto_id
      simpa using this
    have hDiv : Tendsto (fun τ : ℝ => lam / (lam + τ)) (nhds (0 : ℝ))
        (nhds (lam / lam)) :=
      tendsto_const_nhds.div hDen hne
    rw [div_self hne] at hDiv
    exact hDiv.mono_left nhdsWithin_le_nhds

/-- Complex diagonal entries tend to the indicator. -/
private lemma diag_entry_tendsto (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (k : R) :
    Tendsto (fun τ : ℝ =>
        RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
          (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1)) := by
  have hReal := real_ratio_tendsto ((K_isHermitian B R C).eigenvalues k)
    (K_eig_nonneg B R C k)
  have hCont : Continuous ((↑) : ℝ → ℂ) := Complex.continuous_ofReal
  have hComp : Tendsto (fun τ : ℝ =>
      (( (K_isHermitian B R C).eigenvalues k / ((K_isHermitian B R C).eigenvalues k + τ) : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℝ) else 1) : ℝ) : ℂ)) :=
    (hCont.tendsto _).comp hReal
  have hEqFun : (fun τ : ℝ =>
      RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
        (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) =
      (fun τ : ℝ => (((K_isHermitian B R C).eigenvalues k /
        ((K_isHermitian B R C).eigenvalues k + τ) : ℝ) : ℂ)) := by
    funext τ
    simp only [RCLike.ofReal_eq_complex_ofReal]
    push_cast
    ring
  have hEqNhds : ((((if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℝ) else 1) : ℝ) : ℂ)) =
      (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) := by
    by_cases hz : (K_isHermitian B R C).eigenvalues k = 0
    · simp [hz]
    · simp [hz]
  rw [← hEqFun, hEqNhds] at hComp
  exact hComp

/-- Ridge entries as finite sums in the eigenbasis (for `τ > 0`). -/
private lemma ridge_entry (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) (i j : R) :
    AndersonAC.S6.ridgeProjection C τ i j =
      ∑ k : R,
        (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
          (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
            (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) *
          star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j) := by
  have hR := ridge_diag_eq B R C τ hτ
  have hEq : AndersonAC.S6.ridgeProjection C τ i j =
      ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
          Matrix.diagonal (fun k =>
            RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
              (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) *
          star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ)) i j) := by
    rw [hR]
  rw [hEq, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_diagonal]

/-- Range-projection entries as finite sums in the eigenbasis. -/
private lemma range_entry (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (i j : R) :
    AndersonAC.S6.rangeProjection C i j =
      ∑ k : R,
        (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
          (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) *
          star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j) := by
  have hP := rangeProjection_eq B R C
  have hEq : AndersonAC.S6.rangeProjection C i j =
      ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) *
          Matrix.diagonal (fun k =>
            if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1) *
          star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ)) i j) := by
    rw [hP]
  rw [hEq, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_diagonal]

theorem ridgeLimit_proof (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) :
    Tendsto (AndersonAC.S6.ridgeProjection C) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (AndersonAC.S6.rangeProjection C)) := by
  have hEntry : ∀ i j : R,
      Tendsto (fun τ : ℝ => AndersonAC.S6.ridgeProjection C τ i j)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (AndersonAC.S6.rangeProjection C i j)) := by
    intro i j
    have hTerm : ∀ k : R,
        Tendsto (fun τ : ℝ =>
            (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
              (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
                (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) *
              star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
            (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1)) *
            star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j)) := by
      intro k
      have hDr := diag_entry_tendsto B R C k
      have hMul1 : Tendsto (fun τ : ℝ =>
          ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
            (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
              (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
            (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1))) :=
        tendsto_const_nhds.mul hDr
      exact hMul1.mul tendsto_const_nhds
    have hSum : Tendsto (fun τ : ℝ => ∑ k : R,
            (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
              (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
                (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) *
              star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ k : R,
          ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
            (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1)) *
            star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j))) :=
      tendsto_finsetSum _ fun k _ => hTerm k
    have hSumP : (∑ k : R,
        ((((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
          (if (K_isHermitian B R C).eigenvalues k = 0 then (0 : ℂ) else 1)) *
          star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j)) =
        AndersonAC.S6.rangeProjection C i j := by
      rw [← range_entry B R C i j]
    rw [hSumP] at hSum
    have hEventually : (fun τ : ℝ => AndersonAC.S6.ridgeProjection C τ i j) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun τ : ℝ => ∑ k : R,
          (((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) i k *
            (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) /
              (RCLike.ofReal ((K_isHermitian B R C).eigenvalues k) + (τ : ℂ))) *
            star ((K_isHermitian B R C).eigenvectorUnitary : Matrix (R) (R) ℂ) k j)) := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro τ hτ
      have hτpos : 0 < τ := Set.mem_Ioi.mp hτ
      exact ridge_entry B R C τ hτpos i j
    exact Filter.Tendsto.congr' hEventually.symm hSum
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hEntry i j


end AndersonAC.SolS6RidgeLim
