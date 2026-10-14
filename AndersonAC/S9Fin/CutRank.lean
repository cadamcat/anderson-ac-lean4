import AndersonAC.S9Fin.SchurProof
import AndersonAC.S9Rank.Rank

noncomputable section
open AndersonAC.S9
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma matrixOpNorm_eq (M : Matrix n n ℂ) : matrixOpNorm M = ‖M‖ := rfl

lemma starAlgEquiv_matrix_inv (φ : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ)
    (M : Matrix n n ℂ) (hM : IsUnit M) : (φ M)⁻¹ = φ M⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← map_mul, Matrix.nonsing_inv_mul M (M.isUnit_iff_isUnit_det.mp hM), map_one]

lemma dampingFunction_diagonal (η : ℝ) (v : n → ℝ) :
    dampingFunction η (Matrix.diagonal (fun i => (v i : ℂ))) =
      Matrix.diagonal (fun i => (v i : ℂ) / (1 - (η * Complex.I) * (v i : ℂ))) := by
  have hn : ∀ i, 1 - (η * Complex.I) * (v i : ℂ) ≠ 0 := by
    intro i h
    have hh := congrArg Complex.re h
    simp at hh
  have heq : 1 - (η * Complex.I) • Matrix.diagonal (fun i => (v i : ℂ)) =
      Matrix.diagonal (fun i => 1 - (η * Complex.I) * (v i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hinv : (Matrix.diagonal (fun i => 1 - (η * Complex.I) * (v i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i => (1 - (η * Complex.I) * (v i : ℂ))⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j <;> simp [hij, hn, Matrix.one_apply]
  unfold dampingFunction
  rw [heq, hinv, Matrix.diagonal_mul_diagonal]
  simp only [div_eq_mul_inv]

lemma scalar_damping_norm_le (u η : ℝ) (hη : 0 < η) :
    ‖(u : ℂ) / (1 - (η * Complex.I) * (u : ℂ))‖ ≤ 1 / η := by
  have hn : 1 - (η * Complex.I) * (u : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  have hden : 0 < ‖1 - (η * Complex.I) * (u : ℂ)‖ := norm_pos_iff.mpr hn
  have hbound : η * |u| ≤ ‖1 - (η * Complex.I) * (u : ℂ)‖ := by
    simpa [Complex.mul_im, abs_mul, abs_of_pos hη] using
      Complex.abs_im_le_norm (1 - (η * Complex.I) * (u : ℂ))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hden]
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hη]
  simpa [mul_comm] using hbound

lemma dampingFunction_norm_le (B : Matrix n n ℂ) (hB : B.IsHermitian)
    (η : ℝ) (hη : 0 < η) : matrixOpNorm (dampingFunction η B) ≤ 1 / η := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary
  let V := Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ))
  have hV : V.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [isSelfAdjoint_iff]
  have hBV : B = φ V := hB.spectral_theorem
  have hd : dampingFunction η B = φ (dampingFunction η V) := by
    unfold dampingFunction
    rw [hBV]
    have hf : 1 - (η * Complex.I) • φ V = φ (1 - (η * Complex.I) • V) := by
      simp only [map_sub, map_one, map_smul]
    rw [hf, starAlgEquiv_matrix_inv φ _ (damping_isUnit V hV η), ← map_mul]
  rw [hd, matrixOpNorm_eq]
  change ‖φ (dampingFunction η V)‖ ≤ 1 / η
  simp only [φ, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  rw [show V = Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)) from rfl,
    dampingFunction_diagonal, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    (fun i => scalar_damping_norm_le _ η hη)

lemma windowProjection_isHermitian (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) :
    (windowProjection H hH E δ).IsHermitian := by
  classical
  apply Matrix.isHermitian_mul_mul_conjTranspose
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  split_ifs <;> simp

lemma windowProjection_commute (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) :
    Commute (H - (E : ℂ) • 1) (windowProjection H hH E δ) := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
  let V := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let W := Matrix.diagonal (fun i : n => if |hH.eigenvalues i - E| ≤ δ then (1 : ℂ) else 0)
  have hH0 : H - (E : ℂ) • 1 = φ (V - (E : ℂ) • 1) := by
    simp only [map_sub, map_smul, map_one]
    have hHV : H = φ V := hH.spectral_theorem
    rw [hHV]
  have hQ : windowProjection H hH E δ = φ W := rfl
  rw [hH0, hQ]
  change φ (V - (E : ℂ) • 1) * φ W = φ W * φ (V - (E : ℂ) • 1)
  rw [← map_mul, ← map_mul]
  apply congrArg φ
  have hd : Commute V W := by
    change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, hd.eq]

lemma cutInverse_isHermitian (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ε : ℝ)
    (hprincipal : allPrincipalInvertible H E) : (cutInverse H hH E η ε).IsHermitian := by
  let H0 := H - (E : ℂ) • 1
  let Q := windowProjection H hH E (ε * η)
  have hH0 : H0.IsHermitian := hH.sub (by simp [Matrix.IsHermitian])
  have hu : IsUnit H0 := allPrincipalInvertible_isUnit H E hprincipal
  have hud : IsUnit H0.det := H0.isUnit_iff_isUnit_det.mp hu
  have hc : H0 * Q = Q * H0 := (windowProjection_commute H hH E (ε * η)).eq
  have hci : H0⁻¹ * Q = Q * H0⁻¹ := by
    apply hu.mul_left_cancel
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv H0 hud, one_mul,
      ← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv H0 hud, mul_one]
  change (H0⁻¹ * (1 - Q)).IsHermitian
  change star (H0⁻¹ * (1 - Q)) = H0⁻¹ * (1 - Q)
  rw [star_mul, star_sub, star_one, (windowProjection_isHermitian H hH E (ε * η)).star_eq,
    hH0.inv.star_eq, sub_mul, mul_sub, one_mul, mul_one, hci]

set_option linter.unusedVariables false in
theorem cut_rank_hilbertSchmidt_proof (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n) :
    let D := dampingFunction η (compress A ((H - (E : ℂ) • 1)⁻¹)) -
      dampingFunction η (compress A (cutInverse H hH E η ε))
    Matrix.rank D ≤ windowRank H hH E (ε * η) ∧
      matrixOpNorm D ≤ 2 / η ∧
      hilbertSchmidtSq D ≤ 4 * (windowRank H hH E (ε * η) : ℝ) / η ^ 2 := by
  let T := (H - (E : ℂ) • 1)⁻¹
  let Q := windowProjection H hH E (ε * η)
  let B := compress A T
  let C := compress A (cutInverse H hH E η ε)
  let D := dampingFunction η B - dampingFunction η C
  have hB : B.IsHermitian := (hH.sub (by simp [Matrix.IsHermitian])).inv.submatrix _
  have hC : C.IsHermitian := (cutInverse_isHermitian H hH E η ε hprincipal).submatrix _
  have hdiff : B - C = compress A (T * Q) := by
    change compress A T - compress A (T * (1 - Q)) = compress A (T * Q)
    rw [mul_sub, mul_one]
    ext i j
    simp [compress]
  have hrBC : Matrix.rank (B - C) ≤ Matrix.rank Q := by
    rw [hdiff]
    exact (Matrix.rank_submatrix_le (T * Q) _ _).trans (Matrix.rank_mul_le_right T Q)
  have hr : Matrix.rank D ≤ windowRank H hH E (ε * η) := by
    change Matrix.rank (dampingFunction η B - dampingFunction η C) ≤ Matrix.rank Q
    rw [dampingFunction_difference_proof B C hB hC η hη]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans hrBC)
  have hn : matrixOpNorm D ≤ 2 / η := by
    calc
      matrixOpNorm D ≤ matrixOpNorm (dampingFunction η B) +
          matrixOpNorm (dampingFunction η C) := by
        simp only [D, matrixOpNorm_eq]
        exact norm_sub_le _ _
      _ ≤ 1 / η + 1 / η := add_le_add (dampingFunction_norm_le B hB η hη)
        (dampingFunction_norm_le C hC η hη)
      _ = 2 / η := by ring
  refine ⟨hr, hn, ?_⟩
  have hn0 : 0 ≤ matrixOpNorm D := norm_nonneg _
  calc
    hilbertSchmidtSq D ≤ (Matrix.rank D : ℝ) * matrixOpNorm D ^ 2 :=
      rankHilbertSchmidt_proof _ D
    _ ≤ (windowRank H hH E (ε * η) : ℝ) * (2 / η) ^ 2 :=
      mul_le_mul (by exact_mod_cast hr) (pow_le_pow_left₀ hn0 hn 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ = 4 * (windowRank H hH E (ε * η) : ℝ) / η ^ 2 := by ring

end AndersonAC.SolS9
