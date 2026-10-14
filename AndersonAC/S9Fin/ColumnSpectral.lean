import AndersonAC.S9Fin.PoissonTrace

noncomputable section
open AndersonAC.S9
open scoped Matrix ComplexConjugate

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Adapted from the checked S9Cut/Spectral support in luna-s9cut.
lemma column_unitary_norm_map (U : unitary (Matrix n n ℂ))
    (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) x‖ = ‖x‖ := by
  let V := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ)
  have hAdj : V.adjoint =
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star (U : Matrix n n ℂ)) := by
    have h := map_star (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
      (U : Matrix n n ℂ)
    simpa only [ContinuousLinearMap.star_eq_adjoint] using h.symm
  have hcomp : V.adjoint ∘L V = 1 := by
    calc
      V.adjoint ∘L V = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
          (star (U : Matrix n n ℂ)) *
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) := by
        rw [hAdj, ← ContinuousLinearMap.mul_def]
      _ = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
          (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) := by rw [← map_mul]
      _ = 1 := by rw [Unitary.coe_star_mul_self U]; simp
  exact (V.norm_map_iff_adjoint_comp_self).mpr hcomp x

lemma conjugated_diagonal_columnNormSq (U : unitary (Matrix n n ℂ))
    (v : n → ℂ) (i : n) :
    columnNormSq (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U (Matrix.diagonal v)) i =
      ∑ j, ‖v j‖ ^ 2 * ‖star (U : Matrix n n ℂ) j i‖ ^ 2 := by
  rw [columnNormSq_eq_norm]
  change ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U (Matrix.diagonal v))
      (EuclideanSpace.single i 1)‖ ^ 2 = _
  rw [Unitary.conjStarAlgAut_apply, map_mul, map_mul]
  change ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ)
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.diagonal v)
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star (U : Matrix n n ℂ))
        (EuclideanSpace.single i 1)))‖ ^ 2 = _
  rw [column_unitary_norm_map]
  have hv : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (Matrix.diagonal v)
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (star (U : Matrix n n ℂ))
        (EuclideanSpace.single i 1)) =
      WithLp.toLp 2 (fun j => v j * star (U : Matrix n n ℂ) j i) := by
    change WithLp.toLp 2 (Matrix.diagonal v *ᵥ
      (star (U : Matrix n n ℂ) *ᵥ Pi.single i 1)) = _
    rw [Matrix.mulVec_single_one]
    congr 1
    funext j
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [hv, EuclideanSpace.norm_sq_eq]
  change (∑ j, ‖v j * star (U : Matrix n n ℂ) j i‖ ^ 2) = _
  simp only [norm_mul, mul_pow]

lemma conjugated_diagonal_column_le (U : unitary (Matrix n n ℂ))
    (a b : n → ℂ) (C : ℝ) (h : ∀ j, ‖a j‖ ^ 2 ≤ C * ‖b j‖ ^ 2) (i : n) :
    columnNormSq (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U (Matrix.diagonal a)) i ≤
      C * columnNormSq (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U (Matrix.diagonal b)) i := by
  rw [conjugated_diagonal_columnNormSq, conjugated_diagonal_columnNormSq, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h j)
      (sq_nonneg ‖star (U : Matrix n n ℂ) j i‖)

lemma damping_scalar_contract (η u : ℝ) :
    ‖(u : ℂ) / (1 - (η * Complex.I) * (u : ℂ))‖ ^ 2 ≤ ‖(u : ℂ)‖ ^ 2 := by
  have hd : 1 ≤ ‖1 - (η * Complex.I) * (u : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (1 - (η * Complex.I) * (u : ℂ))
  have hn : ‖(u : ℂ) / (1 - (η * Complex.I) * (u : ℂ))‖ ≤ ‖(u : ℂ)‖ := by
    rw [norm_div]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
    nlinarith [norm_nonneg (u : ℂ)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn

/-- Apply functional calculus on the compressed Hermitian space itself. -/
lemma dampingFunction_columnNormSq_le (B : Matrix n n ℂ) (hB : B.IsHermitian)
    (η : ℝ) (i : n) : columnNormSq (dampingFunction η B) i ≤ columnNormSq B i := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary
  let V := Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ))
  have hV : V.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro j
    simp [V, isSelfAdjoint_iff]
  have hBV : B = φ V := hB.spectral_theorem
  have hF : dampingFunction η B = φ (dampingFunction η V) := by
    unfold dampingFunction
    rw [hBV]
    have hInside : 1 - (η * Complex.I) • φ V = φ (1 - (η * Complex.I) • V) := by
      simp only [map_sub, map_one, map_smul]
    rw [hInside, starAlgEquiv_matrix_inv φ _ (damping_isUnit V hV η), ← map_mul]
  rw [hF, hBV]
  change columnNormSq (φ (dampingFunction η (Matrix.diagonal
    (fun j => (hB.eigenvalues j : ℂ))))) i ≤ _
  rw [dampingFunction_diagonal]
  have h := conjugated_diagonal_column_le hB.eigenvectorUnitary
    (fun j => (hB.eigenvalues j : ℂ) /
      (1 - (η * Complex.I) * (hB.eigenvalues j : ℂ)))
    (fun j => (hB.eigenvalues j : ℂ)) 1
    (fun j => by simpa using damping_scalar_contract η (hB.eigenvalues j)) i
  simpa only [one_mul] using h

lemma compress_columnNormSq_le (A : Finset n) (T : Matrix n n ℂ) (i : A) :
    columnNormSq (compress A T) i ≤ columnNormSq T i := by
  classical
  unfold columnNormSq compress
  simp only [Matrix.submatrix_apply]
  calc
    (∑ j : A, ‖T j i‖ ^ 2) = ∑ j ∈ A, ‖T j i‖ ^ 2 := by
      simpa only [Finset.attach_eq_univ] using Finset.sum_attach A (fun j => ‖T j i‖ ^ 2)
    _ ≤ ∑ j : n, ‖T j i‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _ => sq_nonneg _)

end AndersonAC.SolS9
