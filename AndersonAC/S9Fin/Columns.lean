import AndersonAC.S9Fin.Dissipative

noncomputable section
open AndersonAC.S9
open scoped Matrix ComplexConjugate

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma activeSchur_isHermitian (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E : ℝ) (A : Finset n) : (activeSchur H E A).IsHermitian := by
  let H0 := H - (E : ℂ) • 1
  let Ac := Finset.univ \ A
  let U := H0.submatrix (fun j : Ac => (j : n)) (fun i : A => (i : n))
  have hH0 : H0.IsHermitian := hH.sub (by simp [Matrix.IsHermitian])
  have hAc : (compress Ac H0).IsHermitian := hH0.submatrix _
  have hcross : H0.submatrix (fun i : A => (i : n)) (fun j : Ac => (j : n)) = Uᴴ := by
    ext i j
    exact (hH0.apply i j).symm
  change (compress A H0 - H0.submatrix (fun i : A => (i : n))
    (fun j : Ac => (j : n)) * (compress Ac H0)⁻¹ * U).IsHermitian
  rw [hcross]
  exact (hH0.submatrix _).sub (Matrix.isHermitian_conjTranspose_mul_mul U hAc.inv)

lemma columnNormSq_eq_norm (G : Matrix n n ℂ) (i : n) :
    columnNormSq G i = ‖G.toEuclideanLin (EuclideanSpace.single i 1)‖ ^ 2 := by
  have hv : G.toEuclideanLin (EuclideanSpace.single i 1) = WithLp.toLp 2 (fun j => G j i) := by
    change WithLp.toLp 2 (G *ᵥ Pi.single i 1) = WithLp.toLp 2 (fun j => G j i)
    rw [Matrix.mulVec_single_one]
    rfl
  rw [hv, EuclideanSpace.norm_sq_eq]
  rfl

lemma norm_diagonal_apply_le (v : n → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ i, ‖v i‖ ≤ C) (x : EuclideanSpace ℂ n) :
    ‖(Matrix.diagonal v).toEuclideanLin x‖ ≤ C * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow]
  simp only [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖(Matrix.diagonal v *ᵥ WithLp.ofLp x) i‖ ^ 2) ≤ C ^ 2 * ∑ i, ‖x i‖ ^ 2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Matrix.mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hv i)) (sq_nonneg _)

lemma matrixImaginaryPart_diag (G : Matrix n n ℂ) (i : n) :
    matrixImaginaryPart G i i = ((G i i).im : ℂ) := by
  unfold matrixImaginaryPart
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.star_apply, smul_eq_mul]
  apply Complex.ext <;> norm_num [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

lemma weighted_ward_diag (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η : ℝ) (hη : 0 < η) (r : n → ℂ) (hr : ∀ i, 0 < (r i).im) (i : n) :
    ((S - (η : ℂ) • Matrix.diagonal r)⁻¹ i i).im =
      η * ∑ j, (r j).im * ‖(S - (η : ℂ) • Matrix.diagonal r)⁻¹ j i‖ ^ 2 := by
  let G := (S - (η : ℂ) • Matrix.diagonal r)⁻¹
  have hw := congrArg (fun M : Matrix n n ℂ => M i i)
    (damped_ward_identity_proof S hS η hη r hr)
  change matrixImaginaryPart G i i =
    ((η : ℂ) • (star G * Matrix.diagonal (fun j => ((r j).im : ℂ)) * G)) i i at hw
  rw [matrixImaginaryPart_diag] at hw
  have heq : (star G * Matrix.diagonal (fun j => ((r j).im : ℂ)) * G) i i =
      ((∑ j, (r j).im * ‖G j i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    change star (G j i) * ((r j).im : ℂ) * G j i = ((r j).im : ℂ) * (‖G j i‖ : ℂ) ^ 2
    calc
      _ = ((r j).im : ℂ) * (G j i * star (G j i)) := by ring
      _ = _ := by rw [RCLike.star_def, RCLike.mul_conj]; rfl
  rw [Matrix.smul_apply, smul_eq_mul, heq, ← Complex.ofReal_mul] at hw
  exact Complex.ofReal_injective hw

lemma comparisonConstant_pos (b : CertificateBounds) : 0 < comparisonConstant b := by
  unfold comparisonConstant
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (by linarith [b.B_nonneg]) b.pMin_pos.le)

set_option maxHeartbeats 1200000 in
lemma certified_column_general (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (η : ℝ) (hη : 0 < η) (b : CertificateBounds) (r : n → ℂ)
    (hr : ∀ i, ‖r i‖ ≤ b.B ∧ b.pMin ≤ (r i).im ∧ (r i).im ≤ b.pMax)
    (i : n) (hq : b.qMin ≤ ((S - (η : ℂ) • Matrix.diagonal r)⁻¹ i i).im) :
    columnConstant b ≤ η * columnNormSq ((S - (η * Complex.I) • 1)⁻¹) i := by
  let A := S - (η : ℂ) • Matrix.diagonal r
  let F := S - (η * Complex.I) • 1
  let G := A⁻¹
  let V := F⁻¹
  let ei : EuclideanSpace ℂ n := EuclideanSpace.single i 1
  have hA : IsUnit A := damped_isUnit S hS η b.pMin hη b.pMin_pos r (fun j => (hr j).2.1)
  have hconst : Matrix.diagonal (fun _ : n => Complex.I) = Complex.I • (1 : Matrix n n ℂ) := by
    ext j k
    by_cases hjk : j = k <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hjk]
  have hF : IsUnit F := by
    have hu := damped_isUnit S hS η 1 hη zero_lt_one (fun _ : n => Complex.I)
      (fun _ => by norm_num)
    simpa only [hconst, smul_smul] using hu
  have hdiff : F - A = (η : ℂ) • Matrix.diagonal (fun j => r j - Complex.I) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp only [F, A, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq, smul_eq_mul]
      ring
    · simp [F, A, Matrix.diagonal_apply, Matrix.one_apply, hjk]
  have hinv := Matrix.inv_sub_inv (A := A) (B := F) (iff_of_true hA hF)
  rw [hdiff] at hinv
  have hact : G.toEuclideanLin ei - V.toEuclideanLin ei =
      G.toEuclideanLin (((η : ℂ) • Matrix.diagonal (fun j => r j - Complex.I)).toEuclideanLin
        (V.toEuclideanLin ei)) := by
    have hv := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin ei) hinv
    simpa only [Matrix.toEuclideanLin, map_sub, LinearMap.sub_apply,
      Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hv
  have hGn : matrixOpNorm G ≤ (η * b.pMin)⁻¹ :=
    dissipative_inverse_bound_proof S hS η b.pMin hη b.pMin_pos r (fun j => (hr j).2.1)
  have hvec (x : EuclideanSpace ℂ n) : ‖G.toEuclideanLin x‖ ≤ (η * b.pMin)⁻¹ * ‖x‖ := by
    exact (G.toEuclideanLin.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hGn (norm_nonneg _))
  have hdr (j : n) : ‖r j - Complex.I‖ ≤ b.B + 1 := by
    calc
      _ ≤ ‖r j‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ ≤ b.B + 1 := by simpa using add_le_add (hr j).1 (le_refl ‖Complex.I‖)
  have hcoef : (η * b.pMin)⁻¹ * η * (b.B + 1) = (b.B + 1) / b.pMin := by
    field_simp [hη.ne', b.pMin_pos.ne']
  have hdelta : ‖G.toEuclideanLin ei - V.toEuclideanLin ei‖ ≤
      ((b.B + 1) / b.pMin) * ‖V.toEuclideanLin ei‖ := by
    rw [hact]
    have hd := norm_diagonal_apply_le (fun j => r j - Complex.I) (b.B + 1)
      (by linarith [b.B_nonneg]) hdr (V.toEuclideanLin ei)
    have hs : ((η : ℂ) • Matrix.diagonal (fun j => r j - Complex.I)).toEuclideanLin
        (V.toEuclideanLin ei) = (η : ℂ) •
        (Matrix.diagonal (fun j => r j - Complex.I)).toEuclideanLin (V.toEuclideanLin ei) := by
      simp only [Matrix.toEuclideanLin, map_smul, LinearMap.smul_apply]
    calc
      _ ≤ (η * b.pMin)⁻¹ *
          ‖((η : ℂ) • Matrix.diagonal (fun j => r j - Complex.I)).toEuclideanLin
            (V.toEuclideanLin ei)‖ := hvec _
      _ = (η * b.pMin)⁻¹ * (η *
          ‖(Matrix.diagonal (fun j => r j - Complex.I)).toEuclideanLin (V.toEuclideanLin ei)‖) := by
        rw [hs, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
      _ ≤ (η * b.pMin)⁻¹ * (η * ((b.B + 1) * ‖V.toEuclideanLin ei‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hη.le)
          ((inv_pos.mpr (mul_pos hη b.pMin_pos)).le)
      _ = ((b.B + 1) / b.pMin) * ‖V.toEuclideanLin ei‖ := by
        rw [← mul_assoc, ← mul_assoc, hcoef]
  have hcmp : ‖G.toEuclideanLin ei‖ ≤ comparisonConstant b * ‖V.toEuclideanLin ei‖ := by
    calc
      _ = ‖V.toEuclideanLin ei + (G.toEuclideanLin ei - V.toEuclideanLin ei)‖ := by congr 1; abel
      _ ≤ ‖V.toEuclideanLin ei‖ + ‖G.toEuclideanLin ei - V.toEuclideanLin ei‖ := norm_add_le _ _
      _ ≤ ‖V.toEuclideanLin ei‖ + ((b.B + 1) / b.pMin) * ‖V.toEuclideanLin ei‖ :=
        add_le_add_right hdelta _
      _ = comparisonConstant b * ‖V.toEuclideanLin ei‖ := by unfold comparisonConstant; ring
  have hcmpSq : columnNormSq G i ≤ comparisonConstant b ^ 2 * columnNormSq V i := by
    rw [columnNormSq_eq_norm, columnNormSq_eq_norm]
    have hh := (sq_le_sq₀ (norm_nonneg (G.toEuclideanLin ei))
      (mul_nonneg (comparisonConstant_pos b).le (norm_nonneg _))).mpr hcmp
    simpa only [mul_pow] using hh
  have hw := weighted_ward_diag S hS η hη r
    (fun j => lt_of_lt_of_le b.pMin_pos (hr j).2.1) i
  have hweighted : (G i i).im ≤ η * (b.pMax * columnNormSq G i) := by
    rw [hw]
    apply mul_le_mul_of_nonneg_left _ hη.le
    unfold columnNormSq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hr j).2.2 (sq_nonneg _))
  have hmax : 0 < b.pMax := lt_of_lt_of_le b.pMin_pos b.pMin_le_pMax
  have hmain := hq.trans (hweighted.trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmpSq hmax.le) hη.le))
  unfold columnConstant
  apply (div_le_iff₀ (mul_pos hmax (sq_pos_of_pos (comparisonConstant_pos b)))).mpr
  change b.qMin ≤ η * columnNormSq V i * (b.pMax * comparisonConstant b ^ 2)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hmain

set_option linter.unusedVariables false in
theorem certified_subset_column_proof (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (b : CertificateBounds)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n) (r : n → ℂ)
    (hr : ∀ i ∈ A, ‖r i‖ ≤ b.B ∧ b.pMin ≤ (r i).im ∧ (r i).im ≤ b.pMax)
    (hq : ∀ i : A, b.qMin ≤
      ((activeSchur H E A - (η : ℂ) • Matrix.diagonal (fun j : A => r j))⁻¹ i i).im) :
    ∀ i : A, columnConstant b ≤ η * columnNormSq
      ((activeSchur H E A - (η * Complex.I) • 1)⁻¹) i := by
  intro i
  exact certified_column_general (activeSchur H E A) (activeSchur_isHermitian H hH E A)
    η hη b (fun j : A => r j) (fun j => hr j j.property) i (hq i)

end AndersonAC.SolS9
