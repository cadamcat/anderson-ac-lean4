import AndersonAC.S9Fin.Scalar

noncomputable section
open AndersonAC.S9
open scoped Matrix ComplexConjugate

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

def siteProjection (i : n) : Matrix n n ℂ :=
  Matrix.diagonal (fun j => if j = i then 1 else 0)

lemma siteProjection_mul_entry (X Y : Matrix n n ℂ) (i : n) :
    (X * siteProjection i * Y) i i = X i i * Y i i := by
  unfold siteProjection
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp

lemma inverse_rank_one_diagonal (A B : Matrix n n ℂ) (i : n) (α : ℂ)
    (hA : IsUnit A) (hB : IsUnit B)
    (hBA : B = A + α • siteProjection i) (h0 : A⁻¹ i i ≠ 0) :
    B⁻¹ i i = (α + (A⁻¹ i i)⁻¹)⁻¹ := by
  have hinv := Matrix.inv_sub_inv (A := A) (B := B) (iff_of_true hA hB)
  have hBsub : B - A = α • siteProjection i := by rw [hBA]; abel
  rw [hBsub] at hinv
  have hdiag := congrArg (fun M : Matrix n n ℂ => M i i) hinv
  have hmul : (A⁻¹ * (α • siteProjection i) * B⁻¹) i i =
      α * (A⁻¹ i i) * (B⁻¹ i i) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    rw [siteProjection_mul_entry]
    ring
  rw [hmul] at hdiag
  let g₀ := A⁻¹ i i
  let g := B⁻¹ i i
  have hg₀ : g₀ ≠ 0 := by simpa [g₀] using h0
  have hsum : g₀ = (1 + α * g₀) * g := by
    dsimp [g₀, g] at hdiag ⊢
    calc
      A⁻¹ i i = (A⁻¹ i i - B⁻¹ i i) + B⁻¹ i i := by ring
      _ = α * (A⁻¹ i i) * (B⁻¹ i i) + B⁻¹ i i := by rw [hdiag]
      _ = (1 + α * (A⁻¹ i i)) * (B⁻¹ i i) := by ring
  have hprod : (α + g₀⁻¹) * g = 1 := by
    field_simp [hg₀]
    linear_combination -hsum
  rw [eq_inv_of_mul_eq_one_left hprod, inv_inv]

lemma matrixResolvent_diagonal_im_pos (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (i : n) :
    0 < (matrixResolvent H E η i i).im := by
  let A := H - ((E : ℂ) + η * Complex.I) • 1
  have hA : IsUnit A := by
    dsimp [A]
    rw [scalar_damped_matrix_eq]
    exact damped_isUnit (H - (E : ℂ) • 1)
      (hH.sub (by simp [Matrix.IsHermitian])) η 1 hη zero_lt_one
      (fun _ : n => Complex.I) (by norm_num)
  have hdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA
  have hmul := Matrix.mul_nonsing_inv A hdet
  have hentry : (∑ j, A i j * A⁻¹ j i) = 1 := by
    have hh := congrArg (fun M : Matrix n n ℂ => M i i) hmul
    simpa [Matrix.mul_apply, Matrix.one_apply] using hh
  have hsome : ∃ j, A⁻¹ j i ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (∑ j, A i j * A⁻¹ j i) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [h j]
      simp
    rw [hz] at hentry
    norm_num at hentry
  obtain ⟨j, hj⟩ := hsome
  have hterm : 0 < ‖A⁻¹ j i‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hj)
  have hsum : 0 < ∑ k, ‖A⁻¹ k i‖ ^ 2 :=
    lt_of_lt_of_le hterm
      (Finset.single_le_sum (fun k hk => sq_nonneg (‖A⁻¹ k i‖)) (Finset.mem_univ j))
  have hcol : 0 < columnNormSq (matrixResolvent H E η) i := by
    simpa [columnNormSq, matrixResolvent, A] using hsum
  have hq : 0 < scalarQ H E η i := by
    rw [scalarQ_eq_ward H hH E η hη i]
    exact mul_pos hη hcol
  simpa [scalarQ] using hq

lemma matrixResolvent_add_siteProjection_diagonal
    (H H' : Matrix n n ℂ) (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (α : ℂ) (i : n)
    (hpert : H' = H + α • siteProjection i) :
    matrixResolvent H' E η i i =
      ((matrixResolvent H E η i i)⁻¹ + α)⁻¹ := by
  let A := H - ((E : ℂ) + η * Complex.I) • 1
  let B := H' - ((E : ℂ) + η * Complex.I) • 1
  have hA : IsUnit A := by
    dsimp [A]
    rw [scalar_damped_matrix_eq]
    exact damped_isUnit (H - (E : ℂ) • 1)
      (hH.sub (by simp [Matrix.IsHermitian])) η 1 hη zero_lt_one
      (fun _ : n => Complex.I) (by norm_num)
  have hB : IsUnit B := by
    dsimp [B]
    rw [scalar_damped_matrix_eq]
    exact damped_isUnit (H' - (E : ℂ) • 1)
      (hH'.sub (by simp [Matrix.IsHermitian])) η 1 hη zero_lt_one
      (fun _ : n => Complex.I) (by norm_num)
  have hBA : B = A + α • siteProjection i := by
    ext j k
    simp [A, B, hpert, siteProjection, Matrix.diagonal_apply] <;> ring
  have h0 : A⁻¹ i i ≠ 0 := by
    have hp := matrixResolvent_diagonal_im_pos H hH E η hη i
    have hpeq : A⁻¹ = matrixResolvent H E η := rfl
    rw [← hpeq] at hp
    intro hz
    rw [hz] at hp
    norm_num at hp
  have h := inverse_rank_one_diagonal A B i α hA hB hBA h0
  simpa [A, B, matrixResolvent, add_comm] using h

lemma matrixResolvent_inverse_diagonal_im_neg (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η) (i : n) :
    0 < -((matrixResolvent H E η i i)⁻¹).im := by
  have hpos := matrixResolvent_diagonal_im_pos H hH E η hη i
  have hne : matrixResolvent H E η i i ≠ 0 := by
    intro hz
    rw [hz] at hpos
    norm_num at hpos
  have hnorm : 0 < Complex.normSq (matrixResolvent H E η i i) :=
    Complex.normSq_pos.mpr hne
  rw [Complex.inv_im]
  exact neg_pos.mpr (div_neg_of_neg_of_pos (by linarith) hnorm)

lemma scalarQ_rankOne_cauchy_kernel
    (H H' : Matrix n n ℂ) (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (E η a : ℝ) (hη : 0 < η) (i : n)
    (hpert : H' = H + (a : ℂ) • siteProjection i) :
    scalarQ H' E η i =
      (-((matrixResolvent H E η i i)⁻¹).im) /
        ((a + (matrixResolvent H E η i i)⁻¹).re ^ 2 +
          ((matrixResolvent H E η i i)⁻¹).im ^ 2) := by
  rw [scalarQ, matrixResolvent_add_siteProjection_diagonal H H' hH hH' E η hη
    (a : ℂ) i hpert]
  let z := (matrixResolvent H E η i i)⁻¹
  change ((z + (a : ℂ))⁻¹).im = -z.im / ((a + z.re) ^ 2 + z.im ^ 2)
  rw [Complex.inv_im, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im]
  ring

end AndersonAC.SolS9
