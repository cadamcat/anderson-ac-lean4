import AndersonAC.S2.WardBounds

/-! Symmetry and the finite resolvent Ward identity. -/

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator ComplexOrder

namespace AndersonAC.SolS2
open AndersonAC.S2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem damped_symmetric (M : Matrix ι ι ℝ) (hM : M.IsSymm) (t : ℝ) (r : ι → ℂ) :
    (dampedMatrix M t r).IsSymm :=
  (hM.map Complex.ofReal).sub ((Matrix.isSymm_diagonal r).smul (t : ℂ))

theorem complex_imaginary_difference (z : ℂ) :
    (1 / (2 * Complex.I)) * (z - conj z) = (z.im : ℂ) := by
  have hd : z - conj z = (2 * Complex.I) * (z.im : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hd, div_eq_mul_inv, one_mul, ← mul_assoc,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) Complex.I_ne_zero), one_mul]

theorem damped_star_difference (M : Matrix ι ι ℝ) (hM : M.IsSymm) (t : ℝ) (r : ι → ℂ) :
    (dampedMatrix M t r).conjTranspose - dampedMatrix M t r =
      (2 * Complex.I * (t : ℂ)) • Matrix.diagonal (fun i => ((r i).im : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    apply Complex.ext <;> simp [dampedMatrix, realMatrix, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
  · have hji := Ne.symm hij
    simp [dampedMatrix, realMatrix, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Complex.star_def, hij, hji, hM.apply i j]

theorem inverse_difference (B G : Matrix ι ι ℂ) (hBG : B * G = 1) (hGB : G * B = 1) :
    G - G.conjTranspose = G * (B.conjTranspose - B) * G.conjTranspose := by
  have hstar : B.conjTranspose * G.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hGB, Matrix.conjTranspose_one]
  symm
  calc
    _ = G * B.conjTranspose * G.conjTranspose - (G * B) * G.conjTranspose := by noncomm_ring
    _ = G * 1 - 1 * G.conjTranspose := by rw [mul_assoc, hstar, hGB]
    _ = G - G.conjTranspose := by simp

theorem unnormalized_ward (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    {t : ℝ} (ht : 0 < t) (r : ι → ℂ) (hp : ∀ i, 0 < (r i).im) :
    (t : ℂ) • (resolvent M t r * Matrix.diagonal (fun i => ((r i).im : ℂ)) *
      (resolvent M t r).conjTranspose) = hermitianImaginary (resolvent M t r) := by
  have hu := damped_invertible M hM ht r hp
  have hd := (dampedMatrix M t r).isUnit_iff_isUnit_det.mp hu
  have hBG := (dampedMatrix M t r).mul_nonsing_inv hd
  have hGB := (dampedMatrix M t r).nonsing_inv_mul hd
  have hg := inverse_difference (dampedMatrix M t r) (resolvent M t r) hBG hGB
  rw [damped_star_difference M hM] at hg
  rw [hermitianImaginary, hg, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  field_simp [Complex.I_ne_zero]

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem resolvent_symmetric (M : Matrix ι ι ℝ) (hM : M.IsSymm) (t : ℝ) (r : ι → ℂ) :
    (resolvent M t r).IsSymm ∧ (normalizedResolvent M t r).IsSymm := by
  have hg := (damped_symmetric M hM t r).inv
  exact ⟨hg, hg.smul (Real.sqrt t : ℂ)⟩

theorem symmetric_imaginary (B : Matrix ι ι ℂ) (hB : B.IsSymm) :
    hermitianImaginary B = realMatrix (fun i j => (B i j).im) := by
  ext i j
  simpa only [hermitianImaginary, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.conjTranspose_apply, hB.apply i j, Complex.star_def, realMatrix] using
    complex_imaginary_difference (B i j)

end AndersonAC.S2
