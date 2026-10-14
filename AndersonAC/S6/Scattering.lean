import AndersonAC.S6.Definitions

/-! Scattering algebra from the actual inverse; no planning theorem is imported. -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem sqrtDamping_conjTranspose (p : ι → ℝ) :
    (AndersonAC.S6.sqrtDamping p)ᴴ = AndersonAC.S6.sqrtDamping p := by
  simp [AndersonAC.S6.sqrtDamping, Matrix.diagonal_conjTranspose]

theorem sqrtDamping_sq (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    AndersonAC.S6.sqrtDamping p * AndersonAC.S6.sqrtDamping p =
      Matrix.diagonal (fun i => (p i : ℂ)) := by
  rw [AndersonAC.S6.sqrtDamping, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  norm_cast
  nlinarith [Real.sq_sqrt (hp i)]

theorem inverse_transpose (A G : Matrix ι ι ℂ) (hA : Aᵀ = A)
    (hInv : AndersonAC.Blueprint.twoSidedInverse A G) : Gᵀ = G := by
  have hleft : Gᵀ * A = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one, hA] using
      congrArg Matrix.transpose hInv.1
  calc
    Gᵀ = Gᵀ * (A * G) := by rw [hInv.1, Matrix.mul_one]
    _ = (Gᵀ * A) * G := (Matrix.mul_assoc _ _ _).symm
    _ = G := by rw [hleft, Matrix.one_mul]

end AndersonAC.SolS6

namespace AndersonAC.S6
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scattering_unitary (t : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : g.IsSymm)
    (hWard : g - gᴴ = (2 * Complex.I * (t : ℂ)) •
      (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ)) :
    (scatteringOfDamping t p g).IsSymm ∧
      scatteringOfDamping t p g * (scatteringOfDamping t p g)ᴴ = 1 := by
  let P := sqrtDamping p
  let Z := P * g * P
  let k : ℂ := 2 * Complex.I * (t : ℂ)
  have hP : Pᴴ = P := AndersonAC.SolS6.sqrtDamping_conjTranspose p
  have hP2 : P * P = Matrix.diagonal (fun i => (p i : ℂ)) :=
    AndersonAC.SolS6.sqrtDamping_sq p hp
  have hZ : Z - Zᴴ = k • (Z * Zᴴ) := by
    calc
      Z - Zᴴ = P * (g - gᴴ) * P := by
        simp only [Z, Matrix.conjTranspose_mul, hP, Matrix.mul_sub, Matrix.sub_mul]
        noncomm_ring
      _ = k • (P * (g * Matrix.diagonal (fun i => (p i : ℂ)) * gᴴ) * P) := by
        rw [hWard]
        simp only [k, Matrix.mul_smul, Matrix.smul_mul]
      _ = k • (Z * Zᴴ) := by
        rw [← hP2]
        congr 1
        simp only [Z, Matrix.conjTranspose_mul, hP]
        noncomm_ring
  have hk : star k = -k := by simp [k]
  have hPt : Pᵀ = P := by simp [P, sqrtDamping]
  have hgt : gᵀ = g := hs
  constructor
  · change (1 + k • Z)ᵀ = 1 + k • Z
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
      Z, Matrix.transpose_mul, hPt, hgt]
    noncomm_ring
  · change (1 + k • Z) * (1 + k • Z)ᴴ = 1
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hk]
    calc
      (1 + k • Z) * (1 + -k • Zᴴ) =
          1 + k • (Z - Zᴴ) - (k * k) • (Z * Zᴴ) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, neg_smul,
          Matrix.mul_neg, smul_add]
        abel
      _ = 1 := by rw [hZ, smul_smul]; abel

end AndersonAC.S6

namespace AndersonAC.SolS6
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_symmetric_hermitian (M : Matrix ι ι ℂ) (hM : Mᵀ = M)
    (hreal : ∀ i j, (M i j).im = 0) : Mᴴ = M := by
  ext i j
  change star (M j i) = M i j
  have hij : M j i = M i j := congrFun (congrFun hM i) j
  rw [hij]
  apply Complex.ext <;> simp [hreal]

theorem diagonal_imaginary_difference (r : ι → ℂ) :
    Matrix.diagonal r - (Matrix.diagonal r)ᴴ =
      (2 * Complex.I) • Matrix.diagonal (fun i => ((r i).im : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  · simp [Matrix.diagonal, Matrix.conjTranspose_apply, hij, Ne.symm hij]

theorem scattering_from_inverse (M G : Matrix ι ι ℂ) (t : ℝ) (r : ι → ℂ)
    (hM : Mᵀ = M) (hreal : ∀ i j, (M i j).im = 0) (hp : ∀ i, 0 ≤ (r i).im)
    (hInv : AndersonAC.Blueprint.twoSidedInverse
      (M - (t : ℂ) • Matrix.diagonal r) G) :
    (AndersonAC.S6.scattering t r G).IsSymm ∧
      AndersonAC.S6.scattering t r G * (AndersonAC.S6.scattering t r G)ᴴ = 1 := by
  let A := M - (t : ℂ) • Matrix.diagonal r
  let D := Matrix.diagonal (fun i => ((r i).im : ℂ))
  have hMt : Aᵀ = A := by
    simp [A, Matrix.transpose_sub, Matrix.transpose_smul, hM]
  have hGs : G.IsSymm := inverse_transpose A G hMt hInv
  have hDiff : Aᴴ - A = (2 * Complex.I * (t : ℂ)) • D := by
    have hMh := real_symmetric_hermitian M hM hreal
    simp only [A, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      hMh, Complex.star_def, Complex.conj_ofReal]
    calc
      (M - (t : ℂ) • (Matrix.diagonal r)ᴴ) - (M - (t : ℂ) • Matrix.diagonal r) =
          (t : ℂ) • (Matrix.diagonal r - (Matrix.diagonal r)ᴴ) := by
        rw [smul_sub]
        abel
      _ = (2 * Complex.I * (t : ℂ)) • D := by
        rw [diagonal_imaginary_difference, smul_smul]
        congr 1
        ring
  have hWard : G - Gᴴ = (2 * Complex.I * (t : ℂ)) • (G * D * Gᴴ) := by
    have hstar : Aᴴ * Gᴴ = 1 := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
        congrArg (fun H => Hᴴ) hInv.2
    calc
      G - Gᴴ = G * (Aᴴ - A) * Gᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc G Aᴴ Gᴴ,
          hstar, Matrix.mul_one, hInv.2, Matrix.one_mul]
      _ = (2 * Complex.I * (t : ℂ)) • (G * D * Gᴴ) := by
        rw [hDiff]
        simp only [Matrix.mul_smul, Matrix.smul_mul]
  exact AndersonAC.S6.scattering_unitary t (AndersonAC.S6.imagDamping r) G hp hGs hWard

end AndersonAC.SolS6

#print axioms AndersonAC.S6.scattering_unitary
#print axioms AndersonAC.SolS6.scattering_from_inverse
