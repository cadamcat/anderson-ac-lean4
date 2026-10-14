import AndersonAC.L64.Vec

/-!
# Lemma 6.4: the damped resolvent, Ward identities and the scattering matrix

`06-clearing.tex` l.19–80: `g = (M - t diag r)⁻¹` with `M` real symmetric, `p = Im r > 0`,
`h = √t g`, and `S = 1 + 2it D_p^{1/2} g D_p^{1/2}` (eq. `clearing-scattering`), which is symmetric
and unitary by the Ward identity.
-/

open Matrix Finset ComplexConjugate Complex

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the damped matrix `M - t diag r`. -/
noncomputable def damped (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) : Matrix ι ι ℂ :=
  M.map (fun a : ℝ => (a : ℂ)) - (t : ℂ) • diagonal r

/-- `D_p^{1/2}` as a complex diagonal matrix. -/
noncomputable def sqrtDiag (p : ι → ℝ) : Matrix ι ι ℂ := diagonal fun i => ((√(p i) : ℝ) : ℂ)

/-- the scattering matrix `S = 1 + 2it D_p^{1/2} g D_p^{1/2}`. -/
noncomputable def scat (t : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1 + (2 * I * (t : ℂ)) • (sqrtDiag p * g * sqrtDiag p)

lemma scat_apply (t : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ) (i j : ι) :
    scat t p g i j = (if i = j then 1 else 0)
      + 2 * I * (t : ℂ) * ((√(p i) : ℝ) : ℂ) * ((√(p j) : ℝ) : ℂ) * g i j := by
  simp only [scat, sqrtDiag, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    diagonal_mul, mul_diagonal, smul_eq_mul]
  ring

lemma scat_apply_ne (t : ℝ) (p : ι → ℝ) (g : Matrix ι ι ℂ) {i j : ι} (h : i ≠ j) :
    scat t p g i j = 2 * I * (t : ℂ) * ((√(p i) : ℝ) : ℂ) * ((√(p j) : ℝ) : ℂ) * g i j := by
  rw [scat_apply, if_neg h, zero_add]

section Damped

variable (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ)

lemma damped_transpose (hM : M.IsSymm) : (damped M t r)ᵀ = damped M t r := by
  unfold damped
  rw [transpose_sub, transpose_smul, diagonal_transpose, ← transpose_map, hM.eq]

lemma damped_conjTranspose (hM : M.IsSymm) :
    (damped M t r)ᴴ = damped M t (fun i => conj (r i)) := by
  unfold damped
  ext i j
  have hij : M j i = M i j := by
    have := congrFun (congrFun hM.eq i) j
    simpa [transpose_apply] using this
  simp only [conjTranspose_apply, Matrix.sub_apply, map_apply, Matrix.smul_apply,
    diagonal_apply, smul_eq_mul, star_sub, star_mul', Complex.star_def, conj_ofReal, hij]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `(M - t diag r)ᴴ - (M - t diag r) = 2it diag(Im r)`. -/
lemma damped_conjTranspose_sub (hM : M.IsSymm) :
    (damped M t r)ᴴ - damped M t r
      = (2 * I * (t : ℂ)) • diagonal (fun i => (((r i).im : ℝ) : ℂ)) := by
  rw [damped_conjTranspose M t r hM]
  unfold damped
  ext i j
  simp only [Matrix.sub_apply, map_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp only [ite_true]
    apply Complex.ext <;> simp <;> ring
  · simp [h]

/-- The damped matrix is invertible when `t > 0` and `Im r > 0`. -/
lemma isUnit_det_damped (hM : M.IsSymm) (ht : 0 < t) (hp : ∀ i, 0 < (r i).im) :
    IsUnit (damped M t r).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨z, hz, hz0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e1 : star z ⬝ᵥ (((damped M t r)ᴴ - damped M t r) *ᵥ z) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hz0, dotProduct_zero, sub_zero, dotProduct_mulVec,
      ← star_mulVec, hz0, star_zero, zero_dotProduct]
  rw [damped_conjTranspose_sub M t r hM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at e1
  have hk : (2 * I * (t : ℂ)) ≠ 0 := by
    simp [ht.ne', Complex.I_ne_zero]
  have e2 : ∑ i, ((r i).im * ‖z i‖ ^ 2 : ℝ) = 0 := by
    have := (mul_eq_zero.mp e1).resolve_left hk
    simp only [dotProduct, Pi.star_apply, Complex.star_def, mulVec_diagonal] at this
    have h' : ((∑ i, ((r i).im * ‖z i‖ ^ 2 : ℝ)) : ℂ) = 0 := by
      rw [← this]; push_cast
      refine sum_congr rfl fun i _ => ?_
      rw [show ((‖z i‖ : ℂ)) ^ 2 = conj (z i) * z i from ofReal_norm_sq_eq _]; ring
    exact_mod_cast h'
  apply hz
  ext i
  have hnn : ∀ j ∈ univ, 0 ≤ (r j).im * ‖z j‖ ^ 2 := fun j _ =>
    mul_nonneg (hp j).le (sq_nonneg _)
  have := (sum_eq_zero_iff_of_nonneg hnn).mp e2 i (mem_univ i)
  have : ‖z i‖ ^ 2 = 0 := (mul_eq_zero.mp this).resolve_left (hp i).ne'
  simpa using this

end Damped

section Ward

variable {M : Matrix ι ι ℝ} {t : ℝ} {r : ι → ℂ}

lemma ward_left_of (Dm : Matrix ι ι ℂ) (hD : IsUnit Dm.det) :
    Dm⁻¹ - (Dm⁻¹)ᴴ = (Dm⁻¹)ᴴ * (Dmᴴ - Dm) * Dm⁻¹ := by
  have h1 : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
  have h2 : (Dm⁻¹)ᴴ * Dmᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, h2, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

lemma ward_right_of (Dm : Matrix ι ι ℂ) (hD : IsUnit Dm.det) :
    Dm⁻¹ - (Dm⁻¹)ᴴ = Dm⁻¹ * (Dmᴴ - Dm) * (Dm⁻¹)ᴴ := by
  have h1 : Dm⁻¹ * Dm = 1 := Matrix.nonsing_inv_mul _ hD
  have h2 : Dmᴴ * (Dm⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, h1, Matrix.one_mul]

/-- The Ward identity `g - gᴴ = 2it gᴴ D_p g`. -/
lemma ward_left (hM : M.IsSymm) (hD : IsUnit (damped M t r).det) :
    (damped M t r)⁻¹ - ((damped M t r)⁻¹)ᴴ
      = (2 * I * (t : ℂ)) • (((damped M t r)⁻¹)ᴴ
          * diagonal (fun i => (((r i).im : ℝ) : ℂ)) * (damped M t r)⁻¹) := by
  rw [ward_left_of _ hD, damped_conjTranspose_sub M t r hM, Matrix.mul_smul, Matrix.smul_mul]

/-- The Ward identity `g - gᴴ = 2it g D_p gᴴ`. -/
lemma ward_right (hM : M.IsSymm) (hD : IsUnit (damped M t r).det) :
    (damped M t r)⁻¹ - ((damped M t r)⁻¹)ᴴ
      = (2 * I * (t : ℂ)) • ((damped M t r)⁻¹
          * diagonal (fun i => (((r i).im : ℝ) : ℂ)) * ((damped M t r)⁻¹)ᴴ) := by
  rw [ward_right_of _ hD, damped_conjTranspose_sub M t r hM, Matrix.mul_smul, Matrix.smul_mul]

/-- The resolvent is symmetric. -/
lemma resolvent_transpose (hM : M.IsSymm) : ((damped M t r)⁻¹)ᵀ = (damped M t r)⁻¹ := by
  rw [transpose_nonsing_inv, damped_transpose M t r hM]

lemma resolvent_symm (hM : M.IsSymm) (i j : ι) :
    (damped M t r)⁻¹ i j = (damped M t r)⁻¹ j i := by
  conv_rhs => rw [← resolvent_transpose hM]
  rfl

/-- The diagonal Ward identity `Im g_xx = t ∑_j p_j |g_xj|²` (eq. `clearing-row-bound`). -/
lemma im_diag_ward (hM : M.IsSymm) (hD : IsUnit (damped M t r).det) (x : ι) :
    ((damped M t r)⁻¹ x x).im = t * ∑ j, (r j).im * ‖(damped M t r)⁻¹ x j‖ ^ 2 := by
  have h := congrFun (congrFun (ward_right hM hD) x) x
  simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    mul_apply, diagonal_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  have hs : ∑ j, (damped M t r)⁻¹ x j * (((r j).im : ℝ) : ℂ) * star ((damped M t r)⁻¹ x j)
      = ((∑ j, (r j).im * ‖(damped M t r)⁻¹ x j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, show ((‖(damped M t r)⁻¹ x j‖ : ℂ)) ^ 2
      = conj ((damped M t r)⁻¹ x j) * (damped M t r)⁻¹ x j from ofReal_norm_sq_eq _]
    ring
  rw [hs] at h
  have h2 := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
    Complex.im_ofNat] at h2
  linarith

end Ward

section Scat

variable {t : ℝ} {p : ι → ℝ}

lemma sqrtDiag_conjTranspose : (sqrtDiag p)ᴴ = sqrtDiag p := by
  simp [sqrtDiag, diagonal_conjTranspose]

lemma sqrtDiag_mul_self (hp : ∀ i, 0 ≤ p i) :
    sqrtDiag p * sqrtDiag p = diagonal fun i => ((p i : ℝ) : ℂ) := by
  rw [sqrtDiag, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← ofReal_mul, Real.mul_self_sqrt (hp i)]

/-- The scattering matrix of a resolvent satisfying the Ward identity is unitary. -/
lemma scat_unitary (g : Matrix ι ι ℂ) (hp : ∀ i, 0 ≤ p i)
    (hW : g - gᴴ = (2 * I * (t : ℂ)) • (gᴴ * diagonal (fun i => ((p i : ℝ) : ℂ)) * g)) :
    (scat t p g)ᴴ * scat t p g = 1 := by
  set P := sqrtDiag p
  set Z := P * g * P
  set k : ℂ := 2 * I * (t : ℂ)
  have hk : star k = -k := by simp [k, Complex.ext_iff]
  have hZ : Z - Zᴴ = k • (Zᴴ * Z) := by
    have e1 : Zᴴ = P * gᴴ * P := by
      simp only [Z, conjTranspose_mul, sqrtDiag_conjTranspose, P, Matrix.mul_assoc]
    rw [e1]
    have : P * g * P - P * gᴴ * P = P * (g - gᴴ) * P := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [this, hW, ← sqrtDiag_mul_self hp]
    simp only [Z, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rfl
  have hkk : star k * k = -(k * k) := by rw [hk]; ring
  unfold scat
  rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul]
  change (1 + star k • Zᴴ) * (1 + k • Z) = 1
  have expand : (1 + star k • Zᴴ) * (1 + k • Z)
      = 1 + (k • Z + star k • Zᴴ + (star k * k) • (Zᴴ * Z)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    abel
  rw [expand, hkk, hk]
  have : k • Z + -k • Zᴴ + -(k * k) • (Zᴴ * Z) = k • (Z - Zᴴ) - (k * k) • (Zᴴ * Z) := by
    rw [smul_sub, neg_smul, neg_smul]; abel
  rw [this, hZ, smul_smul, sub_self, add_zero]

lemma scat_transpose (g : Matrix ι ι ℂ) (hg : gᵀ = g) : (scat t p g)ᵀ = scat t p g := by
  ext i j
  rw [transpose_apply, scat_apply, scat_apply]
  have : g j i = g i j := by simpa [transpose_apply] using congrFun (congrFun hg i) j
  rw [this]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg (Ne.symm h), if_neg h]; ring

end Scat

end AndersonAC.L64
