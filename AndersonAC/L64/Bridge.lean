import AndersonAC.L64.NormalizedDrift

/-!
# Lemma 6.4: from ridge leverages of a cross block to the normalized heat

For a matrix `S` (the scattering matrix), a core `B` and exterior `R = Bᶜ`, the cross block is
`𝒞 = S_{RB}`, `Γ = 𝒞*𝒞`, `G_τ = Γ + τ` and the ridge leverages are
`m_i = 𝒞_i G_τ⁻¹ 𝒞_i*` (eq. `clearing-ridge`). We choose any `L` with `L Lᴴ = G_τ⁻¹`
(the paper uses `L = G_τ^{-1/2}`) and normalize `u_i = 𝒞_i L`. If the post-heat cross rows are
`𝒞'_i = 𝒞_i + c v_i 𝒞_x` (eq. `clearing-cross-update`), the post-heat ridge leverages at the
same `τ` are exactly the `lev'` of the normalized heat (eqs. `clearing-gram-congruence`,
`clearing-leverage-update`).
-/

open Matrix Finset ComplexConjugate
open scoped ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the cross-block row `𝒞_i = S_{iB}`. -/
def crossRow (S : Matrix ι ι ℂ) (B : Finset ι) (i : ι) : B → ℂ := fun b => S i b

/-- `Γ = 𝒞*𝒞` over the exterior rows `R`. -/
noncomputable def gram (S : Matrix ι ι ℂ) (B R : Finset ι) : Matrix B B ℂ :=
  ∑ i ∈ R, vecMulVec (star (crossRow S B i)) (crossRow S B i)

/-- the ridge leverage `m_i = 𝒞_i (𝒞*𝒞 + τ)⁻¹ 𝒞_i*`. -/
noncomputable def ridgeLev (S : Matrix ι ι ℂ) (B R : Finset ι) (τ : ℝ) (i : ι) : ℝ :=
  (crossRow S B i ⬝ᵥ ((gram S B R + (τ : ℂ) • 1)⁻¹ *ᵥ star (crossRow S B i))).re

section Generic

variable {B : Type*} [Fintype B] [DecidableEq B]

lemma vecMulVec_star_vecMul (y : B → ℂ) (L : Matrix B B ℂ) :
    vecMulVec (star (y ᵥ* L)) (y ᵥ* L) = Lᴴ * vecMulVec (star y) y * L := by
  ext a b
  simp only [vecMulVec_apply, mul_apply, vecMul, dotProduct, conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', sum_mul, mul_sum]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring

lemma nsq_vecMul (y : B → ℂ) (L : Matrix B B ℂ) :
    ((nsq (y ᵥ* L) : ℝ) : ℂ) = y ⬝ᵥ ((L * Lᴴ) *ᵥ star y) := by
  rw [← dotProduct_star_self_eq, star_vecMul, ← mulVec_mulVec, ← dotProduct_mulVec]

lemma dotProduct_vecMul' (y z : B → ℂ) (L : Matrix B B ℂ) :
    (y ᵥ* L) ⬝ᵥ z = y ⬝ᵥ (L *ᵥ z) := (dotProduct_mulVec y L z).symm

/-- `∑_i |𝒞_i y|² = Re (y* Γ y)`. -/
lemma sum_norm_sq_eq {ι' : Type*} (R : Finset ι') (C : ι' → B → ℂ) (y : B → ℂ) :
    ((∑ i ∈ R, ‖C i ⬝ᵥ y‖ ^ 2 : ℝ) : ℂ)
      = star y ⬝ᵥ ((∑ i ∈ R, vecMulVec (star (C i)) (C i)) *ᵥ y) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [vecMulVec_mulVec', dotProduct_smul, smul_eq_mul, star_dotProduct_star, Complex.star_def,
    mul_conj_self_eq]
  push_cast; ring

end Generic

section Bridge

variable (S : Matrix ι ι ℂ) (B : Finset ι) (τ : ℝ)

lemma gram_posSemidef (R : Finset ι) : (gram S B R).PosSemidef :=
  posSemidef_sum _ fun _ _ => posSemidef_vecMulVec_star_self _

lemma ridgeG_posDef (R : Finset ι) (hτ : 0 < τ) : (gram S B R + (τ : ℂ) • 1).PosDef := by
  rw [add_comm]
  refine PosDef.add_posSemidef ?_ (gram_posSemidef S B R)
  exact PosDef.one.smul (Complex.zero_lt_real.mpr hτ)

/-- A factor `L` with `L Lᴴ = G_τ⁻¹`. -/
lemma exists_normalizer (R : Finset ι) (hτ : 0 < τ) :
    ∃ L : Matrix B B ℂ, L * Lᴴ = (gram S B R + (τ : ℂ) • 1)⁻¹ := by
  have h := (ridgeG_posDef S B τ R hτ).inv.posSemidef
  obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  exact ⟨yᴴ, by rw [conjTranspose_conjTranspose, hy]; rfl⟩

variable {S B τ}

/-- The normalized heat attached to a factor `L`, the pivot `x` and the vector `v`. -/
def nheat (S : Matrix ι ι ℂ) (L : Matrix B B ℂ) (x : ι) (v : ι → ℂ) : NHeat ι B where
  S := Bᶜ.erase x
  u := fun i => crossRow S B i ᵥ* L
  ux := crossRow S B x ᵥ* L
  v := v

variable {L : Matrix B B ℂ} {x : ι} (v : ι → ℂ)

section
variable (hτ : 0 < τ) (hL : L * Lᴴ = (gram S B Bᶜ + (τ : ℂ) • 1)⁻¹)
include hτ hL

lemma normalizer_unit : Lᴴ * (gram S B Bᶜ + (τ : ℂ) • 1) * L = 1 := by
  have hG := (ridgeG_posDef S B τ Bᶜ hτ).isUnit
  have h1 : (gram S B Bᶜ + (τ : ℂ) • 1) * (L * Lᴴ) = 1 := by
    rw [hL]; exact Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG)
  rw [← Matrix.mul_assoc] at h1
  rw [Matrix.mul_assoc]
  exact mul_eq_one_comm.mp h1

lemma isUnit_det_normalizer : IsUnit L.det :=
  Matrix.isUnit_det_of_left_inverse (B := Lᴴ * (gram S B Bᶜ + (τ : ℂ) • 1))
    (normalizer_unit hτ hL)

lemma nheat_lev (i : ι) : (nheat S L x v).lev i = ridgeLev S B Bᶜ τ i := by
  have := nsq_vecMul (crossRow S B i) L
  rw [hL] at this
  unfold NHeat.lev ridgeLev
  simp only [nheat]
  rw [← this, Complex.ofReal_re]

lemma nheat_m : (nheat S L x v).m = ridgeLev S B Bᶜ τ x := by
  have := nsq_vecMul (crossRow S B x) L
  rw [hL] at this
  unfold NHeat.m ridgeLev
  simp only [nheat]
  rw [← this, Complex.ofReal_re]

lemma nheat_A (hx : x ∉ B) : (nheat S L x v).A = ∑ i ∈ Bᶜ, ridgeLev S B Bᶜ τ i := by
  have hxR : x ∈ (Bᶜ : Finset ι) := mem_compl.mpr hx
  unfold NHeat.A
  rw [nheat_m v hτ hL, ← sum_erase_add _ _ hxR]
  congr 1
  exact sum_congr rfl fun i _ => nheat_lev v hτ hL i

lemma nheat_P (hx : x ∉ B) : (nheat S L x v).P = ∑ i ∈ Bᶜ, ridgeLev S B Bᶜ τ i ^ 2 := by
  have hxR : x ∈ (Bᶜ : Finset ι) := mem_compl.mpr hx
  unfold NHeat.P
  rw [nheat_m v hτ hL, ← sum_erase_add _ _ hxR]
  congr 1
  exact sum_congr rfl fun i _ => by rw [nheat_lev v hτ hL i]

lemma nheat_Q (hx : x ∉ B) : (nheat S L x v).Q = Lᴴ * gram S B Bᶜ * L := by
  have hxR : x ∈ (Bᶜ : Finset ι) := mem_compl.mpr hx
  unfold NHeat.Q gram
  simp only [nheat]
  rw [Matrix.mul_sum, Matrix.sum_mul, ← sum_erase_add _ _ hxR]
  simp only [vecMulVec_star_vecMul]

/-- `‖z‖² = ∑_{i ∈ R} |𝒞_i L z|² + τ ‖L z‖²`, i.e. `Lᴴ G_τ L = 1`. -/
lemma nsq_eq_bessel_add (z : B → ℂ) :
    nsq z = ∑ i ∈ Bᶜ, ‖crossRow S B i ⬝ᵥ (L *ᵥ z)‖ ^ 2 + τ * nsq (L *ᵥ z) := by
  have e2 := sum_norm_sq_eq Bᶜ (crossRow S B) (L *ᵥ z)
  have e3 : star (L *ᵥ z) ⬝ᵥ ((gram S B Bᶜ + (τ : ℂ) • 1) *ᵥ (L *ᵥ z)) = ((nsq z : ℝ) : ℂ) := by
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      normalizer_unit hτ hL, Matrix.one_mulVec, star_dotProduct_self_eq]
  have e4 : star (L *ᵥ z) ⬝ᵥ ((gram S B Bᶜ + (τ : ℂ) • 1) *ᵥ (L *ᵥ z))
      = star (L *ᵥ z) ⬝ᵥ (gram S B Bᶜ *ᵥ (L *ᵥ z)) + (τ : ℂ) * ((nsq (L *ᵥ z) : ℝ) : ℂ) := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      star_dotProduct_self_eq, smul_eq_mul]
  rw [e3, gram, ← e2] at e4
  exact_mod_cast e4

/-- `τ ‖L z‖² ≤ ‖z‖²`. -/
lemma tau_nsq_mulVec_le (z : B → ℂ) : τ * nsq (L *ᵥ z) ≤ nsq z := by
  rw [nsq_eq_bessel_add hτ hL z]
  have : 0 ≤ ∑ i ∈ Bᶜ, ‖crossRow S B i ⬝ᵥ (L *ᵥ z)‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- `τ ‖Lᴴ z‖² ≤ ‖z‖²`, i.e. `τ G_τ⁻¹ ≤ 1`. -/
lemma tau_nsq_conjTranspose_mulVec_le (z : B → ℂ) : τ * nsq (Lᴴ *ᵥ z) ≤ nsq z := by
  set w := Lᴴ *ᵥ z
  have e : ((nsq w : ℝ) : ℂ) = star z ⬝ᵥ (L *ᵥ w) := by
    rw [← star_dotProduct_self_eq, show w = Lᴴ *ᵥ z from rfl, star_mulVec,
      conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have h1 : nsq w ≤ √(nsq z) * √(nsq (L *ᵥ w)) := by
    have := norm_dotProduct_le (star z) (L *ᵥ w)
    rw [← e, nsq_star, Complex.norm_real, Real.norm_of_nonneg (nsq_nonneg _)] at this
    exact this
  have h2 := tau_nsq_mulVec_le hτ hL w
  have hw := nsq_nonneg w
  have hz := nsq_nonneg z
  have hLw := nsq_nonneg (L *ᵥ w)
  -- τ ‖w‖⁴ ≤ ‖z‖² τ ‖Lw‖² ≤ ‖z‖² ‖w‖²
  have h3 : τ * nsq w ^ 2 ≤ nsq z * nsq w := by
    have : nsq w ^ 2 ≤ nsq z * nsq (L *ᵥ w) := by
      calc nsq w ^ 2 ≤ (√(nsq z) * √(nsq (L *ᵥ w))) ^ 2 := pow_le_pow_left₀ hw h1 2
        _ = nsq z * nsq (L *ᵥ w) := by
          rw [mul_pow, Real.sq_sqrt hz, Real.sq_sqrt hLw]
    calc τ * nsq w ^ 2 ≤ τ * (nsq z * nsq (L *ᵥ w)) := mul_le_mul_of_nonneg_left this hτ.le
      _ = nsq z * (τ * nsq (L *ᵥ w)) := by ring
      _ ≤ nsq z * nsq w := mul_le_mul_of_nonneg_left h2 hz
  rcases hw.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]; simpa using hz

/-- `‖Lᴴ y‖² = Re (y* G_τ⁻¹ y)`. -/
lemma nsq_conjTranspose_mulVec (y : B → ℂ) :
    ((nsq (Lᴴ *ᵥ y) : ℝ) : ℂ) = star y ⬝ᵥ ((gram S B Bᶜ + (τ : ℂ) • 1)⁻¹ *ᵥ y) := by
  rw [← star_dotProduct_self_eq, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec,
    Matrix.mulVec_mulVec, hL]

/-- The Bessel inequality for the normalized rows (`0 ≤ V_τ = τ Lᴴ L`). -/
lemma nheat_bessel (hx : x ∉ B) : (nheat S L x v).Bessel := by
  intro z
  have hxR : x ∈ (Bᶜ : Finset ι) := mem_compl.mpr hx
  have e1 : ∑ i ∈ (nheat S L x v).S, ‖(nheat S L x v).u i ⬝ᵥ z‖ ^ 2
      + ‖(nheat S L x v).ux ⬝ᵥ z‖ ^ 2 = ∑ i ∈ Bᶜ, ‖crossRow S B i ⬝ᵥ (L *ᵥ z)‖ ^ 2 := by
    simp only [nheat, dotProduct_vecMul']
    rw [← sum_erase_add _ _ hxR]
  rw [e1]
  have := nsq_eq_bessel_add hτ hL z
  have := mul_nonneg hτ.le (nsq_nonneg (L *ᵥ z))
  linarith

variable (S' : Matrix ι ι ℂ) (c : ℂ)
  (hC' : ∀ i ∈ Bᶜ.erase x, crossRow S' B i = crossRow S B i + (c * v i) • crossRow S B x)
include hC'

lemma nheat_w {i : ι} (hi : i ∈ Bᶜ.erase x) : (nheat S L x v).w c i = crossRow S' B i ᵥ* L := by
  rw [hC' i hi, add_vecMul, smul_vecMul]; rfl

/-- The exact congruence `Γ' + τ = G_τ^{1/2}(1 + D_*)G_τ^{1/2}` in the form `1 + D = Lᴴ G'_τ L`
(eq. `clearing-gram-congruence`). -/
lemma nheat_one_add_D (hx : x ∉ B) :
    1 + (nheat S L x v).D c = Lᴴ * (gram S' B (Bᶜ.erase x) + (τ : ℂ) • 1) * L := by
  have h1 := normalizer_unit hτ hL
  have hW : ∑ i ∈ (nheat S L x v).S, vecMulVec (star ((nheat S L x v).w c i)) ((nheat S L x v).w c i)
      = Lᴴ * gram S' B (Bᶜ.erase x) * L := by
    unfold gram
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [nheat_w v hτ hL S' c hC' hi, vecMulVec_star_vecMul]
  unfold NHeat.D
  rw [hW, nheat_Q v hτ hL hx]
  conv_lhs => rw [← h1]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

lemma nheat_lev' (hx : x ∉ B) {i : ι} (hi : i ∈ Bᶜ.erase x) :
    (nheat S L x v).lev' c i = ridgeLev S' B (Bᶜ.erase x) τ i := by
  have hLu := isUnit_det_normalizer hτ hL
  have hLHu : IsUnit Lᴴ.det := by rw [det_conjTranspose]; exact hLu.star
  have e1 : (1 + (nheat S L x v).D c)⁻¹
      = L⁻¹ * (gram S' B (Bᶜ.erase x) + (τ : ℂ) • 1)⁻¹ * Lᴴ⁻¹ := by
    rw [nheat_one_add_D v hτ hL S' c hC' hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.mul_assoc]
  unfold NHeat.lev' ridgeLev
  rw [e1, nheat_w v hτ hL S' c hC' hi, star_vecMul, dotProduct_vecMul', Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  congr 3
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hLHu, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hLu, Matrix.one_mul]

lemma nheat_A' (hx : x ∉ B) :
    (nheat S L x v).A' c = ∑ i ∈ Bᶜ.erase x, ridgeLev S' B (Bᶜ.erase x) τ i :=
  sum_congr rfl fun i hi => nheat_lev' v hτ hL S' c hC' hx hi

lemma nheat_P' (hx : x ∉ B) :
    (nheat S L x v).P' c = ∑ i ∈ Bᶜ.erase x, ridgeLev S' B (Bᶜ.erase x) τ i ^ 2 :=
  sum_congr rfl fun _ hi => by rw [nheat_lev' v hτ hL S' c hC' hx hi]

end

end Bridge

end AndersonAC.L64
