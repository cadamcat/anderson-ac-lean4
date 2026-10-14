import AndersonAC.L64.Vec

/-!
# Lemma 6.4: the normalized heat (abstract layer)

This file isolates the linear algebra of the proof of Lemma 6.4 (`06-clearing.tex`, l.425–640)
after the normalization `U = 𝒞 G_τ^{-1/2}`. Rows of `U` are `u i` for surviving exterior indices
`i ∈ S` (`S = R'` in the paper) and `ux` for the pivot `x`. The heat replaces the surviving rows by
`w_i = u_i + c v_i u_x` (eq. `clearing-cross-update`), the Gram increment is `D = W*W - Q`
(eq. `clearing-gram-increment`), and the new leverages are `m'_i = w_i (1 + D)⁻¹ w_i*`
(eq. `clearing-leverage-update`).

The only structural hypothesis on the rows is the Bessel inequality `Q ≤ 1`
(`0 ≤ V_τ = 1 - Q`, eq. `clearing-ridge-defect`).
-/

open Matrix Finset ComplexConjugate

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

/-- Normalized data of one heat. -/
structure NHeat (ι B : Type*) where
  /-- surviving exterior indices `R' = R ∖ {x}` -/
  S : Finset ι
  /-- normalized rows `u_i` of `U = 𝒞 G_τ^{-1/2}` -/
  u : ι → B → ℂ
  /-- normalized pivot row `u_x` -/
  ux : B → ℂ
  /-- the vector `v_i = h_{ix} √(p_i/p_x)` -/
  v : ι → ℂ

namespace NHeat

variable {ι B : Type*} [Fintype B] [DecidableEq B] (H : NHeat ι B)

/-- `m = m_x = ‖u_x‖²`. -/
noncomputable def m : ℝ := nsq H.ux
/-- old leverages `m_i = ‖u_i‖²`. -/
noncomputable def lev (i : ι) : ℝ := nsq (H.u i)
/-- `Q = U*U`. -/
noncomputable def Q : Matrix B B ℂ :=
  ∑ i ∈ H.S, vecMulVec (star (H.u i)) (H.u i) + vecMulVec (star H.ux) H.ux
/-- `b_x = U_{R'}* v`. -/
noncomputable def b : B → ℂ := ∑ i ∈ H.S, H.v i • star (H.u i)
/-- `‖v‖²`. -/
noncomputable def vn : ℝ := ∑ i ∈ H.S, ‖H.v i‖ ^ 2
/-- new normalized rows `w_i = u_i + c v_i u_x`. -/
noncomputable def w (c : ℂ) (i : ι) : B → ℂ := H.u i + (c * H.v i) • H.ux
/-- the Gram increment `D_* = W*W - Q`. -/
noncomputable def D (c : ℂ) : Matrix B B ℂ :=
  ∑ i ∈ H.S, vecMulVec (star (H.w c i)) (H.w c i) - H.Q
/-- new leverages `m'_i = w_i (1 + D_*)⁻¹ w_i*`. -/
noncomputable def lev' (c : ℂ) (i : ι) : ℝ :=
  (H.w c i ⬝ᵥ ((1 + H.D c)⁻¹ *ᵥ star (H.w c i))).re
/-- `𝒜 = ∑_{i ∈ R} m_i`. -/
noncomputable def A : ℝ := ∑ i ∈ H.S, H.lev i + H.m
/-- `𝒫 = ∑_{i ∈ R} m_i²`. -/
noncomputable def P : ℝ := ∑ i ∈ H.S, H.lev i ^ 2 + H.m ^ 2
/-- `𝒜' = ∑_{i ∈ R'} m'_i`. -/
noncomputable def A' (c : ℂ) : ℝ := ∑ i ∈ H.S, H.lev' c i
/-- `𝒫' = ∑_{i ∈ R'} m'_i²`. -/
noncomputable def P' (c : ℂ) : ℝ := ∑ i ∈ H.S, H.lev' c i ^ 2

/-- The Bessel inequality `Q ≤ 1`, i.e. `‖U z‖² ≤ ‖z‖²`. -/
def Bessel : Prop := ∀ z : B → ℂ, ∑ i ∈ H.S, ‖H.u i ⬝ᵥ z‖ ^ 2 + ‖H.ux ⬝ᵥ z‖ ^ 2 ≤ nsq z

lemma D_apply (c : ℂ) (a a' : B) :
    H.D c a a' = ∑ i ∈ H.S, (conj (H.w c i a) * H.w c i a' - conj (H.u i a) * H.u i a')
      - conj (H.ux a) * H.ux a' := by
  simp only [D, Q, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply,
    Pi.star_apply, Complex.star_def, sum_sub_distrib]
  ring

/-- The Gram increment, eq. `clearing-gram-increment`:
`D_* = (|c|²‖v‖² - 1) u_x* u_x + c b_x u_x + c̄ u_x* b_x*`. -/
lemma D_eq (c : ℂ) :
    H.D c = (((‖c‖ ^ 2 * H.vn - 1 : ℝ)) : ℂ) • vecMulVec (star H.ux) H.ux
      + c • vecMulVec H.b H.ux + conj c • vecMulVec (star H.ux) (star H.b) := by
  ext a a'
  rw [D_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    Complex.star_def, smul_eq_mul, b, vn, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_mul, Complex.conj_conj]
  have key : ∀ T : Finset ι, ∑ i ∈ T, (conj (H.w c i a) * H.w c i a' - conj (H.u i a) * H.u i a')
      = (conj c * c * ∑ i ∈ T, conj (H.v i) * H.v i) * (conj (H.ux a) * H.ux a')
        + c * ((∑ i ∈ T, H.v i * conj (H.u i a)) * H.ux a')
        + conj c * (conj (H.ux a) * ∑ i ∈ T, conj (H.v i) * H.u i a') := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hj ih =>
      rw [sum_insert hj, sum_insert hj, sum_insert hj, sum_insert hj, ih]
      simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
      ring
  rw [key]
  push_cast
  simp only [ofReal_norm_sq_eq]
  ring

/-! ### Weighted Gram matrices -/

/-- weighted new Gram matrix `∑_i λ_i w_i* w_i`. -/
noncomputable def Gw (lam : ι → ℝ) (c : ℂ) : Matrix B B ℂ :=
  ∑ i ∈ H.S, ((lam i : ℝ) : ℂ) • vecMulVec (star (H.w c i)) (H.w c i)
/-- weighted old Gram matrix `∑_i λ_i u_i* u_i`. -/
noncomputable def G0 (lam : ι → ℝ) : Matrix B B ℂ :=
  ∑ i ∈ H.S, ((lam i : ℝ) : ℂ) • vecMulVec (star (H.u i)) (H.u i)
/-- `∑_i λ_i v_i u_i*`. -/
noncomputable def bw (lam : ι → ℝ) : B → ℂ := ∑ i ∈ H.S, ((lam i : ℂ) * H.v i) • star (H.u i)
/-- `∑_i λ_i |v_i|²`. -/
noncomputable def vw (lam : ι → ℝ) : ℝ := ∑ i ∈ H.S, lam i * ‖H.v i‖ ^ 2

lemma Gw_eq (lam : ι → ℝ) (c : ℂ) :
    H.Gw lam c = H.G0 lam + ((‖c‖ ^ 2 * H.vw lam : ℝ) : ℂ) • vecMulVec (star H.ux) H.ux
      + c • vecMulVec (H.bw lam) H.ux + conj c • vecMulVec (star H.ux) (star (H.bw lam)) := by
  ext a a'
  simp only [Gw, G0, bw, vw, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    vecMulVec_apply, Pi.star_apply, Complex.star_def, smul_eq_mul, Finset.sum_apply,
    Pi.smul_apply, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  have key : ∀ T : Finset ι, ∑ i ∈ T, (lam i : ℂ) * (conj (H.w c i a) * H.w c i a')
      = ∑ i ∈ T, (lam i : ℂ) * (conj (H.u i a) * H.u i a')
        + (conj c * c * ∑ i ∈ T, (lam i : ℂ) * (conj (H.v i) * H.v i))
          * (conj (H.ux a) * H.ux a')
        + c * ((∑ i ∈ T, (lam i : ℂ) * H.v i * conj (H.u i a)) * H.ux a')
        + conj c * (conj (H.ux a) * ∑ i ∈ T, (lam i : ℂ) * conj (H.v i) * H.u i a') := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hj ih =>
      simp only [sum_insert hj, ih]
      simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
      ring
  rw [key]
  push_cast
  simp only [ofReal_norm_sq_eq]

/-- `tr(D Y)` through the rank-three form of `D`. -/
lemma trace_D_mul (c : ℂ) (Y : Matrix B B ℂ) :
    trace (H.D c * Y) = (((‖c‖ ^ 2 * H.vn - 1 : ℝ)) : ℂ) * (H.ux ⬝ᵥ (Y *ᵥ star H.ux))
      + c * (H.ux ⬝ᵥ (Y *ᵥ H.b)) + conj c * (star H.b ⬝ᵥ (Y *ᵥ star H.ux)) := by
  rw [D_eq]
  simp only [Matrix.add_mul, Matrix.smul_mul, trace_add, trace_smul, trace_vecMulVec_mul,
    smul_eq_mul]

lemma trace_mul_Gw (c : ℂ) (Y : Matrix B B ℂ) (lam : ι → ℝ) :
    trace (Y * H.Gw lam c) = ∑ i ∈ H.S, (lam i : ℂ) * (H.w c i ⬝ᵥ (Y *ᵥ star (H.w c i))) := by
  simp only [Gw, Matrix.mul_sum, trace_sum, Matrix.mul_smul, trace_smul, trace_mul_vecMulVec,
    smul_eq_mul]

/-! ### Consequences of the Bessel inequality -/

namespace Bessel

variable {H}

lemma sum_le (hB : H.Bessel) (p : B → ℂ) :
    ∑ i ∈ H.S, ‖p ⬝ᵥ star (H.u i)‖ ^ 2 + ‖p ⬝ᵥ star H.ux‖ ^ 2 ≤ nsq p := by
  have := hB (star p)
  simp only [norm_dotProduct_star_comm p]
  rwa [nsq_star] at this

lemma sum_rows_le (hB : H.Bessel) (p : B → ℂ) :
    ∑ i ∈ H.S, ‖p ⬝ᵥ star (H.u i)‖ ^ 2 ≤ nsq p :=
  le_trans (le_add_of_nonneg_right (sq_nonneg _)) (hB.sum_le p)

lemma m_nonneg : 0 ≤ H.m := nsq_nonneg _

lemma lev_nonneg (i : ι) : 0 ≤ H.lev i := nsq_nonneg _

lemma m_le_one (hB : H.Bessel) : H.m ≤ 1 := by
  have h := hB.sum_le H.ux
  have h1 : ‖H.ux ⬝ᵥ star H.ux‖ = H.m := by
    rw [dotProduct_star_self_eq, Complex.norm_real, Real.norm_of_nonneg (nsq_nonneg _)]; rfl
  rw [h1] at h
  have h2 : 0 ≤ ∑ i ∈ H.S, ‖H.ux ⬝ᵥ star (H.u i)‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h3 : H.m ^ 2 ≤ H.m := by unfold m at *; linarith
  nlinarith [m_nonneg (H := H)]

/-- `∑_i |u_x u_i*|² ≤ m`. -/
lemma sum_pivot_le (hB : H.Bessel) : ∑ i ∈ H.S, ‖H.ux ⬝ᵥ star (H.u i)‖ ^ 2 ≤ H.m :=
  hB.sum_rows_le H.ux

/-- Dual Bessel inequality: `‖U* y‖² ≤ ‖y‖²`. -/
lemma dual (hB : H.Bessel) (y : ι → ℂ) :
    nsq (∑ i ∈ H.S, y i • star (H.u i)) ≤ ∑ i ∈ H.S, ‖y i‖ ^ 2 := by
  set β := ∑ i ∈ H.S, y i • star (H.u i) with hβ
  have e1 : ((nsq β : ℝ) : ℂ) = ∑ i ∈ H.S, y i * (star β ⬝ᵥ star (H.u i)) := by
    rw [← star_dotProduct_self_eq, hβ, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
  have e2 : nsq β ≤ √(∑ i ∈ H.S, ‖y i‖ ^ 2) * √(nsq β) := by
    have h := norm_sum_mul_le H.S y (fun i => star β ⬝ᵥ star (H.u i))
    rw [← e1, Complex.norm_real, Real.norm_of_nonneg (nsq_nonneg _)] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    have := hB.sum_rows_le (star β)
    rwa [nsq_star] at this
  set s := √(nsq β)
  have hs : s ^ 2 = nsq β := Real.sq_sqrt (nsq_nonneg _)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set r := √(∑ i ∈ H.S, ‖y i‖ ^ 2)
  have hr : r ^ 2 = ∑ i ∈ H.S, ‖y i‖ ^ 2 := Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have : s ≤ r := by nlinarith
  rw [← hs, ← hr]
  exact pow_le_pow_left₀ hs0 this 2

/-- `𝒜 = tr Q ≤ |B|`. -/
lemma A_le_card (hB : H.Bessel) : H.A ≤ Fintype.card B := by
  have h : ∀ b : B, ∑ i ∈ H.S, ‖H.u i b‖ ^ 2 + ‖H.ux b‖ ^ 2 ≤ 1 := by
    intro b
    have := hB (Pi.single b 1)
    rw [nsq_single] at this
    simpa [dotProduct_single] using this
  calc H.A = ∑ b : B, (∑ i ∈ H.S, ‖H.u i b‖ ^ 2 + ‖H.ux b‖ ^ 2) := by
        simp only [A, lev, m, nsq, sum_add_distrib]
        rw [sum_comm]
    _ ≤ ∑ _b : B, (1 : ℝ) := sum_le_sum fun b _ => h b
    _ = Fintype.card B := by simp

/-- `|p Q y| ≤ 2 ‖p‖ ‖y‖`. -/
lemma Q_form (hB : H.Bessel) (p y : B → ℂ) :
    ‖p ⬝ᵥ (H.Q *ᵥ y)‖ ≤ 2 * (√(nsq p) * √(nsq y)) := by
  have e : p ⬝ᵥ (H.Q *ᵥ y) = ∑ i ∈ H.S, (p ⬝ᵥ star (H.u i)) * (H.u i ⬝ᵥ y)
      + (p ⬝ᵥ star H.ux) * (H.ux ⬝ᵥ y) := by
    simp only [Q, Matrix.add_mulVec, Matrix.sum_mulVec, dotProduct_add, dotProduct_sum,
      dotProduct_vecMulVec_mulVec]
  rw [e]
  have h1 : ‖∑ i ∈ H.S, (p ⬝ᵥ star (H.u i)) * (H.u i ⬝ᵥ y)‖ ≤ √(nsq p) * √(nsq y) := by
    refine (norm_sum_mul_le _ _ _).trans
      (mul_le_mul (Real.sqrt_le_sqrt (hB.sum_rows_le p)) (Real.sqrt_le_sqrt ?_)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    exact le_trans (le_add_of_nonneg_right (sq_nonneg _)) (hB y)
  have h2 : ‖(p ⬝ᵥ star H.ux) * (H.ux ⬝ᵥ y)‖ ≤ √(nsq p) * √(nsq y) := by
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (Real.sqrt_nonneg _)
    · refine Real.le_sqrt_of_sq_le ?_
      exact le_trans (le_add_of_nonneg_left (sum_nonneg fun _ _ => sq_nonneg _)) (hB.sum_le p)
    · refine Real.le_sqrt_of_sq_le ?_
      exact le_trans (le_add_of_nonneg_left (sum_nonneg fun _ _ => sq_nonneg _)) (hB y)
  linarith [norm_add_le (∑ i ∈ H.S, (p ⬝ᵥ star (H.u i)) * (H.u i ⬝ᵥ y))
    ((p ⬝ᵥ star H.ux) * (H.ux ⬝ᵥ y))]

/-- `|p (1 - Q) y| ≤ 3 ‖p‖ ‖y‖`. -/
lemma V_form (hB : H.Bessel) (p y : B → ℂ) :
    ‖p ⬝ᵥ ((1 - H.Q) *ᵥ y)‖ ≤ 3 * (√(nsq p) * √(nsq y)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  refine (norm_sub_le _ _).trans ?_
  have := hB.Q_form p y
  have := norm_dotProduct_le p y
  linarith

/-- `|p X₀ y| ≤ m ‖p‖ ‖y‖` for `X₀ = ∑_i m_i u_i* u_i`, using maximality of `m`. -/
lemma G0_form (hB : H.Bessel) (hmax : ∀ i ∈ H.S, H.lev i ≤ H.m) (p y : B → ℂ) :
    ‖p ⬝ᵥ (H.G0 H.lev *ᵥ y)‖ ≤ H.m * (√(nsq p) * √(nsq y)) := by
  have e : p ⬝ᵥ (H.G0 H.lev *ᵥ y) = ∑ i ∈ H.S, ((H.lev i : ℂ) * (p ⬝ᵥ star (H.u i))) * (H.u i ⬝ᵥ y) := by
    simp only [G0, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
      dotProduct_vecMulVec_mulVec, smul_eq_mul]
    exact sum_congr rfl fun i _ => by ring
  rw [e]
  refine (norm_sum_mul_le _ _ _).trans ?_
  have h1 : ∑ i ∈ H.S, ‖(H.lev i : ℂ) * (p ⬝ᵥ star (H.u i))‖ ^ 2
      ≤ H.m ^ 2 * ∑ i ∈ H.S, ‖p ⬝ᵥ star (H.u i)‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (lev_nonneg i)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (lev_nonneg i) (hmax i hi) 2)
      (sq_nonneg _)
  have h2 : ∑ i ∈ H.S, ‖H.u i ⬝ᵥ y‖ ^ 2 ≤ nsq y :=
    le_trans (le_add_of_nonneg_right (sq_nonneg _)) (hB y)
  calc √(∑ i ∈ H.S, ‖(H.lev i : ℂ) * (p ⬝ᵥ star (H.u i))‖ ^ 2) * √(∑ i ∈ H.S, ‖H.u i ⬝ᵥ y‖ ^ 2)
      ≤ √(H.m ^ 2 * nsq p) * √(nsq y) := by
        refine mul_le_mul (Real.sqrt_le_sqrt (h1.trans ?_)) (Real.sqrt_le_sqrt h2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (hB.sum_rows_le p) (sq_nonneg _)
    _ = H.m * (√(nsq p) * √(nsq y)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq m_nonneg, mul_assoc]

end Bessel

/-! ### Pathwise control of `(1 + D)⁻¹` -/

lemma D_herm (c : ℂ) : (H.D c)ᴴ = H.D c := by
  ext a a'
  rw [conjTranspose_apply, D_apply, D_apply]
  simp only [star_sub, star_sum, star_mul', Complex.star_def, Complex.conj_conj]
  congr 1
  · exact sum_congr rfl fun i _ => by ring
  · ring

/-- nonsingularity of `1 + D` when `‖D‖_F² ≤ 1/4`. -/
lemma isUnit_det_one_add (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) : IsUnit (1 + H.D c).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨z, hz, hz0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e : z = -(H.D c *ᵥ z) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hz0
    exact eq_neg_of_add_eq_zero_left hz0
  have h1 : nsq z ≤ fro (H.D c) * nsq z := by
    conv_lhs => rw [e, nsq_neg]
    exact nsq_mulVec_le _ _
  have h2 : nsq z ≤ 0 := by nlinarith [nsq_nonneg z, fro_nonneg (H.D c)]
  apply hz
  ext b
  have := (nsq_le_of_sum z b).trans h2
  have : ‖z b‖ = 0 := by nlinarith [norm_nonneg (z b)]
  simpa using this

/-- the resolvent `Z = (1 + D)⁻¹`. -/
noncomputable def Z (c : ℂ) : Matrix B B ℂ := (1 + H.D c)⁻¹

lemma one_add_mul_Z (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) : (1 + H.D c) * H.Z c = 1 :=
  Matrix.mul_nonsing_inv _ (H.isUnit_det_one_add c hF)

lemma Z_mul_one_add (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) : H.Z c * (1 + H.D c) = 1 :=
  Matrix.nonsing_inv_mul _ (H.isUnit_det_one_add c hF)

lemma Z_mul_D (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) : H.Z c * H.D c = 1 - H.Z c := by
  have := H.Z_mul_one_add c hF
  rw [Matrix.mul_add, Matrix.mul_one] at this
  rw [← this]; abel

lemma D_mul_Z (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) : H.D c * H.Z c = 1 - H.Z c := by
  have := H.one_add_mul_Z c hF
  rw [Matrix.add_mul, Matrix.one_mul] at this
  rw [← this]; abel

/-- `(1 + D)⁻¹ = 1 - D + D (1 + D)⁻¹ D`. -/
lemma Z_expand (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) :
    H.Z c = 1 - H.D c + H.D c * H.Z c * H.D c := by
  rw [Matrix.mul_assoc, H.Z_mul_D c hF, Matrix.mul_sub, Matrix.mul_one, H.D_mul_Z c hF]
  abel

/-- `‖(1 + D)⁻¹ q‖² ≤ 4 ‖q‖²`. -/
lemma nsq_Z_mulVec_le (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) (q : B → ℂ) :
    nsq (H.Z c *ᵥ q) ≤ 4 * nsq q := by
  set y := H.Z c *ᵥ q
  have e : y = q + -(H.D c *ᵥ y) := by
    have : (1 + H.D c) *ᵥ y = q := by
      rw [Matrix.mulVec_mulVec, H.one_add_mul_Z c hF, Matrix.one_mulVec]
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at this
    rw [← this]; abel
  have h1 : nsq y ≤ 2 * nsq q + 2 * nsq (H.D c *ᵥ y) := by
    conv_lhs => rw [e]
    have := nsq_add_le q (-(H.D c *ᵥ y))
    rwa [nsq_neg] at this
  have h2 : nsq (H.D c *ᵥ y) ≤ fro (H.D c) * nsq y := nsq_mulVec_le _ _
  nlinarith [nsq_nonneg y, fro_nonneg (H.D c)]

/-- `q_i = D w_i*`. -/
noncomputable def q (c : ℂ) (i : ι) : B → ℂ := H.D c *ᵥ star (H.w c i)

/-- Second-order expansion of a new leverage. -/
lemma lev'_expand (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) (i : ι) :
    H.lev' c i = nsq (H.w c i) - (H.w c i ⬝ᵥ (H.D c *ᵥ star (H.w c i))).re
      + (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re := by
  have e1 : H.w c i ⬝ᵥ ((H.D c * H.Z c * H.D c) *ᵥ star (H.w c i))
      = star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      mulVec_star_eq_star _ (H.D_herm c)]
    rfl
  have e2 : (1 + H.D c)⁻¹ = 1 - H.D c + H.D c * H.Z c * H.D c := H.Z_expand c hF
  unfold lev'
  rw [e2, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_sub, e1, dotProduct_star_self_eq]
  simp

lemma norm_q_Z_le (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) (i : ι) :
    ‖star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)‖ ≤ 2 * nsq (H.q c i) := by
  refine (norm_dotProduct_le _ _).trans ?_
  rw [nsq_star]
  have h := Real.sqrt_le_sqrt (H.nsq_Z_mulVec_le c hF (H.q c i))
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have h0 := Real.mul_self_sqrt (nsq_nonneg (H.q c i))
  nlinarith [Real.sqrt_nonneg (nsq (H.q c i))]

/-- `|m'_i - ‖w_i‖²| ≤ 2 ‖w_i‖ ‖q_i‖`. -/
lemma abs_lev'_sub_le (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) (i : ι) :
    |H.lev' c i - nsq (H.w c i)| ≤ 2 * (√(nsq (H.w c i)) * √(nsq (H.q c i))) := by
  have e : H.lev' c i - nsq (H.w c i) = -(H.w c i ⬝ᵥ (H.Z c *ᵥ H.q c i)).re := by
    unfold lev'
    have hZ : H.Z c = 1 - H.Z c * H.D c := by rw [H.Z_mul_D c hF]; abel
    rw [show (1 + H.D c)⁻¹ = H.Z c from rfl]
    conv_lhs => rw [hZ]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_star_self_eq,
      ← Matrix.mulVec_mulVec]
    simp [q]
  rw [e, abs_neg]
  refine (Complex.abs_re_le_norm _).trans ((norm_dotProduct_le _ _).trans ?_)
  have h := Real.sqrt_le_sqrt (H.nsq_Z_mulVec_le c hF (H.q c i))
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  nlinarith [Real.sqrt_nonneg (nsq (H.w c i))]

/-- Bessel bound for the new rows: `‖W z‖² ≤ 2(1 + |c|²‖v‖² m) ‖z‖²`. -/
lemma W_bessel (hB : H.Bessel) (c : ℂ) (z : B → ℂ) :
    ∑ i ∈ H.S, ‖H.w c i ⬝ᵥ z‖ ^ 2 ≤ 2 * (1 + ‖c‖ ^ 2 * H.vn * H.m) * nsq z := by
  have h1 : ∀ i ∈ H.S, ‖H.w c i ⬝ᵥ z‖ ^ 2
      ≤ 2 * ‖H.u i ⬝ᵥ z‖ ^ 2 + 2 * (‖c‖ ^ 2 * ‖H.v i‖ ^ 2) * ‖H.ux ⬝ᵥ z‖ ^ 2 := by
    intro i _
    have e : H.w c i ⬝ᵥ z = H.u i ⬝ᵥ z + (c * H.v i) * (H.ux ⬝ᵥ z) := by
      simp [w, add_dotProduct, smul_dotProduct]
    rw [e]
    refine (norm_add_sq_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul]; ring
  have h2 : ∑ i ∈ H.S, ‖H.u i ⬝ᵥ z‖ ^ 2 ≤ nsq z :=
    le_trans (le_add_of_nonneg_right (sq_nonneg _)) (hB z)
  have h3 : ‖H.ux ⬝ᵥ z‖ ^ 2 ≤ H.m * nsq z := norm_dotProduct_sq_le _ _
  calc ∑ i ∈ H.S, ‖H.w c i ⬝ᵥ z‖ ^ 2
      ≤ ∑ i ∈ H.S, (2 * ‖H.u i ⬝ᵥ z‖ ^ 2 + 2 * (‖c‖ ^ 2 * ‖H.v i‖ ^ 2) * ‖H.ux ⬝ᵥ z‖ ^ 2) :=
        sum_le_sum h1
    _ = 2 * ∑ i ∈ H.S, ‖H.u i ⬝ᵥ z‖ ^ 2 + 2 * ‖c‖ ^ 2 * H.vn * ‖H.ux ⬝ᵥ z‖ ^ 2 := by
        simp only [vn, mul_sum, sum_mul, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
    _ ≤ 2 * nsq z + 2 * ‖c‖ ^ 2 * H.vn * (H.m * nsq z) := by
        have hvn : 0 ≤ H.vn := sum_nonneg fun _ _ => sq_nonneg _
        gcongr
    _ = _ := by ring

/-- `∑_i ‖D w_i*‖² ≤ ω ‖D‖_F²` from a Bessel bound `ω` for the new rows. -/
lemma sum_nsq_q_le (c : ℂ) (ω : ℝ)
    (hW : ∀ z : B → ℂ, ∑ i ∈ H.S, ‖H.w c i ⬝ᵥ z‖ ^ 2 ≤ ω * nsq z) :
    ∑ i ∈ H.S, nsq (H.q c i) ≤ ω * fro (H.D c) := by
  have e : ∀ i a, ‖H.q c i a‖ = ‖H.w c i ⬝ᵥ star (H.D c a)‖ := by
    intro i a
    simp only [q, mulVec, dotProduct, Pi.star_apply]
    rw [← norm_star, star_sum]
    congr 1
    exact sum_congr rfl fun b _ => by simp [mul_comm]
  calc ∑ i ∈ H.S, nsq (H.q c i) = ∑ a, ∑ i ∈ H.S, ‖H.w c i ⬝ᵥ star (H.D c a)‖ ^ 2 := by
        simp only [nsq, e]; exact sum_comm
    _ ≤ ∑ a, ω * nsq (star (H.D c a)) := sum_le_sum fun a _ => hW _
    _ = ω * fro (H.D c) := by simp only [nsq_star, ← mul_sum, fro_eq_sum_nsq]

/-! ### Exact sum identities -/

lemma nsq_w (c : ℂ) (i : ι) :
    nsq (H.w c i) = H.lev i + 2 * (c * H.v i * (H.ux ⬝ᵥ star (H.u i))).re
      + ‖c‖ ^ 2 * ‖H.v i‖ ^ 2 * H.m := by
  rw [w, nsq_add_smul, norm_mul, mul_pow]; rfl

lemma sum_vecMulVec_w (c : ℂ) :
    ∑ i ∈ H.S, vecMulVec (star (H.w c i)) (H.w c i) = H.Q + H.D c := by
  rw [D]; abel

lemma re_trace_D (c : ℂ) : (trace (H.D c)).re = ∑ i ∈ H.S, nsq (H.w c i) - H.A := by
  have : trace (H.D c) = ((∑ i ∈ H.S, nsq (H.w c i) - H.A : ℝ) : ℂ) := by
    simp only [D, Q, trace_sub, trace_add, trace_sum, trace_vecMulVec_star, A, lev, m]
    push_cast; ring
  rw [this, Complex.ofReal_re]

lemma sum_wDw (c : ℂ) :
    ∑ i ∈ H.S, H.w c i ⬝ᵥ (H.D c *ᵥ star (H.w c i)) = trace (H.D c * (H.Q + H.D c)) := by
  rw [← sum_vecMulVec_w, Matrix.mul_sum, trace_sum]
  exact sum_congr rfl fun i _ => (trace_mul_vecMulVec _ _ _).symm

/-- Exact form of the total-leverage change (eq. `clearing-total-leverage`, expanded). -/
lemma A'_sub_A (c : ℂ) (hF : fro (H.D c) ≤ 1 / 4) :
    H.A' c - H.A = (trace (H.D c * (1 - H.Q))).re - fro (H.D c)
      + ∑ i ∈ H.S, (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re := by
  have h1 : H.A' c = ∑ i ∈ H.S, nsq (H.w c i)
      - (∑ i ∈ H.S, H.w c i ⬝ᵥ (H.D c *ᵥ star (H.w c i))).re
      + ∑ i ∈ H.S, (star (H.q c i) ⬝ᵥ (H.Z c *ᵥ H.q c i)).re := by
    simp only [A', H.lev'_expand c hF, sum_add_distrib, sum_sub_distrib, Complex.re_sum]
  have h2 : (trace (H.D c * H.D c)).re = fro (H.D c) := by
    rw [← fro_eq_trace_mul_self _ (H.D_herm c), Complex.ofReal_re]
  have h3 := H.re_trace_D c
  rw [h1, sum_wDw, Matrix.mul_add, trace_add, Complex.add_re, h2, Matrix.mul_sub,
    Matrix.mul_one, trace_sub, Complex.sub_re]
  linarith

/-- Real part of `tr(D Y)` as an affine function of `(|c|², c)`. -/
lemma re_trace_D_mul (c : ℂ) (Y : Matrix B B ℂ) :
    (trace (H.D c * Y)).re = (‖c‖ ^ 2 * H.vn - 1) * (H.ux ⬝ᵥ (Y *ᵥ star H.ux)).re
      + (c * (H.ux ⬝ᵥ (Y *ᵥ H.b) + conj (star H.b ⬝ᵥ (Y *ᵥ star H.ux)))).re := by
  rw [trace_D_mul]
  simp only [Complex.add_re, Complex.re_ofReal_mul, mul_add]
  rw [show (conj c * (star H.b ⬝ᵥ (Y *ᵥ star H.ux))).re
      = (c * conj (star H.b ⬝ᵥ (Y *ᵥ star H.ux))).re by
    rw [← Complex.conj_re, map_mul, Complex.conj_conj]]
  ring

/-- the `𝒫`-weighted rank-three expansion. -/
lemma sum_lev_wDw (c : ℂ) :
    ∑ i ∈ H.S, (H.lev i : ℂ) * (H.w c i ⬝ᵥ (H.D c *ᵥ star (H.w c i)))
      = trace (H.D c * H.G0 H.lev)
        + ((‖c‖ ^ 2 * H.vw H.lev : ℝ) : ℂ) * (H.ux ⬝ᵥ (H.D c *ᵥ star H.ux))
        + c * (H.ux ⬝ᵥ (H.D c *ᵥ H.bw H.lev))
        + conj c * (star (H.bw H.lev) ⬝ᵥ (H.D c *ᵥ star H.ux)) := by
  rw [← trace_mul_Gw, Gw_eq]
  simp only [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, trace_mul_vecMulVec,
    smul_eq_mul]

lemma sum_lev_d0 (c : ℂ) :
    ∑ i ∈ H.S, H.lev i * (nsq (H.w c i) - H.lev i)
      = 2 * (c * (H.ux ⬝ᵥ H.bw H.lev)).re + ‖c‖ ^ 2 * H.m * H.vw H.lev := by
  have e : H.ux ⬝ᵥ H.bw H.lev = ∑ i ∈ H.S, (H.lev i : ℂ) * (H.v i * (H.ux ⬝ᵥ star (H.u i))) := by
    simp only [bw, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    exact sum_congr rfl fun i _ => by ring
  rw [e, mul_sum, Complex.re_sum, mul_sum, vw, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [nsq_w]
  have : (c * ((H.lev i : ℂ) * (H.v i * (H.ux ⬝ᵥ star (H.u i))))).re
      = H.lev i * (c * H.v i * (H.ux ⬝ᵥ star (H.u i))).re := by
    rw [← Complex.re_ofReal_mul]; ring_nf
  rw [this]; ring

end NHeat

end AndersonAC.L64
