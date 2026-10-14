import AndersonAC.L64.Bridge

/-!
# Lemma 6.4: the unitary cancellation

Paper l.471–500 (eq. `clearing-b-cancellation`): for a symmetric unitary `S`, the vector
`U* S_{Rx}` has norm at most `√m`, where `m = m_x` is the ridge leverage of the pivot. This is
stronger than the trivial bound `‖U‖ ‖S_{Rx}‖ ≤ 1` and is what makes `b_x = U_{R'}* v` of size
`√(m/t)`.

With `T = S_B`, `s = S_{Bx}`: orthogonality of the columns of `S` gives `𝒞* S_{Rx} = -T* s`,
and `G_τ T* = T* Ĝ` with `Ĝ = (1+τ) - T T* = conj G_τ` gives `T G_τ⁻¹ T* = (1+τ) Ĝ⁻¹ - 1`.
-/

open Matrix Finset ComplexConjugate
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Cancel

variable {S : Matrix ι ι ℂ} {B : Finset ι} {τ : ℝ} {L : Matrix B B ℂ} {x : ι}

/-- the core block `T = S_{BB}`. -/
def coreBlock (S : Matrix ι ι ℂ) (B : Finset ι) : Matrix B B ℂ := fun b b' => S b b'

/-- `𝒞* 𝒞 = 1 - T* T` for a unitary `S`. -/
lemma gram_eq_one_sub (hU : Sᴴ * S = 1) :
    gram S B Bᶜ = 1 - (coreBlock S B)ᴴ * coreBlock S B := by
  ext b b'
  have h := congrFun (congrFun hU b) b'
  simp only [mul_apply, conjTranspose_apply, Matrix.one_apply] at h
  rw [← sum_add_sum_compl B] at h
  simp only [gram, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, crossRow, Matrix.sub_apply,
    Matrix.one_apply, mul_apply, conjTranspose_apply, coreBlock]
  rw [← sum_coe_sort B (fun k => star (S k b) * S k b')] at h
  have hbb : ((b : ι) = b') ↔ b = b' := Subtype.ext_iff.symm
  by_cases hb : b = b'
  · rw [if_pos hb]; rw [if_pos (hbb.mpr hb)] at h; linear_combination h
  · rw [if_neg hb]; rw [if_neg (fun h' => hb (hbb.mp h'))] at h; linear_combination h

/-- `𝒞* S_{Rx} = -T* s` for a unitary `S` and `x ∉ B`. -/
lemma cross_col_eq (hU : Sᴴ * S = 1) (hx : x ∉ B) :
    ∑ i ∈ Bᶜ, S i x • star (crossRow S B i)
      = -((coreBlock S B)ᴴ *ᵥ fun k : B => S k x) := by
  ext b
  have h := congrFun (congrFun hU b) x
  have hbx : (b : ι) ≠ x := fun h' => hx (h' ▸ b.2)
  simp only [mul_apply, conjTranspose_apply, Matrix.one_apply, if_neg hbx] at h
  rw [← sum_add_sum_compl B] at h
  rw [← sum_coe_sort B (fun k => star (S k b) * S k x)] at h
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.star_apply, crossRow, smul_eq_mul, Pi.neg_apply,
    mulVec, dotProduct, conjTranspose_apply, coreBlock]
  rw [sum_congr rfl (fun i _ => mul_comm (S i x) (star (S i b)))]
  linear_combination h

/-- `Ĝ := conj G_τ`. -/
noncomputable def ridgeGconj (S : Matrix ι ι ℂ) (B : Finset ι) (τ : ℝ) : Matrix B B ℂ :=
  (gram S B Bᶜ + (τ : ℂ) • 1).map (starRingEnd ℂ)

lemma ridgeGconj_inv (hτ : 0 < τ) :
    (ridgeGconj S B τ)⁻¹ = ((gram S B Bᶜ + (τ : ℂ) • 1)⁻¹).map (starRingEnd ℂ) := by
  have hG := (ridgeG_posDef S B τ Bᶜ hτ).isUnit
  apply Matrix.inv_eq_right_inv
  unfold ridgeGconj
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG), map_one]

/-- For symmetric `S`: `Ĝ = (1+τ) - T T*`. -/
lemma ridgeGconj_eq (hU : Sᴴ * S = 1) (hS : Sᵀ = S) :
    ridgeGconj S B τ = ((1 + τ : ℝ) : ℂ) • 1 - coreBlock S B * (coreBlock S B)ᴴ := by
  have hs : ∀ i j, S j i = S i j := fun i j => by
    simpa [transpose_apply] using congrFun (congrFun hS i) j
  unfold ridgeGconj
  rw [gram_eq_one_sub hU]
  ext b b'
  simp only [map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    mul_apply, conjTranspose_apply, coreBlock, smul_eq_mul, map_add, map_sub, map_sum, map_mul,
    Complex.star_def, Complex.conj_conj]
  push_cast
  rw [Complex.conj_ofReal]
  have e : ∑ k : B, S k b * conj (S k b') = ∑ k : B, S b k * conj (S b' k) :=
    sum_congr rfl fun k _ => by rw [hs (b : ι) k, hs (b' : ι) k]
  rw [e]
  split_ifs <;> simp; ring

lemma isUnit_det_ridgeGconj (hτ : 0 < τ) : IsUnit (ridgeGconj S B τ).det := by
  have hG := (ridgeG_posDef S B τ Bᶜ hτ).isUnit
  refine Matrix.isUnit_det_of_right_inverse (B := ((gram S B Bᶜ + (τ : ℂ) • 1)⁻¹).map
    (starRingEnd ℂ)) ?_
  unfold ridgeGconj
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG), map_one]

/-- The intertwining `G_τ T* = T* Ĝ`. -/
lemma intertwine (hU : Sᴴ * S = 1) (hS : Sᵀ = S) :
    (gram S B Bᶜ + (τ : ℂ) • 1) * (coreBlock S B)ᴴ = (coreBlock S B)ᴴ * ridgeGconj S B τ := by
  rw [gram_eq_one_sub hU, ridgeGconj_eq hU hS]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  push_cast
  rw [add_smul, one_smul]
  abel

/-- `T G_τ⁻¹ T* = (1+τ) Ĝ⁻¹ - 1`. -/
lemma core_sandwich (hτ : 0 < τ) (hU : Sᴴ * S = 1) (hS : Sᵀ = S) :
    coreBlock S B * (gram S B Bᶜ + (τ : ℂ) • 1)⁻¹ * (coreBlock S B)ᴴ
      = ((1 + τ : ℝ) : ℂ) • (ridgeGconj S B τ)⁻¹ - 1 := by
  have hG := (isUnit_iff_isUnit_det _).mp (ridgeG_posDef S B τ Bᶜ hτ).isUnit
  have hGc := isUnit_det_ridgeGconj (S := S) (B := B) hτ
  have h1 : (gram S B Bᶜ + (τ : ℂ) • 1)⁻¹ * (coreBlock S B)ᴴ
      = (coreBlock S B)ᴴ * (ridgeGconj S B τ)⁻¹ := by
    have := congrArg (fun X => (gram S B Bᶜ + (τ : ℂ) • 1)⁻¹ * X * (ridgeGconj S B τ)⁻¹)
      (intertwine (τ := τ) hU hS)
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGc, Matrix.mul_one] at this
    exact this.symm
  have h2 : coreBlock S B * (coreBlock S B)ᴴ = ((1 + τ : ℝ) : ℂ) • 1 - ridgeGconj S B τ := by
    rw [ridgeGconj_eq hU hS]; abel
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, h2, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_nonsing_inv _ hGc]

lemma star_dotProduct_map_conj_mulVec {B : Type*} [Fintype B] (M : Matrix B B ℂ) (s : B → ℂ) :
    star s ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ s) = conj (s ⬝ᵥ (M *ᵥ star s)) := by
  simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.star_def, map_sum, map_mul,
    Complex.conj_conj]

/-- **Unitary cancellation**: `‖U* S_{Rx}‖² ≤ m_x` (paper l.475–500). -/
lemma cancellation (hτ : 0 < τ) (hL : L * Lᴴ = (gram S B Bᶜ + (τ : ℂ) • 1)⁻¹)
    (hU : Sᴴ * S = 1) (hS : Sᵀ = S) (hx : x ∉ B) :
    nsq (∑ i ∈ Bᶜ, S i x • star (crossRow S B i ᵥ* L)) ≤ ridgeLev S B Bᶜ τ x := by
  have hs : ∀ i j, S j i = S i j := fun i j => by
    simpa [transpose_apply] using congrFun (congrFun hS i) j
  have hsC : (fun k : B => S k x) = crossRow S B x := funext fun k => hs x k
  have e1 : ∑ i ∈ Bᶜ, S i x • star (crossRow S B i ᵥ* L)
      = Lᴴ *ᵥ (-((coreBlock S B)ᴴ *ᵥ fun k : B => S k x)) := by
    rw [← cross_col_eq hU hx, Matrix.mulVec_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, star_vecMul]
  have e2 : ((nsq (Lᴴ *ᵥ (-((coreBlock S B)ᴴ *ᵥ fun k : B => S k x))) : ℝ) : ℂ)
      = ((1 + τ : ℝ) : ℂ) * (star (crossRow S B x) ⬝ᵥ ((ridgeGconj S B τ)⁻¹ *ᵥ crossRow S B x))
        - ((nsq (crossRow S B x) : ℝ) : ℂ) := by
    rw [nsq_conjTranspose_mulVec hτ hL, star_neg, Matrix.mulVec_neg, neg_dotProduct,
      dotProduct_neg, neg_neg, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, core_sandwich hτ hU hS,
      Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, star_dotProduct_self_eq, hsC]
  have e3 : star (crossRow S B x) ⬝ᵥ ((ridgeGconj S B τ)⁻¹ *ᵥ crossRow S B x)
      = conj (crossRow S B x ⬝ᵥ ((gram S B Bᶜ + (τ : ℂ) • 1)⁻¹ *ᵥ star (crossRow S B x))) := by
    rw [ridgeGconj_inv hτ, star_dotProduct_map_conj_mulVec]
  -- `m_x = ‖Lᴴ 𝒞_x*‖²`
  have e4 : ((nsq (Lᴴ *ᵥ star (crossRow S B x)) : ℝ) : ℂ)
      = crossRow S B x ⬝ᵥ ((gram S B Bᶜ + (τ : ℂ) • 1)⁻¹ *ᵥ star (crossRow S B x)) := by
    rw [nsq_conjTranspose_mulVec hτ hL, star_star]
  have hm : ridgeLev S B Bᶜ τ x = nsq (Lᴴ *ᵥ star (crossRow S B x)) := by
    unfold ridgeLev; rw [← e4, Complex.ofReal_re]
  have h5 := tau_nsq_conjTranspose_mulVec_le hτ hL (star (crossRow S B x))
  rw [nsq_star, ← hm] at h5
  rw [e3, ← e4] at e2
  have e6 : nsq (Lᴴ *ᵥ (-((coreBlock S B)ᴴ *ᵥ fun k : B => S k x)))
      = (1 + τ) * nsq (Lᴴ *ᵥ star (crossRow S B x)) - nsq (crossRow S B x) := by
    have := congrArg Complex.re e2
    simpa [Complex.conj_ofReal] using this
  rw [e1, e6, ← hm]
  linarith

lemma norm_diag_le_one (hU : Sᴴ * S = 1) (x : ι) : ‖S x x‖ ≤ 1 := by
  have h := congrFun (congrFun hU x) x
  simp only [mul_apply, conjTranspose_apply, Matrix.one_apply, if_true] at h
  have h2 : ∑ k, ‖S k x‖ ^ 2 = 1 := by
    have : ((∑ k, ‖S k x‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]; push_cast
      exact sum_congr rfl fun k _ => by rw [Complex.star_def, ← ofReal_norm_sq_eq]
    exact_mod_cast this
  have h3 : ‖S x x‖ ^ 2 ≤ 1 := by
    rw [← h2]
    exact single_le_sum (f := fun k => ‖S k x‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ x)
  nlinarith [norm_nonneg (S x x)]

/-- The bound `‖b_x‖² ≤ 4|κ|² m_x` when `v_i = κ S_{ix}` on `R'` (eq. `clearing-b-cancellation`). -/
lemma nsq_b_le (hτ : 0 < τ) (hL : L * Lᴴ = (gram S B Bᶜ + (τ : ℂ) • 1)⁻¹)
    (hU : Sᴴ * S = 1) (hS : Sᵀ = S) (hx : x ∉ B) (v : ι → ℂ) (κ : ℂ)
    (hv : ∀ i ∈ Bᶜ.erase x, v i = κ * S i x) :
    nsq (nheat S L x v).b ≤ 4 * ‖κ‖ ^ 2 * (nheat S L x v).m := by
  have hxR : x ∈ (Bᶜ : Finset ι) := mem_compl.mpr hx
  have hm : (nheat S L x v).m = ridgeLev S B Bᶜ τ x := nheat_m v hτ hL
  have e : (nheat S L x v).b = κ • (∑ i ∈ Bᶜ, S i x • star (crossRow S B i ᵥ* L)
      - S x x • star (crossRow S B x ᵥ* L)) := by
    rw [← sum_erase_add _ _ hxR, add_sub_cancel_right, Finset.smul_sum]
    unfold NHeat.b
    refine sum_congr rfl fun i hi => ?_
    simp only [nheat]
    rw [hv i hi, smul_smul]
  rw [e, nsq_smul]
  have h1 := nsq_add_le (∑ i ∈ Bᶜ, S i x • star (crossRow S B i ᵥ* L))
    (-(S x x • star (crossRow S B x ᵥ* L)))
  rw [nsq_neg, ← sub_eq_add_neg, nsq_smul, nsq_star] at h1
  have h2 := cancellation hτ hL hU hS hx
  have h3 : ‖S x x‖ ^ 2 ≤ 1 := by
    have := norm_diag_le_one hU x
    nlinarith [norm_nonneg (S x x)]
  have h4 : nsq (crossRow S B x ᵥ* L) = (nheat S L x v).m := rfl
  rw [h4, hm] at h1
  rw [hm]
  have h5 : 0 ≤ ridgeLev S B Bᶜ τ x := by rw [← hm]; exact nsq_nonneg _
  have h6 : nsq (∑ i ∈ Bᶜ, S i x • star (crossRow S B i ᵥ* L) - S x x • star (crossRow S B x ᵥ* L))
      ≤ 4 * ridgeLev S B Bᶜ τ x := by nlinarith
  calc ‖κ‖ ^ 2 * nsq (∑ i ∈ Bᶜ, S i x • star (crossRow S B i ᵥ* L)
        - S x x • star (crossRow S B x ᵥ* L))
      ≤ ‖κ‖ ^ 2 * (4 * ridgeLev S B Bᶜ τ x) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
    _ = _ := by ring

end Cancel

end AndersonAC.L64
