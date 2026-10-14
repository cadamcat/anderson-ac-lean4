import AndersonAC.L64.Heat
import AndersonAC.L64.Residual

/-!
# Lemma 6.4: the concrete inputs of the normalized heat

For the paper's prestate (`06-clearing.tex` l.391–404) we define the ridge leverages before and
after the heat and verify the inputs of `NHeat.drift`: the Bessel inequality, the bounds
eq. `clearing-v-bounds` on `v`, the cancellation bound on `b_x`, and the bound on
`∑ m_i |v_i|²` used in eq. `clearing-raw-mean`.
-/

open Matrix Finset ComplexConjugate Complex MeasureTheory

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Defs

variable (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) (B : Finset ι) (x : ι) (τ : ℝ)

/-- prestate ridge leverage `m_i = (𝒞(𝒞*𝒞 + τ)⁻¹𝒞*)_{ii}`, `𝒞 = S_{RB}`, `R = Bᶜ`. -/
noncomputable def preLev (i : ι) : ℝ := ridgeLev (scat t (pim r) (damped M t r)⁻¹) B Bᶜ τ i
/-- `𝒜 = ∑_{i ∈ R} m_i`. -/
noncomputable def preA : ℝ := ∑ i ∈ Bᶜ, preLev M t r B τ i
/-- `𝒫 = ∑_{i ∈ R} m_i²`. -/
noncomputable def preP : ℝ := ∑ i ∈ Bᶜ, preLev M t r B τ i ^ 2
/-- poststate ridge leverage `m'_i` on `R' = R ∖ {x}`, computed from the new active inverse
(the `A ∖ {x}` block of the inverse of the updated damped matrix) at the same ridge `τ`. -/
noncomputable def postLev (ξ : ℝ) (i : ι) : ℝ :=
  ridgeLev (scat t (pim r) (dampedPost M t r x ξ)⁻¹) B (Bᶜ.erase x) τ i
/-- `𝒜' = ∑_{i ∈ R'} m'_i`. -/
noncomputable def postA (ξ : ℝ) : ℝ := ∑ i ∈ Bᶜ.erase x, postLev M t r B x τ ξ i
/-- `𝒫' = ∑_{i ∈ R'} m'_i²`. -/
noncomputable def postP (ξ : ℝ) : ℝ := ∑ i ∈ Bᶜ.erase x, postLev M t r B x τ ξ i ^ 2

end Defs

section Inputs

variable {M : Matrix ι ι ℝ} {t : ℝ} {r : ι → ℂ} {B : Finset ι} {x : ι} {τ : ℝ} {C c : ℝ}

/-- `|v_i|² = t |g_{ix}|² p_i/p_x`. -/
lemma norm_sq_heatVec (ht : 0 < t) (hp : ∀ i, 0 < (r i).im) (i : ι) :
    ‖heatVec M t r x i‖ ^ 2 = t * ‖(damped M t r)⁻¹ i x‖ ^ 2 * ((r i).im / (r x).im) := by
  rw [heatVec, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt (div_nonneg (hp i).le (hp x).le)]

/-- `|h_{xi}|² = t |g_{xi}|²`. -/
lemma norm_sq_h (ht : 0 < t) (i j : ι) :
    ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ i j‖ ^ 2 = t * ‖(damped M t r)⁻¹ i j‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt ht.le]

/-- The Ward identity for `v`: `∑_i |v_i|² = Im g_xx / p_x` (paper l.437–441). -/
lemma sum_norm_sq_heatVec (hM : M.IsSymm) (ht : 0 < t) (hp : ∀ i, 0 < (r i).im) :
    ∑ i, ‖heatVec M t r x i‖ ^ 2 = ((damped M t r)⁻¹ x x).im / (r x).im := by
  have hD := isUnit_det_damped M t r hM ht hp
  rw [im_diag_ward hM hD x, mul_sum, sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [norm_sq_heatVec ht hp, resolvent_symm hM i x]
  ring

/-- Each `|v_i|² ≤ (C/c) |h_{xi}|²`. -/
lemma norm_sq_heatVec_le (ht : 0 < t) (hp : ∀ i, c ≤ (r i).im ∧ (r i).im ≤ C) (hc0 : 0 < c)
    (hM : M.IsSymm) (i : ι) :
    ‖heatVec M t r x i‖ ^ 2 ≤ C / c * ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 2 := by
  have hp' : ∀ i, 0 < (r i).im := fun i => hc0.trans_le (hp i).1
  rw [norm_sq_heatVec ht hp', norm_sq_h ht, resolvent_symm hM i x]
  have h1 : (r i).im / (r x).im ≤ C / c :=
    div_le_div₀ (hc0.le.trans (hp i).1 |>.trans (hp i).2) (hp i).2 hc0 (hp x).1
  have h2 : 0 ≤ t * ‖(damped M t r)⁻¹ x i‖ ^ 2 := mul_nonneg ht.le (sq_nonneg _)
  calc t * ‖(damped M t r)⁻¹ x i‖ ^ 2 * ((r i).im / (r x).im)
      ≤ t * ‖(damped M t r)⁻¹ x i‖ ^ 2 * (C / c) := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

lemma norm_sq_h_le_sqrt {Hs : ℝ} (ht : 0 < t)
    (hfour : ∑ j, ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x j‖ ^ 4 ≤ Hs) (i : ι) :
    ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 2 ≤ √Hs := by
  have h1 : ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 4 ≤ Hs :=
    (single_le_sum (f := fun j => ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x j‖ ^ 4)
      (fun _ _ => by positivity) (mem_univ i)).trans hfour
  rw [show ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 4
      = (‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 2) ^ 2 by ring] at h1
  exact Real.le_sqrt_of_sq_le h1

end Inputs

section Normalization

variable {M : Matrix ι ι ℝ} {t : ℝ} {r : ι → ℂ} {B : Finset ι} {x : ι} {τ : ℝ} {C c : ℝ}
  {L : Matrix B B ℂ}

/-- The normalized heat of the prestate. -/
noncomputable abbrev theHeat (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) (B : Finset ι) (x : ι)
    (L : Matrix B B ℂ) : NHeat ι B :=
  nheat (scat t (pim r) (damped M t r)⁻¹) L x (heatVec M t r x)

variable (hM : M.IsSymm) (ht : 0 < t) (hc0 : 0 < c) (hp : ∀ i, c ≤ (r i).im ∧ (r i).im ≤ C)
  (hx : x ∉ B) (hτ : 0 < τ)
  (hL : L * Lᴴ = (gram (scat t (pim r) (damped M t r)⁻¹) B Bᶜ + (τ : ℂ) • 1)⁻¹)
include hM ht hc0 hp hx hτ hL

lemma theHeat_vn_bound {Hs : ℝ}
    (hfour : ∑ j, ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x j‖ ^ 4 ≤ Hs) :
    |(theHeat M t r B x L).vn - 1|
      ≤ ‖(damped M t r)⁻¹ x x - r x‖ / c + (B.card + 1) * (C / c * √Hs) := by
  have hp' : ∀ i, 0 < (r i).im := fun i => hc0.trans_le (hp i).1
  have hxR : x ∈ (Bᶜ : Finset ι) := mem_compl.mpr hx
  set W : ι → ℝ := fun i => ‖heatVec M t r x i‖ ^ 2
  have hW0 : ∀ i, 0 ≤ W i := fun i => sq_nonneg _
  have hWle : ∀ i, W i ≤ C / c * √Hs := fun i =>
    (norm_sq_heatVec_le ht hp hc0 hM i).trans
      (mul_le_mul_of_nonneg_left (norm_sq_h_le_sqrt ht hfour i)
        (div_nonneg (hc0.le.trans (hp i).1 |>.trans (hp i).2) hc0.le))
  have e1 : ∑ i, W i = ((damped M t r)⁻¹ x x).im / (r x).im := sum_norm_sq_heatVec hM ht hp'
  have e2 : ∑ i, W i = ∑ i ∈ B, W i + (∑ i ∈ Bᶜ.erase x, W i + W x) := by
    rw [sum_erase_add _ _ hxR, sum_add_sum_compl]
  have hvn : (theHeat M t r B x L).vn = ∑ i ∈ Bᶜ.erase x, W i := rfl
  have e3 : ∑ i ∈ B, W i + W x ≤ (B.card + 1) * (C / c * √Hs) := by
    have := sum_le_card_nsmul B W (C / c * √Hs) fun i _ => hWle i
    rw [nsmul_eq_mul] at this
    have := hWle x
    linarith
  have e4 : |((damped M t r)⁻¹ x x).im / (r x).im - 1| ≤ ‖(damped M t r)⁻¹ x x - r x‖ / c := by
    have hpx := hp' x
    rw [div_sub_one hpx.ne', abs_div, abs_of_pos hpx]
    calc |((damped M t r)⁻¹ x x).im - (r x).im| / (r x).im
        ≤ ‖(damped M t r)⁻¹ x x - r x‖ / (r x).im := by
          gcongr
          rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      _ ≤ ‖(damped M t r)⁻¹ x x - r x‖ / c :=
          div_le_div_of_nonneg_left (norm_nonneg _) hc0 (hp x).1
  have h0 : 0 ≤ ∑ i ∈ B, W i := sum_nonneg fun i _ => hW0 i
  rw [hvn]
  have : ∑ i ∈ Bᶜ.erase x, W i - 1
      = (((damped M t r)⁻¹ x x).im / (r x).im - 1) - (∑ i ∈ B, W i + W x) := by
    rw [← e1, e2]; ring
  rw [this]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (add_nonneg h0 (hW0 x))]
  linarith

lemma theHeat_v4_bound {Hs : ℝ}
    (hfour : ∑ j, ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x j‖ ^ 4 ≤ Hs) :
    (theHeat M t r B x L).v4 ≤ (C / c) ^ 2 * Hs := by
  have hCc : 0 ≤ C / c := div_nonneg (hc0.le.trans (hp x).1 |>.trans (hp x).2) hc0.le
  have h1 : ∀ i, ‖heatVec M t r x i‖ ^ 4
      ≤ (C / c) ^ 2 * ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 4 := by
    intro i
    have := norm_sq_heatVec_le ht hp hc0 hM (x := x) i
    calc ‖heatVec M t r x i‖ ^ 4 = (‖heatVec M t r x i‖ ^ 2) ^ 2 := by ring
      _ ≤ (C / c * ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) this 2
      _ = _ := by ring
  calc (theHeat M t r B x L).v4 = ∑ i ∈ Bᶜ.erase x, ‖heatVec M t r x i‖ ^ 4 := rfl
    _ ≤ ∑ i, ‖heatVec M t r x i‖ ^ 4 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
    _ ≤ ∑ i, (C / c) ^ 2 * ‖((√t : ℝ) : ℂ) * (damped M t r)⁻¹ x i‖ ^ 4 := sum_le_sum fun i _ => h1 i
    _ ≤ (C / c) ^ 2 * Hs := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hfour (sq_nonneg _)

lemma theHeat_b_bound :
    nsq (theHeat M t r B x L).b ≤ (theHeat M t r B x L).m / (t * c ^ 2) := by
  have hp' : ∀ i, 0 < (r i).im := fun i => hc0.trans_le (hp i).1
  have hD := isUnit_det_damped M t r hM ht hp'
  have hU := scat_unitary (t := t) (p := pim r) _ (fun i => (hp' i).le) (ward_left hM hD)
  have hS := scat_transpose (t := t) (p := pim r) _ (resolvent_transpose (t := t) (r := r) hM)
  set κ : ℂ := 1 / (2 * I * ((√t : ℝ) : ℂ) * (((r x).im : ℝ) : ℂ))
  have hv : ∀ i ∈ Bᶜ.erase x, heatVec M t r x i = κ * scat t (pim r) (damped M t r)⁻¹ i x :=
    fun i hi => heatVec_eq ht hp' x (ne_of_mem_erase hi)
  have h := nsq_b_le hτ hL hU hS hx (heatVec M t r x) κ hv
  have hκ : ‖κ‖ ^ 2 = 1 / (4 * (t * (r x).im ^ 2)) := by
    simp only [κ, norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_I,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (hp' x).le, RCLike.norm_ofNat]
    rw [div_pow, one_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht.le]
    ring
  rw [hκ] at h
  have hm := nsq_nonneg (theHeat M t r B x L).ux
  calc nsq (theHeat M t r B x L).b ≤ 4 * (1 / (4 * (t * (r x).im ^ 2))) * (theHeat M t r B x L).m := h
    _ = (theHeat M t r B x L).m / (t * (r x).im ^ 2) := by field_simp
    _ ≤ (theHeat M t r B x L).m / (t * c ^ 2) := by
        apply div_le_div_of_nonneg_left hm (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le (hp x).1 2) ht.le

end Normalization

end AndersonAC.L64
