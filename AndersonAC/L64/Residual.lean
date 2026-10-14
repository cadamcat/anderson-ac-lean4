import AndersonAC.L64.Vec

/-!
# Lemma 6.4: moments of the heat coefficient

`c_x = -a/(√t (1 + a g_xx))`, `a = ξ + t r_x` (eq. `clearing-heat-update`). Under the residual
hypotheses (eq. `clearing-residual-moments`) `𝔼ξ = 0`, `𝔼ξ² = t - η`, `|ξ| ≤ C√t`,
`0 ≤ η ≤ C t²`, we get (eq. `clearing-heat-moments`)
`|c_x| ≤ 4C`, `|𝔼 c_x - √t (g_xx - r_x)| ≲ t`, `|𝔼|c_x|² - 1| ≲ √t`.
-/

open Complex MeasureTheory

namespace AndersonAC.L64

/-- `c(ξ) = -(ξ + tρ)/(√t (1 + (ξ + tρ) γ))`. -/
noncomputable def hc (t : ℝ) (ρ γ : ℂ) (ξ : ℝ) : ℂ :=
  -((ξ : ℂ) + (t : ℂ) * ρ) / (((√t : ℝ) : ℂ) * (1 + ((ξ : ℂ) + (t : ℂ) * ρ) * γ))

lemma hc_expand_alg (a γ s : ℂ) (hs : s ≠ 0) (h1 : 1 + a * γ ≠ 0) :
    -a / (s * (1 + a * γ)) - (-a / s + a ^ 2 * γ / s) = -(a ^ 3 * γ ^ 2) / (s * (1 + a * γ)) := by
  field_simp
  ring

lemma norm_sq_hc_alg (a z : ℂ) (s : ℝ) (hs : 0 < s) :
    ‖-a / ((s : ℂ) * (1 + z))‖ ^ 2 = ‖a‖ ^ 2 / s ^ 2 / ‖1 + z‖ ^ 2 := by
  rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, div_pow,
    mul_pow, div_div]

section Pathwise

variable {t C : ℝ} {ρ γ : ℂ} {ξ : ℝ}

/-- standing smallness: `0 < t ≤ 1`, `4 C² √t ≤ 1`. -/
structure Small (t C : ℝ) : Prop where
  pos : 0 < t
  le_one : t ≤ 1
  C_nonneg : 0 ≤ C
  small : 4 * C ^ 2 * √t ≤ 1

lemma Small.sqrt_pos (h : Small t C) : 0 < √t := Real.sqrt_pos.mpr h.pos

lemma Small.sqrt_le_one (h : Small t C) : √t ≤ 1 := Real.sqrt_le_one.mpr h.le_one

lemma Small.t_le_sqrt (h : Small t C) : t ≤ √t := by
  have := h.sqrt_le_one
  have e : t = √t * √t := (Real.mul_self_sqrt h.pos.le).symm
  calc t = √t * √t := e
    _ ≤ 1 * √t := mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    _ = √t := one_mul _

variable (h : Small t C) (hρ : ‖ρ‖ ≤ C) (hγ : ‖γ‖ ≤ C) (hξ : |ξ| ≤ C * √t)
include h hρ hξ

lemma norm_a_le : ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ≤ 2 * C * √t := by
  calc ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ≤ |ξ| + t * C := by
        refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h.pos.le]
        exact mul_le_mul_of_nonneg_left hρ h.pos.le
    _ ≤ C * √t + √t * C := add_le_add hξ (mul_le_mul_of_nonneg_right h.t_le_sqrt h.C_nonneg)
    _ = 2 * C * √t := by ring

include hγ

lemma norm_aγ_le : ‖((ξ : ℂ) + (t : ℂ) * ρ) * γ‖ ≤ 1 / 2 := by
  rw [norm_mul]
  have h1 := norm_a_le h hρ hξ
  calc ‖(ξ : ℂ) + (t : ℂ) * ρ‖ * ‖γ‖ ≤ (2 * C * √t) * C :=
        mul_le_mul h1 hγ (norm_nonneg _) (by have := h.sqrt_pos; have := h.C_nonneg; positivity)
    _ = (4 * C ^ 2 * √t) / 2 := by ring
    _ ≤ 1 / 2 := by have := h.small; linarith

lemma half_le_norm_one_add : 1 / 2 ≤ ‖1 + ((ξ : ℂ) + (t : ℂ) * ρ) * γ‖ := by
  have h1 := norm_aγ_le h hρ hγ hξ
  have h2 := norm_sub_norm_le (1 : ℂ) (-(((ξ : ℂ) + (t : ℂ) * ρ) * γ))
  rw [sub_neg_eq_add, norm_neg, norm_one] at h2
  linarith

lemma one_add_ne_zero : 1 + ((ξ : ℂ) + (t : ℂ) * ρ) * γ ≠ 0 := by
  intro h0
  have := half_le_norm_one_add h hρ hγ hξ
  rw [h0, norm_zero] at this
  norm_num at this

lemma norm_hc_le : ‖hc t ρ γ ξ‖ ≤ 4 * C := by
  have h1 := norm_a_le h hρ hξ
  have h2 := half_le_norm_one_add h hρ hγ hξ
  have hs := h.sqrt_pos
  unfold hc
  rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le,
    div_le_iff₀ (by positivity)]
  calc ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ≤ 2 * C * √t := h1
    _ = 4 * C * (√t * (1 / 2)) := by ring
    _ ≤ 4 * C * (√t * ‖1 + ((ξ : ℂ) + (t : ℂ) * ρ) * γ‖) := by
        have := h.C_nonneg
        gcongr

/-- Second-order expansion: `c = -a/√t + a²γ/√t + O(t)`. -/
lemma norm_hc_sub_le :
    ‖hc t ρ γ ξ - (-((ξ : ℂ) + (t : ℂ) * ρ) / ((√t : ℝ) : ℂ)
        + ((ξ : ℂ) + (t : ℂ) * ρ) ^ 2 * γ / ((√t : ℝ) : ℂ))‖ ≤ 16 * C ^ 5 * t := by
  have h1 := norm_a_le h hρ hξ
  have h2 := half_le_norm_one_add h hρ hγ hξ
  have hne := one_add_ne_zero h hρ hγ hξ
  have hs := h.sqrt_pos
  have hs' : ((√t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  unfold hc
  rw [hc_expand_alg _ _ _ hs' hne, norm_div, norm_neg, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hs.le, div_le_iff₀ (by positivity)]
  have hC := h.C_nonneg
  have ha3 : ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ^ 3 ≤ (2 * C * √t) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h1 3
  have hγ2 : ‖γ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hγ 2
  have et : t = √t * √t := (Real.mul_self_sqrt h.pos.le).symm
  have hk : 0 ≤ 16 * C ^ 5 * t := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC 5)) h.pos.le
  calc ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ^ 3 * ‖γ‖ ^ 2 ≤ (2 * C * √t) ^ 3 * C ^ 2 :=
        mul_le_mul ha3 hγ2 (sq_nonneg _) (by positivity)
    _ = 16 * C ^ 5 * (√t * √t) * (√t * (1 / 2)) := by ring
    _ ≤ 16 * C ^ 5 * t * (√t * ‖1 + ((ξ : ℂ) + (t : ℂ) * ρ) * γ‖) := by
        rw [← et]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hs.le) hk

/-- `||c|² - |a|²/t| ≤ 96 C⁴ √t`. -/
lemma abs_norm_hc_sq_sub_le :
    |‖hc t ρ γ ξ‖ ^ 2 - ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t| ≤ 96 * C ^ 4 * √t := by
  have h1 := norm_a_le h hρ hξ
  have h2 := half_le_norm_one_add h hρ hγ hξ
  have hz := norm_aγ_le h hρ hγ hξ
  have hs := h.sqrt_pos
  have hC := h.C_nonneg
  have et : t = √t * √t := (Real.mul_self_sqrt h.pos.le).symm
  have e : ‖hc t ρ γ ξ‖ ^ 2
      = ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t / ‖1 + ((ξ : ℂ) + (t : ℂ) * ρ) * γ‖ ^ 2 := by
    unfold hc
    rw [norm_sq_hc_alg _ _ _ hs, Real.sq_sqrt h.pos.le]
  generalize hA : ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t = A at e
  generalize hzz : ((ξ : ℂ) + (t : ℂ) * ρ) * γ = z at h2 hz e
  have hz2 : |‖1 + z‖ ^ 2 - 1| ≤ 3 * ‖z‖ := by
    have l1 : ‖1 + z‖ ≤ 1 + ‖z‖ := by
      have := norm_add_le (1 : ℂ) z; rwa [norm_one] at this
    have l2 : 1 - ‖z‖ ≤ ‖1 + z‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-z); rw [sub_neg_eq_add, norm_neg, norm_one] at this
      exact this
    have hz0 := norm_nonneg z
    rw [abs_le]; constructor <;> nlinarith
  have ha2 : A ≤ 4 * C ^ 2 := by
    rw [← hA, div_le_iff₀ h.pos]
    calc ‖(ξ : ℂ) + (t : ℂ) * ρ‖ ^ 2 ≤ (2 * C * √t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = 4 * C ^ 2 * t := by
        rw [show (2 * C * √t) ^ 2 = 4 * C ^ 2 * (√t) ^ 2 by ring, Real.sq_sqrt h.pos.le]
  have hA0 : 0 ≤ A := by rw [← hA]; exact div_nonneg (sq_nonneg _) h.pos.le
  have hz' : ‖z‖ ≤ 2 * C ^ 2 * √t := by
    rw [← hzz]
    calc ‖((ξ : ℂ) + (t : ℂ) * ρ) * γ‖ = ‖(ξ : ℂ) + (t : ℂ) * ρ‖ * ‖γ‖ := norm_mul _ _
      _ ≤ (2 * C * √t) * C := mul_le_mul h1 hγ (norm_nonneg _) (by positivity)
      _ = 2 * C ^ 2 * √t := by ring
  rw [e]
  have hq : 1 / 4 ≤ ‖1 + z‖ ^ 2 := by nlinarith
  have hq0 : 0 < ‖1 + z‖ ^ 2 := by linarith
  have key : A / ‖1 + z‖ ^ 2 - A = A * (1 - ‖1 + z‖ ^ 2) / ‖1 + z‖ ^ 2 := by
    field_simp
  rw [key, abs_div, abs_mul, abs_of_nonneg hA0, abs_of_pos hq0, div_le_iff₀ hq0, abs_sub_comm]
  calc A * |‖1 + z‖ ^ 2 - 1| ≤ 4 * C ^ 2 * (3 * (2 * C ^ 2 * √t)) :=
        mul_le_mul ha2 (hz2.trans (by linarith)) (abs_nonneg _) (by positivity)
    _ = 96 * C ^ 4 * √t * (1 / 4) := by ring
    _ ≤ 96 * C ^ 4 * √t * ‖1 + z‖ ^ 2 := by
        have : 0 ≤ 96 * C ^ 4 * √t := by positivity
        exact mul_le_mul_of_nonneg_left hq this

end Pathwise

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Ω → ℝ} {t C : ℝ} {ρ γ : ℂ}

lemma measurable_hc (hξm : Measurable ξ) : Measurable (fun ω => hc t ρ γ (ξ ω)) := by
  unfold hc
  have ha : Measurable (fun ω => (ξ ω : ℂ) + (t : ℂ) * ρ) :=
    (Complex.measurable_ofReal.comp hξm).add_const _
  exact ha.neg.div (measurable_const.mul ((ha.mul_const γ).const_add 1))

lemma norm_sq_a_eq (x : ℝ) : ‖(x : ℂ) + (t : ℂ) * ρ‖ ^ 2 = x ^ 2 + 2 * t * ρ.re * x + t ^ 2 * ‖ρ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.add_im,
    Complex.mul_im]
  ring

/-- Moments of the heat coefficient, eq. `clearing-heat-moments`. -/
theorem heat_moments (hξm : Measurable ξ) (h : Small t C) (hρ : ‖ρ‖ ≤ C) (hγ : ‖γ‖ ≤ C)
    (hξb : ∀ᵐ ω ∂μ, |ξ ω| ≤ C * √t) (η : ℝ) (hm1 : ∫ ω, ξ ω ∂μ = 0)
    (hm2 : ∫ ω, ξ ω ^ 2 ∂μ = t - η) (hη0 : 0 ≤ η) (hη1 : η ≤ C * t ^ 2) :
    (∀ᵐ ω ∂μ, ‖hc t ρ γ (ξ ω)‖ ≤ 4 * C) ∧
    ‖(∫ ω, hc t ρ γ (ξ ω) ∂μ) - ((√t : ℝ) : ℂ) * (γ - ρ)‖ ≤ (C ^ 2 + C ^ 3 + 16 * C ^ 5) * t ∧
    |(∫ ω, ‖hc t ρ γ (ξ ω)‖ ^ 2 ∂μ) - 1| ≤ (C + C ^ 2 + 96 * C ^ 4) * √t := by
  have hs := h.sqrt_pos
  have hC := h.C_nonneg
  have et : t = √t * √t := (Real.mul_self_sqrt h.pos.le).symm
  have hs' : ((√t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hξI : Integrable ξ μ := by
    refine Integrable.of_bound hξm.aestronglyMeasurable (C * √t) ?_
    filter_upwards [hξb] with ω hω; rwa [Real.norm_eq_abs]
  have hξ2I : Integrable (fun ω => ξ ω ^ 2) μ := by
    refine Integrable.of_bound (hξm.pow_const 2).aestronglyMeasurable ((C * √t) ^ 2) ?_
    filter_upwards [hξb] with ω hω
    rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hcm := measurable_hc (t := t) (ρ := ρ) (γ := γ) hξm
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hξb] with ω hω using norm_hc_le h hρ hγ hω
  · -- the mean
    set a : Ω → ℂ := fun ω => (ξ ω : ℂ) + (t : ℂ) * ρ
    have haI : Integrable a μ := (hξI.ofReal).add (integrable_const _)
    have ha2I : Integrable (fun ω => a ω ^ 2) μ := by
      have : (fun ω => a ω ^ 2) = fun ω => ((ξ ω ^ 2 : ℝ) : ℂ) + (2 * (t : ℂ) * ρ) * (ξ ω : ℂ)
          + (t : ℂ) ^ 2 * ρ ^ 2 := by
        funext ω; simp only [a]; push_cast; ring
      rw [this]
      exact ((hξ2I.ofReal).add (hξI.ofReal.const_mul _)).add (integrable_const _)
    have Ea : ∫ ω, a ω ∂μ = (t : ℂ) * ρ := by
      simp only [a]
      rw [integral_add hξI.ofReal (integrable_const _), integral_complex_ofReal, hm1, integral_const,
        probReal_univ, one_smul]; simp
    have Ea2 : ∫ ω, a ω ^ 2 ∂μ = ((t - η : ℝ) : ℂ) + (t : ℂ) ^ 2 * ρ ^ 2 := by
      have : (fun ω => a ω ^ 2) = fun ω => ((ξ ω ^ 2 : ℝ) : ℂ) + (2 * (t : ℂ) * ρ) * (ξ ω : ℂ)
          + (t : ℂ) ^ 2 * ρ ^ 2 := by
        funext ω; simp only [a]; push_cast; ring
      rw [this, integral_add ((hξ2I.ofReal).add (hξI.ofReal.const_mul _)) (integrable_const _),
        integral_add hξ2I.ofReal (hξI.ofReal.const_mul _), integral_complex_ofReal, hm2,
        integral_const_mul, integral_complex_ofReal, hm1, integral_const, probReal_univ, one_smul]
      push_cast; ring
    set L : Ω → ℂ := fun ω => -a ω / ((√t : ℝ) : ℂ) + a ω ^ 2 * γ / ((√t : ℝ) : ℂ)
    have hLI : Integrable L μ := (haI.neg.div_const _).add ((ha2I.mul_const γ).div_const _)
    have EL : ∫ ω, L ω ∂μ = ((√t : ℝ) : ℂ) * (γ - ρ) - γ * (η : ℂ) / ((√t : ℝ) : ℂ)
        + γ * ((t : ℂ) * ((√t : ℝ) : ℂ)) * ρ ^ 2 := by
      simp only [L]
      have i1 : Integrable (fun ω => -a ω / ((√t : ℝ) : ℂ)) μ := haI.neg.div_const _
      have i2 : Integrable (fun ω => a ω ^ 2 * γ / ((√t : ℝ) : ℂ)) μ :=
        (ha2I.mul_const γ).div_const _
      rw [integral_add i1 i2, integral_div, integral_div,
        integral_neg, integral_mul_const, Ea, Ea2]
      have e1 : (t : ℂ) = ((√t : ℝ) : ℂ) * ((√t : ℝ) : ℂ) := by
        rw [← ofReal_mul, Real.mul_self_sqrt h.pos.le]
      push_cast
      rw [e1]
      field_simp
      ring
    have hcI : Integrable (fun ω => hc t ρ γ (ξ ω)) μ :=
      Integrable.of_bound hcm.aestronglyMeasurable (4 * C)
        (by filter_upwards [hξb] with ω hω using norm_hc_le h hρ hγ hω)
    have hR : ‖∫ ω, (hc t ρ γ (ξ ω) - L ω) ∂μ‖ ≤ 16 * C ^ 5 * t := by
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun ω => hc t ρ γ (ξ ω) - L ω) (C := 16 * C ^ 5 * t)
        (by filter_upwards [hξb] with ω hω using norm_hc_sub_le h hρ hγ hω)
      rwa [probReal_univ, mul_one] at this
    rw [integral_sub hcI hLI, EL] at hR
    have hb1 : ‖γ * (η : ℂ) / ((√t : ℝ) : ℂ)‖ ≤ C ^ 2 * t := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hη0,
        Real.norm_of_nonneg hs.le, div_le_iff₀ hs]
      have hk : 0 ≤ C ^ 2 * t := mul_nonneg (sq_nonneg _) h.pos.le
      calc ‖γ‖ * η ≤ C * (C * t ^ 2) := mul_le_mul hγ hη1 hη0 hC
        _ = C ^ 2 * t * t := by ring
        _ ≤ C ^ 2 * t * √t := mul_le_mul_of_nonneg_left h.t_le_sqrt hk
    have hb2 : ‖γ * ((t : ℂ) * ((√t : ℝ) : ℂ)) * ρ ^ 2‖ ≤ C ^ 3 * t := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg h.pos.le, Real.norm_of_nonneg hs.le]
      have hρ2 : ‖ρ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hρ 2
      have h1 : t * √t ≤ t * 1 := mul_le_mul_of_nonneg_left h.sqrt_le_one h.pos.le
      calc ‖γ‖ * (t * √t) * ‖ρ‖ ^ 2 ≤ C * (t * 1) * C ^ 2 :=
            mul_le_mul (mul_le_mul hγ h1 (mul_nonneg h.pos.le hs.le) hC) hρ2 (sq_nonneg _)
              (mul_nonneg hC (by simpa using h.pos.le))
        _ = C ^ 3 * t := by ring
    have : (∫ ω, hc t ρ γ (ξ ω) ∂μ) - ((√t : ℝ) : ℂ) * (γ - ρ)
        = ((∫ ω, hc t ρ γ (ξ ω) ∂μ) - (((√t : ℝ) : ℂ) * (γ - ρ) - γ * (η : ℂ) / ((√t : ℝ) : ℂ)
            + γ * ((t : ℂ) * ((√t : ℝ) : ℂ)) * ρ ^ 2))
          - γ * (η : ℂ) / ((√t : ℝ) : ℂ) + γ * ((t : ℂ) * ((√t : ℝ) : ℂ)) * ρ ^ 2 := by ring
    rw [this]
    set X := (∫ ω, hc t ρ γ (ξ ω) ∂μ) - (((√t : ℝ) : ℂ) * (γ - ρ) - γ * (η : ℂ) / ((√t : ℝ) : ℂ)
            + γ * ((t : ℂ) * ((√t : ℝ) : ℂ)) * ρ ^ 2)
    set Y := γ * (η : ℂ) / ((√t : ℝ) : ℂ)
    set Z := γ * ((t : ℂ) * ((√t : ℝ) : ℂ)) * ρ ^ 2
    have n1 := norm_add_le (X - Y) Z
    have n2 := norm_sub_le X Y
    linarith
  · -- the second moment
    have hc2I : Integrable (fun ω => ‖hc t ρ γ (ξ ω)‖ ^ 2) μ := by
      refine Integrable.of_bound (hcm.norm.pow_const 2).aestronglyMeasurable
        ((4 * C) ^ 2) ?_
      filter_upwards [hξb] with ω hω
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_hc_le h hρ hγ hω) 2
    have hA2I : Integrable (fun ω => ‖(ξ ω : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t) μ := by
      have : (fun ω => ‖(ξ ω : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t)
          = fun ω => (ξ ω ^ 2 + 2 * t * ρ.re * ξ ω + t ^ 2 * ‖ρ‖ ^ 2) / t := by
        funext ω; rw [norm_sq_a_eq]
      rw [this]
      exact ((hξ2I.add (hξI.const_mul _)).add (integrable_const _)).div_const _
    have EA2 : ∫ ω, ‖(ξ ω : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t ∂μ = 1 - η / t + t * ‖ρ‖ ^ 2 := by
      have : (fun ω => ‖(ξ ω : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t)
          = fun ω => (ξ ω ^ 2 + 2 * t * ρ.re * ξ ω + t ^ 2 * ‖ρ‖ ^ 2) / t := by
        funext ω; rw [norm_sq_a_eq]
      have j1 : Integrable (fun ω => ξ ω ^ 2 + 2 * t * ρ.re * ξ ω) μ := hξ2I.add (hξI.const_mul _)
      have j2 : Integrable (fun ω => 2 * t * ρ.re * ξ ω) μ := hξI.const_mul _
      rw [this, integral_div, integral_add j1 (integrable_const _), integral_add hξ2I j2,
        integral_const_mul, hm1, hm2, integral_const, probReal_univ, one_smul]
      have ht0 : t ≠ 0 := h.pos.ne'
      field_simp
      ring
    have hR : |∫ ω, (‖hc t ρ γ (ξ ω)‖ ^ 2 - ‖(ξ ω : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t) ∂μ|
        ≤ 96 * C ^ 4 * √t := by
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun ω => ‖hc t ρ γ (ξ ω)‖ ^ 2 - ‖(ξ ω : ℂ) + (t : ℂ) * ρ‖ ^ 2 / t)
        (C := 96 * C ^ 4 * √t)
        (by filter_upwards [hξb] with ω hω; rw [Real.norm_eq_abs]
            exact abs_norm_hc_sq_sub_le h hρ hγ hω)
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    rw [integral_sub hc2I hA2I, EA2] at hR
    have hb : |-(η / t) + t * ‖ρ‖ ^ 2| ≤ (C + C ^ 2) * √t := by
      have h1 : η / t ≤ C * t := by
        rw [div_le_iff₀ h.pos]; nlinarith
      have h2 : 0 ≤ η / t := div_nonneg hη0 h.pos.le
      have hρ2 : ‖ρ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hρ 2
      have h3 : t * ‖ρ‖ ^ 2 ≤ t * C ^ 2 := mul_le_mul_of_nonneg_left hρ2 h.pos.le
      have h4 : 0 ≤ t * ‖ρ‖ ^ 2 := mul_nonneg h.pos.le (sq_nonneg _)
      have h5 := h.t_le_sqrt
      rw [abs_le]; constructor <;> nlinarith
    have : (∫ ω, ‖hc t ρ γ (ξ ω)‖ ^ 2 ∂μ) - 1
        = ((∫ ω, ‖hc t ρ γ (ξ ω)‖ ^ 2 ∂μ) - (1 - η / t + t * ‖ρ‖ ^ 2))
          + (-(η / t) + t * ‖ρ‖ ^ 2) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith

end Moments

end AndersonAC.L64
