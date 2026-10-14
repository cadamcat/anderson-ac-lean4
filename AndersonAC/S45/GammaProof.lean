import AndersonAC.S45.Definitions

set_option maxHeartbeats 1000000

noncomputable section

namespace AndersonAC.AgentS45

open AndersonAC.S45
open MeasureTheory ProbabilityTheory

theorem physical_decay_proof : ∀ (C a : ℝ), 0 < C → 0 < a →
    ∃ c > 0, ∃ C' > 0, ∃ t0 > 0,
    ∀ (t r dT : ℝ) (z : ℂ), 0 < t → t < t0 → 0 ≤ r →
    dT ≥ r / 2 - power t (-103 / 100) →
    ‖z‖ ≤ C / Real.sqrt t → ‖z‖ ≤ C / Real.sqrt t * Real.exp (-a * t * dT) →
    ‖z‖ ≤ C' / Real.sqrt t * Real.exp (-c * t^3 * r) := by
  intro C a hC ha
  refine ⟨a / 4, by positivity, C * Real.exp a, by positivity, 1, by norm_num, ?_⟩
  intro t r dT z ht htt hr hd hrough hdec
  have ht_le : t ≤ 1 := htt.le
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have ht2pos : 0 < t ^ 2 := pow_pos ht 2
  have hpower : power t (-103 / 100) ≤ 1 / t ^ 2 := by
    dsimp [power]
    calc
      Real.rpow t (-103 / 100) ≤ Real.rpow t (-2) :=
        Real.rpow_le_rpow_of_exponent_ge ht ht_le (by norm_num)
      _ = 1 / t ^ 2 := by
        simpa [Real.rpow_natCast, one_div] using (Real.rpow_neg ht.le (2 : ℝ))
  have hexpa : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha.le
  by_cases hsmall : r ≤ 4 / t ^ 2
  · have ht3r : t ^ 3 * r ≤ 4 * t := by
      calc
        t ^ 3 * r ≤ t ^ 3 * (4 / t ^ 2) := mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = 4 * t := by field_simp [ne_of_gt ht]
    have ht3r_le : t ^ 3 * r ≤ 4 := by nlinarith [ht3r]
    have hsmallExp : (a / 4) * t ^ 3 * r ≤ a := by
      have hm := mul_le_mul_of_nonneg_left ht3r_le (by positivity : 0 ≤ a / 4)
      nlinarith [hm]
    have hexpSmall : 1 ≤ Real.exp (a - (a / 4) * t ^ 3 * r) :=
      Real.one_le_exp_iff.mpr (sub_nonneg.mpr hsmallExp)
    have hexpFactor : Real.exp a * Real.exp (-(a / 4) * t ^ 3 * r) =
        Real.exp (a - (a / 4) * t ^ 3 * r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      ‖z‖ ≤ C / Real.sqrt t := hrough
      _ = (C / Real.sqrt t) * 1 := by ring
      _ ≤ (C / Real.sqrt t) * Real.exp (a - (a / 4) * t ^ 3 * r) :=
        mul_le_mul_of_nonneg_left hexpSmall (by positivity)
      _ = C * Real.exp a / Real.sqrt t * Real.exp (-(a / 4) * t ^ 3 * r) := by
        rw [← hexpFactor]
        ring
  · have hlarge : 4 / t ^ 2 < r := lt_of_not_ge hsmall
    have hquarter : 1 / t ^ 2 < r / 4 := by
      calc
        1 / t ^ 2 = (1 / 4) * (4 / t ^ 2) := by field_simp [ne_of_gt ht2pos]
        _ < (1 / 4) * r := mul_lt_mul_of_pos_left hlarge (by norm_num)
        _ = r / 4 := by ring
    have hpowquarter : power t (-103 / 100) ≤ r / 4 := hpower.trans hquarter.le
    have hdquarter : r / 4 ≤ dT := by linarith
    have ht2le : t ^ 2 ≤ t := by
      have hm := mul_le_mul_of_nonneg_left ht_le ht.le
      nlinarith [hm]
    have ht2le1 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht_le
    have ht3le : t ^ 3 ≤ t := by
      calc
        t ^ 3 = t * t ^ 2 := by ring
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left ht2le1 ht.le
        _ = t := by ring
    have hcoefNonneg : 0 ≤ (a / 4) * r := mul_nonneg (by positivity) hr
    have hcoef := mul_le_mul_of_nonneg_right ht3le hcoefNonneg
    have hscale : (a / 4) * t ^ 3 * r ≤ a * t * dT := by
      have hm := mul_le_mul_of_nonneg_left hdquarter (mul_nonneg ha.le ht.le)
      nlinarith [hcoef, hm]
    have hexpDecay : Real.exp (-a * t * dT) ≤ Real.exp (-(a / 4) * t ^ 3 * r) :=
      Real.exp_le_exp.mpr (by nlinarith [hscale])
    have hcoeff : C / Real.sqrt t ≤ C * Real.exp a / Real.sqrt t := by
      apply div_le_div_of_nonneg_right ?_ hsqrt.le
      simpa using mul_le_mul_of_nonneg_left hexpa hC.le
    calc
      ‖z‖ ≤ C / Real.sqrt t * Real.exp (-a * t * dT) := hdec
      _ ≤ C / Real.sqrt t * Real.exp (-(a / 4) * t ^ 3 * r) :=
        mul_le_mul_of_nonneg_left hexpDecay (by positivity)
      _ ≤ C * Real.exp a / Real.sqrt t * Real.exp (-(a / 4) * t ^ 3 * r) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)

theorem ae_bound_integral_norm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → E) (K : ℝ)
    (hf : Integrable f μ) (hK : 0 ≤ K)
    (hb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ K) : ‖∫ ω, f ω ∂μ‖ ≤ K := by
  calc
    ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, ‖f ω‖ ∂μ := norm_integral_le_integral_norm f
    _ ≤ ∫ _ω, K ∂μ := integral_mono_ae hf.norm (integrable_const K) hb
    _ = K := by simp

theorem gamma_pointwise_bounds {P : Type*} [Fintype P] [DecidableEq P]
    (C t ε η y : ℝ) (s : State P) (x : P)
    (hC : 1 ≤ C) (ht : 0 < t) (heps_pos : 0 < ε) (heps_le : ε ≤ 1)
    (heps_small : ε < (4 * C ^ 2)⁻¹) (heps_sq : ε ^ 2 = t)
    (heta : ε * η = y) (heta_bound : |η| ≤ C)
    (hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ C) :
    (1 + ((y : ℂ) + (t : ℂ) * s.r x) * s.g x x ≠ 0) ∧
    ‖gamma t s x y‖ ≤ 4 * C ∧
    ‖gamma t s x y - ((η : ℂ) + (ε : ℂ) *
      (s.r x - s.g x x * (η : ℂ) ^ 2))‖ ≤ 10 * C ^ 5 * t ∧
    ‖gamma t s x y - (η : ℂ)‖ ≤ 6 * C ^ 3 * ε ∧
    ‖gamma t s x y ^ 2 - (η : ℂ) ^ 2‖ ≤ 30 * C ^ 4 * ε ∧
    |‖gamma t s x y‖ ^ 2 - η ^ 2| ≤ 30 * C ^ 4 * ε := by
  let g : ℂ := s.g x x
  let r : ℂ := s.r x
  let ec : ℂ := (ε : ℂ)
  let eη : ℂ := (η : ℂ)
  let u : ℂ := eη + ec * r
  let p : ℂ := ((y : ℂ) + (t : ℂ) * r) * g
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hC2 : 1 ≤ C ^ 2 := (one_le_pow₀ hC : 1 ≤ C ^ 2)
  have hCpow13 : C ≤ C ^ 3 := by
    calc
      C = C * 1 := by ring
      _ ≤ C * C ^ 2 := mul_le_mul_of_nonneg_left hC2 hCpos.le
      _ = C ^ 3 := by ring
  have hCpow35 : C ^ 3 ≤ C ^ 5 := pow_le_pow_right₀ hC (by norm_num)
  have hgC : ‖g‖ ≤ C := by linarith [norm_nonneg r]
  have hrC : ‖r‖ ≤ C := by linarith [norm_nonneg g]
  have heps_sqrt : (Real.sqrt t : ℝ) = ε := by
    rw [← heps_sq, Real.sqrt_sq heps_pos.le]
  have heps_le_t : t ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left heps_le heps_pos.le
    rw [← heps_sq]
    nlinarith [hm]
  have hepsC : (1 : ℝ) ≤ 4 * C ^ 2 := by nlinarith [hC2]
  have hηc : ec * eη = (y : ℂ) := by
    dsimp [ec, eη]
    exact_mod_cast heta
  have htC : (t : ℂ) = ec ^ 2 := by
    dsimp [ec]
    exact_mod_cast heps_sq.symm
  have hnum : (y : ℂ) + (t : ℂ) * r = ec * u := by
    calc
      (y : ℂ) + (t : ℂ) * r = ec * eη + ec ^ 2 * r := by rw [← hηc, htC]
      _ = ec * (eη + ec * r) := by ring
      _ = ec * u := by rfl
  have hDform : 1 + p = 1 + ec * u * g := by
    dsimp [p]
    rw [hnum]
  have hηnorm : ‖eη‖ ≤ C := by
    simpa [eη, Complex.norm_real] using heta_bound
  have hyNorm : ‖(y : ℂ)‖ ≤ C * ε := by
    rw [show y = ε * η from heta.symm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rw [abs_of_pos heps_pos]
    nlinarith [mul_le_mul_of_nonneg_right heta_bound heps_pos.le]
  have huNorm : ‖u‖ ≤ 2 * C := by
    calc
      ‖u‖ ≤ ‖eη‖ + ‖ec * r‖ := norm_add_le _ _
      _ ≤ C + ε * C := add_le_add hηnorm (by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps_pos]
        exact mul_le_mul_of_nonneg_left hrC heps_pos.le)
      _ ≤ 2 * C := by
        have hm := mul_le_mul_of_nonneg_left heps_le hCpos.le
        nlinarith [hm]
  have htrNorm : ‖(t : ℂ) * r‖ ≤ t * C := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hrC ht.le
  have hnumNorm : ‖(y : ℂ) + (t : ℂ) * r‖ ≤ 2 * C * ε := by
    calc
      ‖(y : ℂ) + (t : ℂ) * r‖ ≤ ‖(y : ℂ)‖ + ‖(t : ℂ) * r‖ := norm_add_le _ _
      _ ≤ C * ε + t * C := add_le_add hyNorm htrNorm
      _ ≤ 2 * C * ε := by nlinarith [mul_le_mul_of_nonneg_right heps_le hCpos.le]
  have hpNorm : ‖p‖ ≤ 2 * C ^ 2 * ε := by
    dsimp [p]
    rw [norm_mul]
    calc
      ‖(y : ℂ) + (t : ℂ) * r‖ * ‖g‖ ≤ (2 * C * ε) * C :=
        mul_le_mul hnumNorm hgC (norm_nonneg _) (by positivity)
      _ = 2 * C ^ 2 * ε := by ring
  have hpSmall : ‖p‖ < 1 / 2 := by
    calc
      ‖p‖ ≤ 2 * C ^ 2 * ε := hpNorm
      _ < 2 * C ^ 2 * (4 * C ^ 2)⁻¹ :=
        mul_lt_mul_of_pos_left heps_small (by positivity)
      _ = 1 / 2 := by field_simp [ne_of_gt hCpos] <;> norm_num
  have hden : 1 + p ≠ 0 := by
    intro hd
    have hpEq : p = -(1 : ℂ) := by linear_combination hd
    have hpOne : ‖p‖ = 1 := by rw [hpEq]; simp
    linarith
  have hdenLower : 1 / 2 ≤ ‖1 + p‖ := by
    have htriangle : 1 ≤ ‖1 + p‖ + ‖p‖ := by
      calc
        1 = ‖(1 : ℂ)‖ := by simp
        _ = ‖(1 + p) - p‖ := by congr 1 <;> ring
        _ ≤ ‖1 + p‖ + ‖p‖ := norm_sub_le _ _
    linarith
  have hdenPos : 0 < ‖1 + p‖ := by linarith
  have hdenInv : ‖(1 + p)⁻¹‖ ≤ 2 := by
    have h := (div_le_iff₀ hdenPos).2 (by nlinarith [hdenLower] : 1 ≤ 2 * ‖1 + p‖)
    simpa [norm_inv, one_div] using h
  have hden' : 1 + ec * u * g ≠ 0 := by rw [← hDform]; exact hden
  have hgamma : gamma t s x y = u / (1 + p) := by
    dsimp [gamma]
    rw [heps_sqrt, hnum]
    have hepsComplexNe : (ε : ℂ) ≠ 0 := by exact_mod_cast heps_pos.ne'
    rw [hDform]
    dsimp [ec, g] at hden' ⊢
    field_simp [hepsComplexNe, hden']
  have hgammaBound : ‖gamma t s x y‖ ≤ 4 * C := by
    rw [hgamma, div_eq_mul_inv, norm_mul]
    calc
      ‖u‖ * ‖(1 + p)⁻¹‖ ≤ (2 * C) * 2 :=
        mul_le_mul huNorm hdenInv (norm_nonneg _) (by positivity)
      _ = 4 * C := by ring
  have hBnorm : ‖r - g * eη ^ 2‖ ≤ 2 * C ^ 3 := by
    have hηsq : ‖eη ^ 2‖ ≤ C ^ 2 := by
      rw [norm_pow]
      have hm := mul_le_mul hηnorm hηnorm (norm_nonneg _) (by positivity)
      nlinarith [hm]
    have hmul := mul_le_mul hgC hηsq (norm_nonneg _) (by positivity)
    have hCpow := mul_le_mul_of_nonneg_left hC2 hCpos.le
    calc
      ‖r - g * eη ^ 2‖ ≤ ‖r‖ + ‖g * eη ^ 2‖ := norm_sub_le _ _
      _ ≤ C + C ^ 3 := by rw [norm_mul]; nlinarith [hrC, hmul]
      _ ≤ 2 * C ^ 3 := by nlinarith [hCpow]
  have hηrg : ‖eη * r * g‖ ≤ C ^ 3 := by
    rw [norm_mul, norm_mul]
    calc
      ‖eη‖ * ‖r‖ * ‖g‖ ≤ C * C * C := by gcongr
      _ = C ^ 3 := by ring
  have hBug : ‖(r - g * eη ^ 2) * u * g‖ ≤ 4 * C ^ 5 := by
    rw [norm_mul, norm_mul]
    calc
      ‖r - g * eη ^ 2‖ * ‖u‖ * ‖g‖ ≤ (2 * C ^ 3) * (2 * C) * C := by gcongr
      _ = 4 * C ^ 5 := by ring
  have hErrNum : ‖eη * r * g + (r - g * eη ^ 2) * u * g‖ ≤ 5 * C ^ 5 := by
    calc
      ‖eη * r * g + (r - g * eη ^ 2) * u * g‖ ≤
          ‖eη * r * g‖ + ‖(r - g * eη ^ 2) * u * g‖ := norm_add_le _ _
      _ ≤ C ^ 3 + 4 * C ^ 5 := add_le_add hηrg hBug
      _ ≤ 5 * C ^ 5 := by nlinarith [hCpow35]
  have hfirst : gamma t s x y - eη - ec * (r - g * eη ^ 2) =
      -(ec ^ 2) * (eη * r * g + (r - g * eη ^ 2) * u * g) / (1 + p) := by
    rw [hgamma, hDform]
    dsimp [u] at hden' ⊢
    field_simp [hden']
    ring
  have hfirstNorm : ‖gamma t s x y - eη - ec * (r - g * eη ^ 2)‖ ≤ 10 * C ^ 5 * t := by
    rw [hfirst, div_eq_mul_inv, norm_mul, norm_mul, norm_neg, norm_pow]
    have hecNorm : ‖ec‖ = ε := by simp [ec, abs_of_pos heps_pos]
    rw [hecNorm]
    calc
      ε ^ 2 * ‖eη * r * g + (r - g * eη ^ 2) * u * g‖ * ‖(1 + p)⁻¹‖ ≤
          ε ^ 2 * (5 * C ^ 5 * 2) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul hErrNum hdenInv (norm_nonneg _) (by positivity)) (sq_nonneg ε)
      _ = 10 * C ^ 5 * t := by rw [heps_sq]; ring
  have hminus : gamma t s x y - eη =
      ec * ((r - g * eη ^ 2) - ec * eη * r * g) / (1 + p) := by
    rw [hgamma, hDform]
    dsimp [u] at hden' ⊢
    field_simp [hden']
    ring
  have hminusNum : ‖(r - g * eη ^ 2) - ec * eη * r * g‖ ≤ 3 * C ^ 3 := by
    have hmul : ‖ec * eη * r * g‖ ≤ ε * C ^ 3 := by
      rw [norm_mul, norm_mul, norm_mul]
      have hecNorm : ‖ec‖ = ε := by simp [ec, abs_of_pos heps_pos]
      rw [hecNorm]
      calc
        ε * ‖eη‖ * ‖r‖ * ‖g‖ ≤ ε * C * C * C := by gcongr
        _ = ε * C ^ 3 := by ring
    calc
      ‖(r - g * eη ^ 2) - ec * eη * r * g‖ ≤
          ‖r - g * eη ^ 2‖ + ‖ec * eη * r * g‖ := norm_sub_le _ _
      _ ≤ 2 * C ^ 3 + ε * C ^ 3 := add_le_add hBnorm hmul
      _ ≤ 2 * C ^ 3 + C ^ 3 := add_le_add le_rfl
        (by simpa using mul_le_mul_of_nonneg_right heps_le (pow_nonneg hCpos.le 3))
      _ = 3 * C ^ 3 := by ring
  have hminusNorm : ‖gamma t s x y - eη‖ ≤ 6 * C ^ 3 * ε := by
    rw [hminus, div_eq_mul_inv, norm_mul, norm_mul]
    have hecNorm : ‖ec‖ = ε := by simp [ec, abs_of_pos heps_pos]
    rw [hecNorm]
    calc
      ε * ‖(r - g * eη ^ 2) - ec * eη * r * g‖ * ‖(1 + p)⁻¹‖ ≤
          ε * (3 * C ^ 3 * 2) :=
        by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul hminusNum hdenInv (norm_nonneg _) (by positivity)) heps_pos.le
      _ = 6 * C ^ 3 * ε := by ring
  have hsum : ‖gamma t s x y‖ + ‖eη‖ ≤ 5 * C := by
    calc
      ‖gamma t s x y‖ + ‖eη‖ ≤ 4 * C + C := add_le_add hgammaBound hηnorm
      _ = 5 * C := by ring
  have hsumReal : ‖gamma t s x y‖ + |η| ≤ 5 * C := by
    simpa [eη, Complex.norm_real] using hsum
  have hcomplexSq : ‖gamma t s x y ^ 2 - eη ^ 2‖ ≤ 30 * C ^ 4 * ε := by
    calc
      ‖gamma t s x y ^ 2 - eη ^ 2‖ =
          ‖gamma t s x y - eη‖ * ‖gamma t s x y + eη‖ := by
            rw [show gamma t s x y ^ 2 - eη ^ 2 =
              (gamma t s x y - eη) * (gamma t s x y + eη) by ring, norm_mul]
      _ ≤ (6 * C ^ 3 * ε) * (5 * C) :=
        mul_le_mul hminusNorm (by
          calc
            ‖gamma t s x y + eη‖ ≤ ‖gamma t s x y‖ + ‖eη‖ := norm_add_le _ _
            _ ≤ 5 * C := hsum) (norm_nonneg _) (by positivity)
      _ = 30 * C ^ 4 * ε := by ring
  have hnormDiff : abs (‖gamma t s x y‖ - |η|) ≤ ‖gamma t s x y - eη‖ := by
    simpa [eη, Complex.norm_real] using abs_norm_sub_norm_le (gamma t s x y) eη
  have hrealSq : |‖gamma t s x y‖ ^ 2 - η ^ 2| ≤ 30 * C ^ 4 * ε := by
    have hfactor : ‖gamma t s x y‖ ^ 2 - η ^ 2 =
        (‖gamma t s x y‖ - |η|) * (‖gamma t s x y‖ + |η|) := by
      rw [← sq_abs η]
      ring
    calc
      abs (‖gamma t s x y‖ ^ 2 - η ^ 2) =
          abs (‖gamma t s x y‖ - |η|) * abs (‖gamma t s x y‖ + |η|) := by
        rw [hfactor, abs_mul]
      _ ≤ ‖gamma t s x y - eη‖ * (‖gamma t s x y‖ + |η|) := by
        rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (abs_nonneg _))]
        exact mul_le_mul hnormDiff (le_of_eq rfl)
          (add_nonneg (norm_nonneg _) (abs_nonneg _)) (by positivity)
      _ ≤ (6 * C ^ 3 * ε) * (5 * C) :=
        mul_le_mul hminusNorm hsumReal
          (add_nonneg (norm_nonneg _) (abs_nonneg _)) (by positivity)
      _ = 30 * C ^ 4 * ε := by ring
  refine ⟨?_, hgammaBound, ?_, hminusNorm, hcomplexSq, hrealSq⟩
  · change 1 + p ≠ 0
    exact hden
  · change ‖gamma t s x y - (eη + ec * (r - g * eη ^ 2))‖ ≤ 10 * C ^ 5 * t
    have heq : gamma t s x y - (eη + ec * (r - g * eη ^ 2)) =
        gamma t s x y - eη - ec * (r - g * eη ^ 2) := by ring
    rw [heq]
    exact hfirstNorm

theorem gamma_moments_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P) (x : P)
    (ξ : Ω → ℝ),
    0 < t → t < t0 → ‖s.g x x‖ + ‖s.r x‖ ≤ C → MomentLaw μ t C ξ →
    (∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ ≤ C' ∧
      1 + ((ξ ω : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧
    ‖(∫ ω, gamma t s x (ξ ω) ∂μ) + s.z t x‖ ≤ C' * t ∧
    ‖(∫ ω, gamma t s x (ξ ω) ^ 2 ∂μ) - 1‖ ≤ C' * Real.sqrt t ∧
    |(∫ ω, ‖gamma t s x (ξ ω)‖ ^ 2 ∂μ) - 1| ≤ C' * Real.sqrt t := by
  intro C hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨100 * C ^ 5, by positivity, (4 * C ^ 2)⁻¹ ^ 2, by positivity, ?_⟩
  intro P Ω instFintype instDecidable instMeas μ instProb t s x ξ ht htt hstate hM
  let ε : ℝ := Real.sqrt t
  let η : Ω → ℝ := fun ω => ξ ω / ε
  let ηc : Ω → ℂ := fun ω => (η ω : ℂ)
  let γ : Ω → ℂ := fun ω => gamma t s x (ξ ω)
  have hεpos : 0 < ε := Real.sqrt_pos.2 ht
  have hC2 : 1 ≤ C ^ 2 := (one_le_pow₀ hC : 1 ≤ C ^ 2)
  have hthrPos : 0 < (4 * C ^ 2)⁻¹ := by positivity
  have hthrLe : (4 * C ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [hC2])
  have hsqrtlt : Real.sqrt t < Real.sqrt (((4 * C ^ 2)⁻¹) ^ 2) :=
    (Real.sqrt_lt_sqrt_iff ht.le).2 htt
  have hεsmall : ε < (4 * C ^ 2)⁻¹ := by
    dsimp [ε]
    calc
      Real.sqrt t < Real.sqrt (((4 * C ^ 2)⁻¹) ^ 2) := hsqrtlt
      _ = (4 * C ^ 2)⁻¹ := Real.sqrt_sq hthrPos.le
  have hεle : ε ≤ 1 := (le_of_lt hεsmall).trans hthrLe
  have hεsq : ε ^ 2 = t := by simpa [ε] using Real.sq_sqrt ht.le
  have hηbound : ∀ᵐ ω ∂μ, |η ω| ≤ C := by
    filter_upwards [hM.bounded] with ω hω
    have hω' : |ξ ω| ≤ C * ε := by simpa [ε] using hω
    have hdiv : |ξ ω| / ε ≤ C := (div_le_iff₀ hεpos).2 (by nlinarith [hω'])
    simpa [η, abs_div, abs_of_pos hεpos] using hdiv
  have heta (ω : Ω) : ε * η ω = ξ ω := by
    dsimp [η]
    field_simp [ne_of_gt hεpos]
  have hpoint : ∀ᵐ ω ∂μ,
      (1 + ((ξ ω : ℂ) + (t : ℂ) * s.r x) * s.g x x ≠ 0) ∧
      ‖gamma t s x (ξ ω)‖ ≤ 4 * C ∧
      ‖gamma t s x (ξ ω) - ((η ω : ℂ) + (ε : ℂ) *
        (s.r x - s.g x x * (η ω : ℂ) ^ 2))‖ ≤ 10 * C ^ 5 * t ∧
      ‖gamma t s x (ξ ω) - (η ω : ℂ)‖ ≤ 6 * C ^ 3 * ε ∧
      ‖gamma t s x (ξ ω) ^ 2 - (η ω : ℂ) ^ 2‖ ≤ 30 * C ^ 4 * ε ∧
      |‖gamma t s x (ξ ω)‖ ^ 2 - η ω ^ 2| ≤ 30 * C ^ 4 * ε := by
    filter_upwards [hηbound] with ω hω
    exact gamma_pointwise_bounds C t ε (η ω) (ξ ω) s x hC ht hεpos hεle
      hεsmall hεsq (heta ω) hω hstate
  have hC15 : C ≤ C ^ 5 := by
    calc
      C = C ^ 1 := by simp
      _ ≤ C ^ 5 := pow_le_pow_right₀ hC (by norm_num)
  have hgammaCoeff : 4 * C ≤ 100 * C ^ 5 := by nlinarith [hC15]
  have hpair : ∀ᵐ ω ∂μ,
      ‖gamma t s x (ξ ω)‖ ≤ 100 * C ^ 5 ∧
        1 + ((ξ ω : ℂ) + t * s.r x) * s.g x x ≠ 0 := by
    filter_upwards [hpoint] with ω hp
    rcases hp with ⟨hd, hγ, hTaylor, hminus, hsq, hnormsq⟩
    exact ⟨hγ.trans hgammaCoeff, hd⟩
  have hηmeas : Measurable η := hM.measurable.div_const ε
  have hξmeas : Measurable ξ := hM.measurable
  have hηmeasC : Measurable ηc := by
    dsimp [ηc]
    fun_prop
  have hγmeas : Measurable γ := by
    dsimp [γ, gamma]
    fun_prop
  have hηnormBound : ∀ᵐ ω ∂μ, ‖η ω‖ ≤ C := by
    filter_upwards [hηbound] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hηint : Integrable η μ :=
    Integrable.of_bound hηmeas.aestronglyMeasurable C hηnormBound
  have hηsqBound : ∀ᵐ ω ∂μ, ‖η ω ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [hηnormBound] with ω hω
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg (η ω)) (by positivity)).2 hω
  have hηsqMeas : Measurable (fun ω => η ω ^ 2) := by fun_prop
  have hηsqInt : Integrable (fun ω => η ω ^ 2) μ :=
    Integrable.of_bound hηsqMeas.aestronglyMeasurable (C ^ 2) hηsqBound
  have hηcInt : Integrable ηc μ := by
    apply Integrable.of_bound hηmeasC.aestronglyMeasurable C
    filter_upwards [hηbound] with ω hω
    simpa [ηc, Complex.norm_real] using hω
  have hηcSqBound : ∀ᵐ ω ∂μ, ‖ηc ω ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [hηbound] with ω hω
    have hω' : ‖ηc ω‖ ≤ C := by simpa [ηc, Complex.norm_real] using hω
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg (ηc ω)) (by positivity)).2 hω'
  have hηcSqMeas : Measurable (fun ω => ηc ω ^ 2) := by fun_prop
  have hηcSqInt : Integrable (fun ω => ηc ω ^ 2) μ :=
    Integrable.of_bound hηcSqMeas.aestronglyMeasurable (C ^ 2) hηcSqBound
  have hηmean : (∫ ω, η ω ∂μ) = 0 := by
    simp [η, div_eq_mul_inv, integral_mul_const, hM.mean]
  have hηsqMean : (∫ ω, η ω ^ 2 ∂μ) = 1 := by
    have hfun : (fun ω => η ω ^ 2) = fun ω => ξ ω ^ 2 / ε ^ 2 := by
      funext ω
      simp [η, div_pow]
    rw [hfun]
    simp only [div_eq_mul_inv, integral_mul_const]
    rw [hM.variance, hεsq]
    exact div_self ht.ne'
  have hηcMean : (∫ ω, ηc ω ∂μ) = 0 := by
    dsimp [ηc]
    rw [integral_complex_ofReal, hηmean]
    norm_num
  have hηcSqMean : (∫ ω, ηc ω ^ 2 ∂μ) = 1 := by
    have hfun : ∀ ω, ηc ω ^ 2 = Complex.ofReal (η ω ^ 2) := by
      intro ω
      dsimp [ηc]
      rw [← Complex.ofReal_pow]
    calc
      (∫ ω, ηc ω ^ 2 ∂μ) = ∫ ω, Complex.ofReal (η ω ^ 2) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hfun)
      _ = (∫ ω, η ω ^ 2 ∂μ : ℝ) := integral_complex_ofReal
      _ = 1 := by rw [hηsqMean]; norm_num
  let b : Ω → ℂ := fun ω => s.r x - s.g x x * ηc ω ^ 2
  let base : Ω → ℂ := fun ω => ηc ω + (ε : ℂ) * b ω
  let err : Ω → ℂ := fun ω => γ ω - ηc ω - (ε : ℂ) * b ω
  have hbMeas : Measurable b := by
    dsimp [b]
    fun_prop
  have hbInt : Integrable b μ := by
    dsimp [b]
    exact (integrable_const (s.r x)).sub (hηcSqInt.const_mul (s.g x x))
  have hbMean : (∫ ω, b ω ∂μ) = s.r x - s.g x x := by
    dsimp [b]
    rw [integral_sub (integrable_const (s.r x)) (hηcSqInt.const_mul (s.g x x))]
    rw [integral_const_mul (s.g x x) (fun ω => ηc ω ^ 2), hηcSqMean]
    simp
  have hbaseInt : Integrable base μ := by
    dsimp [base]
    exact hηcInt.add (hbInt.const_mul (ε : ℂ))
  have hbaseMean : (∫ ω, base ω ∂μ) = (ε : ℂ) * (s.r x - s.g x x) := by
    dsimp [base]
    rw [integral_add hηcInt (hbInt.const_mul (ε : ℂ)), integral_const_mul]
    simp [hηcMean, hbMean]
  have herrMeas : Measurable err := by
    dsimp [err]
    fun_prop
  have herrBound : ∀ᵐ ω ∂μ, ‖err ω‖ ≤ 10 * C ^ 5 * t := by
    filter_upwards [hpoint] with ω hp
    rcases hp with ⟨hd, hγ, hTaylor, hminus, hsq, hnormsq⟩
    have heq : err ω = gamma t s x (ξ ω) - ((η ω : ℂ) + (ε : ℂ) *
        (s.r x - s.g x x * (η ω : ℂ) ^ 2)) := by
      dsimp [err, γ, ηc, b]
      ring
    rw [heq]
    exact hTaylor
  have herrInt : Integrable err μ :=
    Integrable.of_bound herrMeas.aestronglyMeasurable (10 * C ^ 5 * t) herrBound
  have hdecomp : γ =ᵐ[μ] fun ω => base ω + err ω := by
    filter_upwards [] with ω
    dsimp [γ, base, err, ηc, b]
    ring
  have hγmean : (∫ ω, γ ω ∂μ) =
      (ε : ℂ) * (s.r x - s.g x x) + ∫ ω, err ω ∂μ := by
    calc
      (∫ ω, γ ω ∂μ) = ∫ ω, base ω + err ω ∂μ := integral_congr_ae hdecomp
      _ = (∫ ω, base ω ∂μ) + ∫ ω, err ω ∂μ := integral_add hbaseInt herrInt
      _ = (ε : ℂ) * (s.r x - s.g x x) + ∫ ω, err ω ∂μ := by rw [hbaseMean]
  have hZ : s.z t x = (ε : ℂ) * (s.g x x - s.r x) := by
    simp [State.z, State.rawLag, ε, smul_eq_mul]
  have hmeanTarget : (∫ ω, γ ω ∂μ) + s.z t x = ∫ ω, err ω ∂μ := by
    rw [hγmean, hZ]
    ring
  have herrIntegralBound : ‖∫ ω, err ω ∂μ‖ ≤ 10 * C ^ 5 * t :=
    ae_bound_integral_norm μ err (10 * C ^ 5 * t) herrInt (by positivity) herrBound
  have hmeanFinal : ‖(∫ ω, γ ω ∂μ) + s.z t x‖ ≤ 100 * C ^ 5 * t := by
    rw [hmeanTarget]
    calc
      ‖∫ ω, err ω ∂μ‖ ≤ 10 * C ^ 5 * t := herrIntegralBound
      _ ≤ 100 * C ^ 5 * t := by nlinarith [mul_nonneg (pow_nonneg hCpos.le 5) ht.le]
  let sqErr : Ω → ℂ := fun ω => γ ω ^ 2 - ηc ω ^ 2
  have hsqErrMeas : Measurable sqErr := by
    dsimp [sqErr]
    fun_prop
  have hsqErrBound : ∀ᵐ ω ∂μ, ‖sqErr ω‖ ≤ 30 * C ^ 4 * ε := by
    filter_upwards [hpoint] with ω hp
    rcases hp with ⟨hd, hγ, hTaylor, hminus, hsq, hnormsq⟩
    simpa [sqErr, γ, ηc, Complex.ofReal_pow] using hsq
  have hsqErrInt : Integrable sqErr μ :=
    Integrable.of_bound hsqErrMeas.aestronglyMeasurable (30 * C ^ 4 * ε) hsqErrBound
  have hγsqBound : ∀ᵐ ω ∂μ, ‖γ ω ^ 2‖ ≤ (4 * C) ^ 2 := by
    filter_upwards [hpoint] with ω hp
    rcases hp with ⟨hd, hγ, hTaylor, hminus, hsq, hnormsq⟩
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg (γ ω)) (by positivity)).2 hγ
  have hγsqMeas : Measurable (fun ω => γ ω ^ 2) := by fun_prop
  have hγsqInt : Integrable (fun ω => γ ω ^ 2) μ :=
    Integrable.of_bound hγsqMeas.aestronglyMeasurable ((4 * C) ^ 2) hγsqBound
  have hsqId : (∫ ω, sqErr ω ∂μ) = (∫ ω, γ ω ^ 2 ∂μ) - 1 := by
    dsimp [sqErr]
    rw [integral_sub hγsqInt hηcSqInt, hηcSqMean]
  have hsqIntegralBound : ‖∫ ω, sqErr ω ∂μ‖ ≤ 30 * C ^ 4 * ε :=
    ae_bound_integral_norm μ sqErr (30 * C ^ 4 * ε) hsqErrInt (by positivity) hsqErrBound
  have hC45 : C ^ 4 ≤ C ^ 5 := pow_le_pow_right₀ hC (by norm_num)
  have hC45coeff : 30 * C ^ 4 ≤ 100 * C ^ 5 := by nlinarith [hC45]
  have hsqFinal : ‖(∫ ω, γ ω ^ 2 ∂μ) - 1‖ ≤ 100 * C ^ 5 * ε := by
    calc
      ‖(∫ ω, γ ω ^ 2 ∂μ) - 1‖ = ‖∫ ω, sqErr ω ∂μ‖ := by rw [← hsqId]
      _ ≤ 30 * C ^ 4 * ε := hsqIntegralBound
      _ ≤ 100 * C ^ 5 * ε := mul_le_mul_of_nonneg_right hC45coeff hεpos.le
  let realErr : Ω → ℝ := fun ω => ‖γ ω‖ ^ 2 - η ω ^ 2
  have hrealErrMeas : Measurable realErr := by
    dsimp [realErr]
    fun_prop
  have hrealErrBound : ∀ᵐ ω ∂μ, ‖realErr ω‖ ≤ 30 * C ^ 4 * ε := by
    filter_upwards [hpoint] with ω hp
    rcases hp with ⟨hd, hγ, hTaylor, hminus, hsq, hnormsq⟩
    simpa [realErr, γ, Real.norm_eq_abs] using hnormsq
  have hrealErrInt : Integrable realErr μ :=
    Integrable.of_bound hrealErrMeas.aestronglyMeasurable (30 * C ^ 4 * ε) hrealErrBound
  have hrealSqMeas : Measurable (fun ω => ‖γ ω‖ ^ 2) := by fun_prop
  have hrealSqBound : ∀ᵐ ω ∂μ, ‖‖γ ω‖ ^ 2‖ ≤ (4 * C) ^ 2 := by
    filter_upwards [hpoint] with ω hp
    rcases hp with ⟨hd, hγ, hTaylor, hminus, hsq, hnormsq⟩
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ ‖γ ω‖ ^ 2 := sq_nonneg _
    rw [abs_of_nonneg hnonneg]
    exact (sq_le_sq₀ (norm_nonneg (γ ω)) (by positivity)).2 hγ
  have hrealSqInt : Integrable (fun ω => ‖γ ω‖ ^ 2) μ :=
    Integrable.of_bound hrealSqMeas.aestronglyMeasurable ((4 * C) ^ 2) hrealSqBound
  have hrealId : (∫ ω, realErr ω ∂μ) =
      (∫ ω, ‖γ ω‖ ^ 2 ∂μ) - 1 := by
    dsimp [realErr]
    rw [integral_sub hrealSqInt hηsqInt, hηsqMean]
  have hrealIntegralBound : ‖∫ ω, realErr ω ∂μ‖ ≤ 30 * C ^ 4 * ε :=
    ae_bound_integral_norm μ realErr (30 * C ^ 4 * ε) hrealErrInt (by positivity) hrealErrBound
  have hrealFinal : |(∫ ω, ‖γ ω‖ ^ 2 ∂μ) - 1| ≤ 100 * C ^ 5 * ε := by
    calc
      |(∫ ω, ‖γ ω‖ ^ 2 ∂μ) - 1| = ‖∫ ω, realErr ω ∂μ‖ := by
        rw [← hrealId, Real.norm_eq_abs]
      _ ≤ 30 * C ^ 4 * ε := hrealIntegralBound
      _ ≤ 100 * C ^ 5 * ε := mul_le_mul_of_nonneg_right hC45coeff hεpos.le
  exact ⟨hpair, by simpa [γ, ε] using hmeanFinal,
    by simpa [γ, ε] using hsqFinal, by simpa [γ, ε] using hrealFinal⟩

end AndersonAC.AgentS45
