import AndersonAC.S2.Definitions

/-! The exact scale normalization and weak-coupling cutoff in §2. -/

noncomputable section

namespace AndersonAC.SolS2
open AndersonAC.S2

theorem four_pow_eq_two_pow_sq (n : ℕ) : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
  calc
    (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
    _ = ((2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]

theorem initialScale_pow_bounds {coupling : ℝ} (hc : 0 < coupling) (hc₁ : coupling < 1) :
    (4 : ℝ) ^ initialScale coupling ≤ 3 / coupling ^ 2 ∧
      3 / coupling ^ 2 < (4 : ℝ) ^ (initialScale coupling + 1) := by
  have hc2 : 0 < coupling ^ 2 := sq_pos_of_pos hc
  have hx : 1 < 3 / coupling ^ 2 := by
    apply (lt_div_iff₀ hc2).mpr
    nlinarith
  have hx0 : 0 < 3 / coupling ^ 2 := by positivity
  have hlog : 0 ≤ Real.logb 4 (3 / coupling ^ 2) :=
    (Real.logb_pos (by norm_num : (1 : ℝ) < 4) hx).le
  have hlo : (initialScale coupling : ℝ) ≤ Real.logb 4 (3 / coupling ^ 2) := by
    simpa [initialScale, Real.logb] using Nat.floor_le hlog
  have hhi : Real.logb 4 (3 / coupling ^ 2) < ((initialScale coupling + 1 : ℕ) : ℝ) := by
    simpa [initialScale, Real.logb] using Nat.lt_floor_add_one (Real.logb 4 (3 / coupling ^ 2))
  constructor
  · simpa only [Real.rpow_natCast] using
      (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 4) hx0).mp hlo
  · simpa only [Real.rpow_natCast] using
      (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 4) hx0).mp hhi

theorem le_initialScale_of_pow_le {coupling : ℝ} (hc : 0 < coupling) (k : ℕ)
    (hpow : (4 : ℝ) ^ k ≤ 3 / coupling ^ 2) : k ≤ initialScale coupling := by
  apply Nat.le_floor
  change (k : ℝ) ≤ Real.logb 4 (3 / coupling ^ 2)
  exact (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 4) (by positivity)).mpr
    (by simpa only [Real.rpow_natCast] using hpow)

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2

theorem scaleU_mem {coupling : ℝ} (hcoupling : 0 < coupling) (hcoupling₁ : coupling < 1) :
    scaleU coupling ∈ Set.Ioc (1 / 4 : ℝ) 1 := by
  have hc2 : 0 < coupling ^ 2 := sq_pos_of_pos hcoupling
  obtain ⟨hlo, hhi⟩ := initialScale_pow_bounds hcoupling hcoupling₁
  have hlo' := (le_div_iff₀ hc2).mp hlo
  have hhi' := (div_lt_iff₀ hc2).mp hhi
  rw [pow_succ] at hhi'
  constructor <;> unfold scaleU <;> nlinarith

theorem varianceScale_eq {coupling : ℝ} (n : ℕ) :
    varianceScale coupling n = coupling ^ 2 / 3 * (4 : ℝ) ^
      ((initialScale coupling : ℤ) - (n : ℤ)) := by
  rw [varianceScale, scaleU, zpow_sub₀ (by norm_num : (4 : ℝ) ≠ 0)]
  simp only [zpow_natCast]
  ring

theorem scales_comparable {coupling : ℝ} (hcoupling : 0 < coupling) (hcoupling₁ : coupling < 1)
    {m n : ℕ} (hn : n ≤ m) :
    (1 / 4 : ℝ) / 4 ^ n < varianceScale coupling n ∧
    varianceScale coupling n ≤ 1 / (4 : ℝ) ^ n ∧
    (1 / 4 : ℝ) / 4 ^ n < dampingScale coupling m n ∧
    dampingScale coupling m n ≤ 2 / (4 : ℝ) ^ n := by
  have hu := scaleU_mem hcoupling hcoupling₁
  have hlow : (1 / 4 : ℝ) / 4 ^ n < varianceScale coupling n :=
    div_lt_div_of_pos_right hu.1 (by positivity)
  have hupp : varianceScale coupling n ≤ 1 / (4 : ℝ) ^ n :=
    div_le_div_of_nonneg_right hu.2 (by positivity)
  have hmupp : varianceScale coupling m ≤ 1 / (4 : ℝ) ^ m :=
    div_le_div_of_nonneg_right hu.2 (by positivity)
  have hpow : (4 : ℝ) ^ n ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hn
  have hrec : 1 / (4 : ℝ) ^ m ≤ 1 / (4 : ℝ) ^ n :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hmupp' := hmupp.trans hrec
  have hmpos : 0 < varianceScale coupling m := by
    unfold varianceScale
    exact div_pos (lt_trans (by norm_num) hu.1) (by positivity)
  refine ⟨hlow, hupp, ?_, ?_⟩
  · unfold dampingScale finalHeight
    linarith
  · unfold dampingScale finalHeight
    calc
      varianceScale coupling n + varianceScale coupling m ≤
          1 / (4 : ℝ) ^ n + 1 / (4 : ℝ) ^ n := add_le_add hupp hmupp'
      _ = 2 / (4 : ℝ) ^ n := by ring

theorem initialScale_arbitrarily_large (k : ℕ) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ coupling : ℝ, 0 < coupling → coupling < lambda0 →
      k ≤ initialScale coupling := by
  refine ⟨Real.sqrt 3 / (2 : ℝ) ^ k, by positivity, ?_⟩
  intro coupling hc hk
  have hc2 : 0 < coupling ^ 2 := sq_pos_of_pos hc
  have hmul : coupling * (2 : ℝ) ^ k < Real.sqrt 3 :=
    (lt_div_iff₀ (by positivity)).mp hk
  have hsq : (coupling * (2 : ℝ) ^ k) ^ 2 < 3 := by
    have h := (sq_lt_sq₀ (by positivity : 0 ≤ coupling * (2 : ℝ) ^ k)
      (Real.sqrt_nonneg 3)).mpr hmul
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using h
  apply le_initialScale_of_pow_le hc k
  apply (le_div_iff₀ hc2).mpr
  rw [four_pow_eq_two_pow_sq]
  nlinarith

theorem scaleCoupling_eq {coupling : ℝ} (hcoupling : 0 < coupling) :
    OAI.Anderson.scaleCoupling (initialScale coupling) (scaleU coupling) = coupling := by
  have hrel : 3 * scaleU coupling = (coupling * (2 : ℝ) ^ initialScale coupling) ^ 2 := by
    unfold scaleU
    rw [four_pow_eq_two_pow_sq]
    ring
  rw [OAI.Anderson.scaleCoupling, hrel, Real.sqrt_sq (by positivity)]
  exact mul_div_cancel_right₀ coupling (by positivity)

end AndersonAC.S2
