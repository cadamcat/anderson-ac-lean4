import AndersonAC.S78.Definitions

/-!
# Scale facts at a clearing stage

`t = t_j = u 4^{-j} + u 4^{-m}` with `u ∈ (1/4, 1]` and `j + 2 ≤ m`:
`(1/4) 4^{-j} < t ≤ (17/16) 4^{-j}`; hence `ℓ_j = 4^{4j}` satisfies
`t^{-4}/256 ≤ ℓ_j ≤ 2 t^{-4}` (06-clearing.tex:760–764, `ℓ ≍ t^{-4}`), and a snapshot
component of at most `t^{-ν}` sites with diameter `≤ |B| R_j` lies in a ball of radius
`t^{-9}` once `j ≥ 9` (06-clearing.tex:765–766, 07-assembly.tex:202–203).
-/

set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Geo

open AndersonAC.S78

theorem stage_t_bounds (u : ℝ) (j m : ℕ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j + 2 ≤ m) :
    (1 / 4 : ℝ) / (4 : ℝ) ^ j < stageScale u j m ∧
      stageScale u j m ≤ (17 / 16 : ℝ) / (4 : ℝ) ^ j := by
  obtain ⟨hu1, hu2⟩ := hu
  have hX : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
  have hY : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have hXY : (4 : ℝ) ^ j * 16 ≤ (4 : ℝ) ^ m := by
    have : (4 : ℝ) ^ m = (4 : ℝ) ^ j * 4 ^ (m - j) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hX.le
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ (m - j) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold stageScale
  constructor
  · have h1 : (1 / 4 : ℝ) / (4 : ℝ) ^ j < u / (4 : ℝ) ^ j := div_lt_div_of_pos_right hu1 hX
    have h2 : 0 < u / (4 : ℝ) ^ m := div_pos (by linarith) hY
    linarith
  · have h1 : u / (4 : ℝ) ^ j ≤ 1 / (4 : ℝ) ^ j := div_le_div_of_nonneg_right hu2 hX.le
    have h2 : u / (4 : ℝ) ^ m ≤ (1 / 16) / (4 : ℝ) ^ j := by
      rw [div_le_div_iff₀ hY hX]
      nlinarith
    have h3 : (1 : ℝ) / (4 : ℝ) ^ j + (1 / 16) / (4 : ℝ) ^ j = (17 / 16) / (4 : ℝ) ^ j := by ring
    linarith

theorem stage_t_pos (u : ℝ) (j m : ℕ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j + 2 ≤ m) :
    0 < stageScale u j m :=
  lt_trans (by positivity) (stage_t_bounds u j m hu hjm).1

theorem stage_t_le (u : ℝ) (j m : ℕ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j + 2 ≤ m) :
    stageScale u j m ≤ 2 / (4 : ℝ) ^ j := by
  refine (stage_t_bounds u j m hu hjm).2.trans ?_
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem stage_t_le_one (u : ℝ) (j m : ℕ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j + 2 ≤ m)
    (hj : 1 ≤ j) : stageScale u j m ≤ 1 := by
  refine (stage_t_le u j m hu hjm).trans ?_
  rw [div_le_one (by positivity)]
  calc (2 : ℝ) ≤ 4 ^ 1 := by norm_num
    _ ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hj

theorem stage_ell_bounds (u : ℝ) (j m : ℕ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j + 2 ≤ m) :
    (1 / 256) * stageScale u j m ^ (-4 : ℤ) ≤ inspectionRadius j ∧
      inspectionRadius j ≤ 2 * stageScale u j m ^ (-4 : ℤ) := by
  obtain ⟨hlo, hhi⟩ := stage_t_bounds u j m hu hjm
  set t := stageScale u j m
  set X : ℝ := (4 : ℝ) ^ j
  have hX : 0 < X := by positivity
  have ht : 0 < t := lt_trans (by positivity) hlo
  have hR : inspectionRadius j = X ^ 4 := by
    unfold inspectionRadius; rw [← pow_mul, mul_comm]
  have hzt : t ^ (-4 : ℤ) = (t ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [hR, hzt]
  have hXt1 : 1 / 4 < X * t := by
    rw [div_lt_iff₀ hX] at hlo; nlinarith
  have hXt2 : X * t ≤ 17 / 16 := by
    rw [le_div_iff₀ hX] at hhi; nlinarith
  have ht4 : 0 < t ^ 4 := by positivity
  constructor
  · rw [← div_eq_mul_inv, div_le_iff₀ ht4]
    have : (1 : ℝ) ≤ 256 * (X * t) ^ 4 := by
      have h := pow_le_pow_left₀ (by norm_num) hXt1.le 4
      nlinarith
    nlinarith [show (X * t) ^ 4 = X ^ 4 * t ^ 4 by ring]
  · rw [← div_eq_mul_inv, le_div_iff₀ ht4]
    have h := pow_le_pow_left₀ (by positivity) hXt2 4
    have : (X * t) ^ 4 ≤ 2 := h.trans (by norm_num)
    nlinarith [show (X * t) ^ 4 = X ^ 4 * t ^ 4 by ring]

theorem stage_core_radius (u : ℝ) (j m d : ℕ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (hjm : j + 2 ≤ m) (hj : 9 ≤ j) (hd : 1 ≤ d) (D : ℝ)
    (hD : D ≤ stageScale u j m ^ (-nu d) * separationRadius j) :
    D ≤ stageScale u j m ^ (-(9 : ℝ)) := by
  set t := stageScale u j m
  have ht : 0 < t := stage_t_pos u j m hu hjm
  have htle : t ≤ 2 / (4 : ℝ) ^ j := stage_t_le u j m hu hjm
  set X : ℝ := (4 : ℝ) ^ j
  have hX : 0 < X := by positivity
  have hX9 : (4 : ℝ) ^ 9 ≤ X := pow_le_pow_right₀ (by norm_num) hj
  have ht16 : t ≤ (1 / 65536 : ℝ) := by
    refine htle.trans ?_
    rw [div_le_iff₀ hX]; nlinarith
  have ht1 : t ≤ 1 := ht16.trans (by norm_num)
  have hnu : nu d ≤ 1 / 2 := by
    unfold nu delta
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_iff₀ (by positivity)]; nlinarith
  -- t^{-ν} ≤ t^{-1/2}
  have h1 : t ^ (-nu d) ≤ t ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  -- R_j = X^8 ≤ 256 t^{-8}
  have hXt : X * t ≤ 2 := by rw [le_div_iff₀ hX] at htle; linarith
  have hR : separationRadius j = X ^ 8 := by
    unfold separationRadius; rw [← pow_mul, mul_comm]
  have h2 : X ^ 8 ≤ 256 * t ^ (-(8 : ℝ)) := by
    rw [Real.rpow_neg ht.le, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (by positivity) hXt 8
    nlinarith [show (X * t) ^ 8 = X ^ 8 * t ^ 8 by ring]
  -- 256 ≤ t^{-1/2}
  have h3 : (256 : ℝ) ≤ t ^ (-(1 / 2 : ℝ)) := by
    have hs : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
    rw [hs, le_inv_comm₀ (by norm_num) (Real.sqrt_pos.mpr ht)]
    rw [Real.sqrt_le_left (by norm_num)]
    calc t ≤ 1 / 65536 := ht16
      _ = (256⁻¹) ^ 2 := by norm_num
  have hcomb : t ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) * t ^ (-(8 : ℝ)) = t ^ (-(9 : ℝ)) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]; norm_num
  have hpos8 : 0 ≤ t ^ (-(8 : ℝ)) := by positivity
  calc D ≤ t ^ (-nu d) * separationRadius j := hD
    _ ≤ t ^ (-(1 / 2 : ℝ)) * (256 * t ^ (-(8 : ℝ))) := by
        rw [hR]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ t ^ (-(1 / 2 : ℝ)) * (t ^ (-(1 / 2 : ℝ)) * t ^ (-(8 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right h3 hpos8
    _ = t ^ (-(9 : ℝ)) := by rw [← hcomb]; ring

end AndersonAC.AgentS78Geo
