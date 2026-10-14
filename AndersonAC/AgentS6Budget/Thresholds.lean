import AndersonAC.AgentS6Budget.Numerical

noncomputable section
open Filter Topology

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

theorem heatLimit_one_le {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) : 1 ≤ heatLimit t := by
  have hinv : (2 : ℝ) ≤ t ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, le_inv_comm₀ (by norm_num) ht]
    linarith
  have hpow : t ^ (-1 : ℝ) ≤ t ^ (-1 - eh) :=
    rpow_anti ht (by linarith) (by unfold eh delta; norm_num)
  have hfloor := Nat.lt_floor_add_one (t ^ (-1 - eh))
  have hcast : (1 : ℝ) ≤ (heatLimit t : ℝ) := by unfold heatLimit; linarith
  exact_mod_cast hcast

theorem scaled_entry_le_row_threshold {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.sqrt t * entryBudget t ≤ Real.sqrt (rowBudget t) := by
  apply Real.le_sqrt_of_sq_le
  have hid : (Real.sqrt t * entryBudget t) ^ 2 = t ^ (1 + (84 / 100) * delta) := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    unfold entryBudget
    rw [← Real.rpow_natCast (t ^ ((42 / 100) * delta)) 2, ← Real.rpow_mul ht.le,
      mul_comm t, ← Real.rpow_add_one ht.ne']
    congr 1
    push_cast
    ring
  rw [hid]
  exact rpow_anti ht ht1 (by unfold delta; norm_num)

theorem row_le_frobenius_threshold {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hN : 1 ≤ heatLimit t) : Real.sqrt (rowBudget t) ≤ Real.sqrt (frobeniusBudget t) := by
  apply Real.sqrt_le_sqrt
  have hr : rowBudget t ≤ 1 := rpow_le_one_of ht ht1 (by unfold delta; norm_num)
  have hp : 1 ≤ t ^ (-(1 / 100) * delta) := by
    rw [show (1 : ℝ) = t ^ (0 : ℝ) by simp]
    exact rpow_anti ht ht1 (by unfold delta; norm_num)
  have hN' : (1 : ℝ) ≤ heatLimit t := by exact_mod_cast hN
  exact hr.trans (by
    unfold frobeniusBudget
    nlinarith [mul_nonneg (sub_nonneg.mpr hN') (sub_nonneg.mpr hp)])

theorem budget_bias_quarters (C W : ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      80 * C ^ 5 * t ^ ((21 / 100) * delta) ≤ 1 / 4 ∧
      40 * C ^ 5 * Real.sqrt W * t ^ ((14 / 100) * delta) ≤ 1 / 4 ∧
      20 * C ^ 5 * W * t ^ ((135 / 1000) * delta) ≤ 1 / 4 := by
  have he := rpow_eventually_small (80 * C ^ 5) ((21 / 100) * delta) (1 / 4)
    (by unfold delta; norm_num) (by norm_num)
  have hr := rpow_eventually_small (40 * C ^ 5 * Real.sqrt W) ((14 / 100) * delta) (1 / 4)
    (by unfold delta; norm_num) (by norm_num)
  have hf := rpow_eventually_small (20 * C ^ 5 * W) ((135 / 1000) * delta) (1 / 4)
    (by unfold delta; norm_num) (by norm_num)
  filter_upwards [he, hr, hf] with t he hr hf
  exact ⟨he, hr, hf⟩

theorem entry_variance_ratio {t L : ℝ} (ht : 0 < t) (hL : 0 < L) :
    ((entryBudget t / 2) / 2) ^ 2 / (4 * (L ^ 2 * (16 * fourthCap t / t))) =
      t ^ (-(16 / 100) * delta) / (1024 * L ^ 2) := by
  have hH : fourthCap t ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hid : ((entryBudget t / 2) / 2) ^ 2 / (4 * (L ^ 2 * (16 * fourthCap t / t))) =
      (entryBudget t ^ 2 / (fourthCap t / t)) / (1024 * L ^ 2) := by
    field_simp [ht.ne', hL.ne', hH]
    ring
  rw [hid, (AndersonAC.S6.distortion_margin_identities t ht).1]

theorem entry_jump_ratio {t L : ℝ} (ht : 0 < t) (hL : 0 < L) :
    ((entryBudget t / 2) / 2) / (2 * (L * Real.sqrt (fourthCap t / t))) =
      t ^ (-(8 / 100) * delta) / (8 * L) := by
  have hroot : Real.sqrt (fourthCap t / t) ≠ 0 :=
    (Real.sqrt_pos.mpr (div_pos (Real.rpow_pos_of_pos ht _) ht)).ne'
  have hid : ((entryBudget t / 2) / 2) / (2 * (L * Real.sqrt (fourthCap t / t))) =
      (entryBudget t / Real.sqrt (fourthCap t / t)) / (8 * L) := by
    field_simp [hL.ne', hroot] <;> ring
  rw [hid, (AndersonAC.S6.distortion_margin_identities t ht).2.1]

theorem row_variance_ratio {t L W : ℝ} (ht : 0 < t) (hL : 0 < L) (hW : 0 < W) :
    ((Real.sqrt (rowBudget t) / 2) / 2) ^ 2 /
      (4 * (L ^ 2 * (W * (4 * t ^ ((27 / 100) * delta))))) =
      t ^ (-(2 / 100) * delta) / (256 * L ^ 2 * W) := by
  have hp : t ^ ((27 / 100) * delta) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hrow : 0 ≤ rowBudget t := Real.rpow_nonneg ht.le _
  have hid : ((Real.sqrt (rowBudget t) / 2) / 2) ^ 2 /
      (4 * (L ^ 2 * (W * (4 * t ^ ((27 / 100) * delta))))) =
      (rowBudget t / t ^ ((27 / 100) * delta)) / (256 * L ^ 2 * W) := by
    rw [div_pow, div_pow, Real.sq_sqrt hrow]
    field_simp [hL.ne', hW.ne', hp]
    ring
  rw [hid]
  unfold rowBudget
  rw [← Real.rpow_sub ht]
  congr 2
  ring

theorem frobenius_variance_ratio {t L W : ℝ} (ht : 0 < t) (hL : 0 < L) (hW : 0 < W)
    (hN : 1 ≤ heatLimit t) :
    ((Real.sqrt (frobeniusBudget t) / 2) / 2) ^ 2 /
      (4 * (L ^ 2 * ((heatLimit t : ℝ) * W ^ 2))) =
      t ^ (-(1 / 100) * delta) / (64 * L ^ 2 * W ^ 2) := by
  have hN' : (heatLimit t : ℝ) ≠ 0 := by
    have : (0 : ℝ) < heatLimit t := by exact_mod_cast (by omega : 0 < heatLimit t)
    exact this.ne'
  have hf : 0 ≤ frobeniusBudget t := by unfold frobeniusBudget; positivity
  rw [div_pow, div_pow, Real.sq_sqrt hf]
  unfold frobeniusBudget
  field_simp [hL.ne', hW.ne', hN']
  ring

theorem frobenius_jump_lower {t L W : ℝ} (ht : 0 < t) (hL : 0 < L) (hW : 0 < W)
    (hN : 1 ≤ heatLimit t) :
    t ^ (-budgetConcentrationExponent) / (8 * L * W) ≤
      ((Real.sqrt (frobeniusBudget t) / 2) / 2) / (2 * (L * W)) := by
  have hN' : (1 : ℝ) ≤ heatLimit t := by exact_mod_cast hN
  have hroot : Real.sqrt (t ^ (-(1 / 100) * delta)) ≤ Real.sqrt (frobeniusBudget t) := by
    apply Real.sqrt_le_sqrt
    unfold frobeniusBudget
    exact le_mul_of_one_le_left (Real.rpow_nonneg ht.le _) hN'
  have hid : Real.sqrt (t ^ (-(1 / 100) * delta)) = t ^ (-budgetConcentrationExponent) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    unfold budgetConcentrationExponent
    ring
  rw [hid] at hroot
  calc
    _ ≤ Real.sqrt (frobeniusBudget t) / (8 * L * W) :=
      div_le_div_of_nonneg_right hroot (by positivity)
    _ = _ := by field_simp; ring

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.budget_bias_quarters
#print axioms AndersonAC.AgentS6Budget.frobenius_jump_lower
