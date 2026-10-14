import AndersonAC.AgentS6Budget.Thresholds

noncomputable section

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

theorem row_jump_lower {t L W : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hL : 0 < L) (hW : 0 < W) :
    t ^ (-budgetConcentrationExponent) / (8 * L * Real.sqrt W) ≤
      ((Real.sqrt (rowBudget t) / 2) / 2) / (2 * (L * Real.sqrt (W * Real.sqrt (fourthCap t)))) := by
  have hH : 0 < fourthCap t := Real.rpow_pos_of_pos ht _
  have hRH : 0 < Real.sqrt (Real.sqrt (fourthCap t)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hH)
  have hRW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hsH : Real.sqrt (Real.sqrt (fourthCap t)) = t ^ ((1 + delta) / 4) := by
    unfold fourthCap
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hsR : Real.sqrt (rowBudget t) = t ^ (((25 / 100) * delta) / 2) := by
    unfold rowBudget
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hnum : Real.sqrt (Real.sqrt (fourthCap t)) * t ^ (-budgetConcentrationExponent) ≤
      Real.sqrt (rowBudget t) := by
    rw [hsH, hsR, ← Real.rpow_add ht]
    exact rpow_anti ht ht1 (by unfold budgetConcentrationExponent delta; norm_num)
  calc
    _ = (Real.sqrt (Real.sqrt (fourthCap t)) * t ^ (-budgetConcentrationExponent)) /
        (8 * L * Real.sqrt W * Real.sqrt (Real.sqrt (fourthCap t))) := by
      field_simp [hL.ne', hRW.ne', hRH.ne'] <;> ring
    _ ≤ Real.sqrt (rowBudget t) /
        (8 * L * Real.sqrt W * Real.sqrt (Real.sqrt (fourthCap t))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul hW.le]
      field_simp [hL.ne', hRW.ne', hRH.ne'] <;> ring

/-- The six deterministic reciprocal constants yield one common stretched exponent. -/
theorem distortion_concentration_margins (L W : ℝ) (hL : 0 < L) (hW : 0 < W) :
    ∃ b : ℝ, 0 < b ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → 1 ≤ heatLimit t →
      b * t ^ (-budgetConcentrationExponent) ≤
        min (((entryBudget t / 2) / 2) ^ 2 / (4 * (L ^ 2 * (16 * fourthCap t / t))))
          (((entryBudget t / 2) / 2) / (2 * (L * Real.sqrt (fourthCap t / t)))) ∧
      b * t ^ (-budgetConcentrationExponent) ≤
        min (((Real.sqrt (rowBudget t) / 2) / 2) ^ 2 /
          (4 * (L ^ 2 * (W * (4 * t ^ ((27 / 100) * delta))))))
          (((Real.sqrt (rowBudget t) / 2) / 2) / (2 * (L * Real.sqrt (W * Real.sqrt (fourthCap t))))) ∧
      b * t ^ (-budgetConcentrationExponent) ≤
        min (((Real.sqrt (frobeniusBudget t) / 2) / 2) ^ 2 /
          (4 * (L ^ 2 * ((heatLimit t : ℝ) * W ^ 2))))
          (((Real.sqrt (frobeniusBudget t) / 2) / 2) / (2 * (L * W))) := by
  let KEV : ℝ := 1 / (1024 * L ^ 2)
  let KEJ : ℝ := 1 / (8 * L)
  let KRV : ℝ := 1 / (256 * L ^ 2 * W)
  let KRJ : ℝ := 1 / (8 * L * Real.sqrt W)
  let KFV : ℝ := 1 / (64 * L ^ 2 * W ^ 2)
  let KFJ : ℝ := 1 / (8 * L * W)
  let b := min (min KEV KEJ) (min (min KRV KRJ) (min KFV KFJ))
  have hKEV : 0 < KEV := by dsimp [KEV]; positivity
  have hKEJ : 0 < KEJ := by dsimp [KEJ]; positivity
  have hKRV : 0 < KRV := by dsimp [KRV]; positivity
  have hKRJ : 0 < KRJ := by dsimp [KRJ]; positivity
  have hKFV : 0 < KFV := by dsimp [KFV]; positivity
  have hKFJ : 0 < KFJ := by dsimp [KFJ]; positivity
  refine ⟨b, lt_min (lt_min hKEV hKEJ) (lt_min (lt_min hKRV hKRJ) (lt_min hKFV hKFJ)), ?_⟩
  intro t ht ht1 hN
  have hbEV : b ≤ KEV := (min_le_left _ _).trans (min_le_left _ _)
  have hbEJ : b ≤ KEJ := (min_le_left _ _).trans (min_le_right _ _)
  have hbRV : b ≤ KRV := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hbRJ : b ≤ KRJ := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hbFV : b ≤ KFV := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hbFJ : b ≤ KFJ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hlower : ∀ K a : ℝ, b ≤ K → 0 ≤ K → budgetConcentrationExponent ≤ a →
      b * t ^ (-budgetConcentrationExponent) ≤ K * t ^ (-a) := by
    intro K a hb hK ha
    exact (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ht.le _)).trans
      (mul_le_mul_of_nonneg_left (rpow_anti ht ht1 (by linarith)) hK)
  refine ⟨le_min ?_ ?_, le_min ?_ ?_, le_min ?_ ?_⟩
  · rw [entry_variance_ratio ht hL]
    have h := hlower KEV ((16 / 100) * delta) hbEV hKEV.le
      (by unfold budgetConcentrationExponent delta; norm_num)
    simpa only [KEV, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg, neg_mul] using h
  · rw [entry_jump_ratio ht hL]
    have h := hlower KEJ ((8 / 100) * delta) hbEJ hKEJ.le
      (by unfold budgetConcentrationExponent delta; norm_num)
    simpa only [KEJ, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg, neg_mul] using h
  · rw [row_variance_ratio ht hL hW]
    have h := hlower KRV ((2 / 100) * delta) hbRV hKRV.le
      (by unfold budgetConcentrationExponent delta; norm_num)
    simpa only [KRV, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg, neg_mul] using h
  · apply le_trans (mul_le_mul_of_nonneg_right hbRJ (Real.rpow_nonneg ht.le _))
    simpa only [KRJ, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg, neg_mul] using row_jump_lower ht ht1 hL hW
  · rw [frobenius_variance_ratio ht hL hW hN]
    have h := hlower KFV ((1 / 100) * delta) hbFV hKFV.le
      (by unfold budgetConcentrationExponent delta; norm_num)
    simpa only [KFV, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg, neg_mul] using h
  · apply le_trans (mul_le_mul_of_nonneg_right hbFJ (Real.rpow_nonneg ht.le _))
    simpa only [KFJ, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg, neg_mul] using frobenius_jump_lower ht hL hW hN

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.distortion_concentration_margins
