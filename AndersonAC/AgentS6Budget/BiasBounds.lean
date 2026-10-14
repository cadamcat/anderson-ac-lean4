import AndersonAC.AgentS6Budget.Thresholds

noncomputable section

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

theorem heatLimit_rpow_le {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (heatLimit t : ℝ) * t ^ a ≤ t ^ (-1 - eh + a) := by
  have hN : (heatLimit t : ℝ) ≤ t ^ (-1 - eh) := Nat.floor_le (Real.rpow_nonneg ht.le _)
  exact (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg ht.le _)).trans
    (Real.rpow_add ht _ _).symm.le

theorem heat_fourth_root_bound {t : ℝ} (ht : 0 < t) :
    Real.sqrt ((heatLimit t : ℝ) * fourthCap t) ≤ t ^ ((27 / 100) * delta) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Real.rpow_nonneg ht.le _, ?_⟩
  have h := heatLimit_rpow_le ht (1 + delta)
  unfold fourthCap
  rw [← Real.rpow_natCast (t ^ ((27 / 100) * delta)) 2, ← Real.rpow_mul ht.le]
  convert h using 1
  congr 1
  unfold eh
  push_cast
  ring

theorem entry_bias_factor_bound {t : ℝ} (ht : 0 < t) :
    Real.sqrt t * t ^ betaW * Real.sqrt ((heatLimit t : ℝ) * (16 * fourthCap t / t)) ≤
      4 * t ^ ((63 / 100) * delta) := by
  have hH : 0 < fourthCap t := Real.rpow_pos_of_pos ht _
  have hid : Real.sqrt t * Real.sqrt ((heatLimit t : ℝ) * (16 * fourthCap t / t)) =
      4 * Real.sqrt ((heatLimit t : ℝ) * fourthCap t) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow]
    rw [Real.sq_sqrt ht.le, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp [ht.ne'] <;> ring
  calc
    _ = 4 * t ^ betaW * Real.sqrt ((heatLimit t : ℝ) * fourthCap t) := by rw [mul_right_comm, hid]; ring
    _ ≤ 4 * t ^ betaW * t ^ ((27 / 100) * delta) :=
      mul_le_mul_of_nonneg_left (heat_fourth_root_bound ht) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add ht]
      congr 1
      unfold betaW
      ring

theorem row_bias_factor_bound {t W : ℝ} (ht : 0 < t) (hW : 0 ≤ W) :
    Real.sqrt t * t ^ betaW *
      Real.sqrt ((heatLimit t : ℝ) * (W * (4 * t ^ ((27 / 100) * delta)))) ≤
      2 * Real.sqrt W * t ^ ((265 / 1000) * delta) := by
  let Z := t * (heatLimit t : ℝ) * t ^ ((27 / 100) * delta)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hZsup : Z ≤ t ^ ((27 / 100) * delta - eh) := by
    calc
      Z = (heatLimit t : ℝ) * t ^ ((27 / 100) * delta + 1) := by
        rw [Real.rpow_add_one ht.ne']
        dsimp [Z]
        ring
      _ ≤ t ^ (-1 - eh + ((27 / 100) * delta + 1)) := heatLimit_rpow_le ht _
      _ = _ := by congr 1; ring
  have hroot : Real.sqrt Z ≤ t ^ (((27 / 100) * delta - eh) / 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨Real.rpow_nonneg ht.le _, ?_⟩
    rw [← Real.rpow_natCast (t ^ (((27 / 100) * delta - eh) / 2)) 2, ← Real.rpow_mul ht.le]
    convert hZsup using 1
    congr 1
    push_cast
    ring
  have hid : Real.sqrt t *
      Real.sqrt ((heatLimit t : ℝ) * (W * (4 * t ^ ((27 / 100) * delta)))) =
      2 * Real.sqrt W * Real.sqrt Z := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow]
    rw [Real.sq_sqrt ht.le, Real.sq_sqrt (by positivity), Real.sq_sqrt hW, Real.sq_sqrt hZ]
    dsimp [Z]
    ring
  calc
    _ = 2 * Real.sqrt W * t ^ betaW * Real.sqrt Z := by rw [mul_right_comm, hid]; ring
    _ ≤ 2 * Real.sqrt W * t ^ betaW * t ^ (((27 / 100) * delta - eh) / 2) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add ht]
      congr 1
      unfold betaW eh
      ring

theorem frobenius_bias_factor_bound {t W : ℝ} (ht : 0 < t) (hW : 0 ≤ W) :
    Real.sqrt t * t ^ betaW * Real.sqrt ((heatLimit t : ℝ) * ((heatLimit t : ℝ) * W ^ 2)) ≤
      W * t ^ ((135 / 1000) * delta) * Real.sqrt (frobeniusBudget t) := by
  have hN0 : (0 : ℝ) ≤ heatLimit t := Nat.cast_nonneg _
  have hTN : t * (heatLimit t : ℝ) ≤ t ^ (-eh) := by
    simpa only [Real.rpow_one, show -1 - eh + (1 : ℝ) = -eh by ring, mul_comm] using heatLimit_rpow_le ht 1
  have hroot : Real.sqrt (t * (heatLimit t : ℝ)) ≤ t ^ (-eh / 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨Real.rpow_nonneg ht.le _, ?_⟩
    rw [← Real.rpow_natCast (t ^ (-eh / 2)) 2, ← Real.rpow_mul ht.le]
    convert hTN using 1
    congr 1
    push_cast
    ring
  have hNN : Real.sqrt ((heatLimit t : ℝ) * ((heatLimit t : ℝ) * W ^ 2)) = (heatLimit t : ℝ) * W := by
    rw [show (heatLimit t : ℝ) * ((heatLimit t : ℝ) * W ^ 2) = ((heatLimit t : ℝ) * W) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg hN0 hW)
  have hsplit : Real.sqrt t * (heatLimit t : ℝ) =
      Real.sqrt (t * (heatLimit t : ℝ)) * Real.sqrt (heatLimit t : ℝ) := by
    rw [Real.sqrt_mul ht.le, mul_assoc, Real.mul_self_sqrt hN0]
  have hf : Real.sqrt (frobeniusBudget t) = Real.sqrt (heatLimit t : ℝ) * t ^ (-delta / 200) := by
    unfold frobeniusBudget
    rw [Real.sqrt_mul hN0, Real.sqrt_eq_rpow (t ^ (-(1 / 100) * delta)), ← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [hNN]
  calc
    _ = W * t ^ betaW * (Real.sqrt t * (heatLimit t : ℝ)) := by ring
    _ = W * t ^ betaW * (Real.sqrt (t * (heatLimit t : ℝ)) * Real.sqrt (heatLimit t : ℝ)) := by rw [hsplit]
    _ = W * Real.sqrt (heatLimit t : ℝ) * t ^ betaW * Real.sqrt (t * (heatLimit t : ℝ)) := by ring
    _ ≤ W * Real.sqrt (heatLimit t : ℝ) * t ^ betaW * t ^ (-eh / 2) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by
      rw [hf, mul_assoc, ← Real.rpow_add ht]
      have he : betaW + -eh / 2 = (135 / 1000) * delta + -delta / 200 := by unfold betaW eh; ring
      rw [he, Real.rpow_add ht]
      ring

theorem bias_below_quarter (C W : ℝ) (hC : 0 ≤ C) (hW : 0 ≤ W) {t : ℝ} (ht : 0 < t)
    (he : 80 * C ^ 5 * t ^ ((21 / 100) * delta) ≤ 1 / 4)
    (hr : 40 * C ^ 5 * Real.sqrt W * t ^ ((14 / 100) * delta) ≤ 1 / 4)
    (hf : 20 * C ^ 5 * W * t ^ ((135 / 1000) * delta) ≤ 1 / 4) :
    (20 * C ^ 5 * Real.sqrt t * t ^ betaW) *
      Real.sqrt ((heatLimit t : ℝ) * (16 * fourthCap t / t)) ≤ (entryBudget t / 2) / 2 ∧
    (20 * C ^ 5 * Real.sqrt t * t ^ betaW) *
      Real.sqrt ((heatLimit t : ℝ) * (W * (4 * t ^ ((27 / 100) * delta)))) ≤
        (Real.sqrt (rowBudget t) / 2) / 2 ∧
    (20 * C ^ 5 * Real.sqrt t * t ^ betaW) *
      Real.sqrt ((heatLimit t : ℝ) * ((heatLimit t : ℝ) * W ^ 2)) ≤
        (Real.sqrt (frobeniusBudget t) / 2) / 2 := by
  have h20 : 0 ≤ 20 * C ^ 5 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (20 * C ^ 5) * (Real.sqrt t * t ^ betaW * Real.sqrt ((heatLimit t : ℝ) * (16 * fourthCap t / t))) := by ring
      _ ≤ (20 * C ^ 5) * (4 * t ^ ((63 / 100) * delta)) := mul_le_mul_of_nonneg_left (entry_bias_factor_bound ht) h20
      _ = entryBudget t * (80 * C ^ 5 * t ^ ((21 / 100) * delta)) := by
        unfold entryBudget
        rw [show (63 / 100) * delta = (42 / 100) * delta + (21 / 100) * delta by ring, Real.rpow_add ht]
        ring
      _ ≤ entryBudget t * (1 / 4) := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
      _ = _ := by ring
  · calc
      _ = (20 * C ^ 5) * (Real.sqrt t * t ^ betaW *
          Real.sqrt ((heatLimit t : ℝ) * (W * (4 * t ^ ((27 / 100) * delta))))) := by ring
      _ ≤ (20 * C ^ 5) * (2 * Real.sqrt W * t ^ ((265 / 1000) * delta)) :=
        mul_le_mul_of_nonneg_left (row_bias_factor_bound ht hW) h20
      _ = Real.sqrt (rowBudget t) * (40 * C ^ 5 * Real.sqrt W * t ^ ((14 / 100) * delta)) := by
        unfold rowBudget
        rw [Real.sqrt_eq_rpow (t ^ ((25 / 100) * delta)), ← Real.rpow_mul ht.le,
          show (265 / 1000) * delta = ((25 / 100) * delta) * (1 / 2) + (14 / 100) * delta by ring,
          Real.rpow_add ht]
        ring
      _ ≤ Real.sqrt (rowBudget t) * (1 / 4) := mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      _ = (20 * C ^ 5) * (Real.sqrt t * t ^ betaW *
          Real.sqrt ((heatLimit t : ℝ) * ((heatLimit t : ℝ) * W ^ 2))) := by ring
      _ ≤ (20 * C ^ 5) * (W * t ^ ((135 / 1000) * delta) * Real.sqrt (frobeniusBudget t)) :=
        mul_le_mul_of_nonneg_left (frobenius_bias_factor_bound ht hW) h20
      _ = Real.sqrt (frobeniusBudget t) * (20 * C ^ 5 * W * t ^ ((135 / 1000) * delta)) := by ring
      _ ≤ Real.sqrt (frobeniusBudget t) * (1 / 4) := mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg _)
      _ = _ := by ring

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.bias_below_quarter
