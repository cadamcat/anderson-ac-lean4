import AndersonAC.AgentS6Budget.Exterior
import AndersonAC.AgentS6Budget.Thresholds
import AndersonAC.AgentS6.Stretched

noncomputable section
open Filter Topology

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

theorem exterior_numeric_small (d : ℕ) (K L W Cf cf : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hW : 0 ≤ W) (hCf : 0 ≤ Cf) (hcf : 0 < cf) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (heatLimit t : ℝ) * L * Real.sqrt
        (2 * (Cf * K ^ 3 / t * t ^ (-(d : ℝ)) * Real.exp (-cf * t ^ (-4 : ℤ))) * W) ≤
          Real.sqrt t * entryBudget t / 2 := by
  let p : ℝ := (d : ℝ) + 4 + 2 * eh + (84 / 100) * delta
  let a : ℝ := 8 * L ^ 2 * W * Cf * K ^ 3
  have hev := poly_stretched_small a p cf 4 2 hcf (by norm_num) (by norm_num)
  filter_upwards [hev, self_mem_nhdsWithin] with t htiny ht
  have ht : 0 < t := ht
  have hN : (heatLimit t : ℝ) ≤ t ^ (-1 - eh) := Nat.floor_le (Real.rpow_nonneg ht.le _)
  have hN2 := pow_le_pow_left₀ (Nat.cast_nonneg (heatLimit t)) hN 2
  have he : Real.exp (-t ^ (-(2 : ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (Real.rpow_nonneg ht.le _))
  have hsmall : a * t ^ (-p) * Real.exp (-cf * t ^ (-4 : ℤ)) ≤ 1 := by
    have h := htiny.trans (show (1 / 3 : ℝ) * Real.exp (-t ^ (-(2 : ℝ))) ≤ 1 by linarith)
    rw [← Real.rpow_intCast]
    norm_num only [Int.cast_neg, Int.cast_ofNat]
    exact h
  have hentry : t * entryBudget t ^ 2 = t ^ (1 + (84 / 100) * delta) := by
    unfold entryBudget
    rw [← Real.rpow_natCast (t ^ ((42 / 100) * delta)) 2, ← Real.rpow_mul ht.le,
      mul_comm t, ← Real.rpow_add_one ht.ne']
    congr 1
    push_cast
    ring
  have hident :
      8 * (t ^ (-1 - eh)) ^ 2 * L ^ 2 *
        (Cf * K ^ 3 / t * t ^ (-(d : ℝ)) * Real.exp (-cf * t ^ (-4 : ℤ))) * W =
      (a * t ^ (-p) * Real.exp (-cf * t ^ (-4 : ℤ))) * (t * entryBudget t ^ 2) := by
    rw [hentry]
    rw [show (t ^ (-1 - eh)) ^ 2 = t ^ (2 * (-1 - eh)) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    have hp : -p + (1 + (84 / 100) * delta) = 2 * (-1 - eh) + -1 + -(d : ℝ) := by dsimp [p]; ring
    calc
      _ = a * (t ^ (2 * (-1 - eh)) * t ^ (-1 : ℝ) * t ^ (-(d : ℝ))) *
          Real.exp (-cf * t ^ (-4 : ℤ)) := by dsimp [a]; ring
      _ = a * t ^ (-p + (1 + (84 / 100) * delta)) * Real.exp (-cf * t ^ (-4 : ℤ)) := by
        rw [← Real.rpow_add ht, ← Real.rpow_add ht, hp]
      _ = _ := by rw [Real.rpow_add ht]; ring
  apply (pow_le_pow_iff_left₀ (by positivity) (by unfold entryBudget; positivity)
    (by decide : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), div_pow, mul_pow, Real.sq_sqrt ht.le]
  have hstep := mul_le_mul_of_nonneg_right hN2
    (by positivity : 0 ≤ 8 * L ^ 2 *
      (Cf * K ^ 3 / t * t ^ (-(d : ℝ)) * Real.exp (-cf * t ^ (-4 : ℤ))) * W)
  have hfinal := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ t * entryBudget t ^ 2)
  rw [← hident] at hfinal
  nlinarith

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.exterior_numeric_small
