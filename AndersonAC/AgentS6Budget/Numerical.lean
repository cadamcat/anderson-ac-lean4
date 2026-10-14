import AndersonAC.AgentS6.Margins
import AndersonAC.L64.Residual

noncomputable section
open Filter Topology

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

def budgetConcentrationExponent : ℝ := delta / 200

theorem clearingExponent_lt_budgetConcentrationExponent (d : ℕ) (hd : 3 ≤ d) :
    clearingExponent d < budgetConcentrationExponent := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hnu : 0 < nu d := by unfold nu delta; positivity
  unfold clearingExponent budgetConcentrationExponent eh e0
  linarith

theorem rpow_eventually_small (A a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), A * t ^ a ≤ b := by
  have hlim := (tendsto_rpow_zero ha).const_mul A
  have h := (tendsto_order.mp hlim).2 b (by simpa using hb)
  exact h.mono fun _ h => h.le

theorem small_of_t_le {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 1 ≤ C)
    (htC : t ≤ 1 / (16 * C ^ 4)) : AndersonAC.L64.Small t C := by
  have hC0 : 0 ≤ C := by linarith
  have hden : 0 < 16 * C ^ 4 := by positivity
  have hprod := (le_div_iff₀ hden).mp htC
  have hsq : (4 * C ^ 2 * Real.sqrt t) ^ 2 ≤ 1 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht.le]
    nlinarith
  refine ⟨ht, ht1, hC0, ?_⟩
  nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * C ^ 2) (Real.sqrt_nonneg t)]

theorem monitoring_card_polynomial (d : ℕ) (K Cloc : ℝ) (hK : 0 ≤ K) (hCloc : 0 ≤ Cloc)
    {t ell X : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hell0 : 0 ≤ ell)
    (hell : ell ≤ 2 * t ^ (-4 : ℤ))
    (hX : X ≤ K * (1 + (t ^ (-Cloc) + (ell / 2 + t ^ (-5 : ℤ) + 1))) ^ d) :
    X ≤ K * 5 ^ d * t ^ (-(d : ℝ) * (Cloc + 5)) := by
  let T : ℝ := t ^ (-(Cloc + 5))
  have hT : 0 < T := Real.rpow_pos_of_pos ht _
  have h1 : 1 ≤ T := by
    rw [show (1 : ℝ) = t ^ (0 : ℝ) by simp]
    exact rpow_anti ht ht1 (by linarith)
  have hloc : t ^ (-Cloc) ≤ T := rpow_anti ht ht1 (by linarith)
  have h4 : t ^ (-4 : ℤ) ≤ T := by
    rw [← Real.rpow_intCast]
    apply rpow_anti ht ht1
    norm_num
    linarith
  have h5 : t ^ (-5 : ℤ) ≤ T := by
    rw [← Real.rpow_intCast]
    apply rpow_anti ht ht1
    norm_num
    linarith
  have hinner : 1 + (t ^ (-Cloc) + (ell / 2 + t ^ (-5 : ℤ) + 1)) ≤ 5 * T := by
    linarith
  have hinner0 : 0 ≤ 1 + (t ^ (-Cloc) + (ell / 2 + t ^ (-5 : ℤ) + 1)) := by
    positivity
  calc
    X ≤ K * (1 + (t ^ (-Cloc) + (ell / 2 + t ^ (-5 : ℤ) + 1))) ^ d := hX
    _ ≤ K * (5 * T) ^ d := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hinner0 hinner d) hK
    _ = K * 5 ^ d * t ^ (-(d : ℝ) * (Cloc + 5)) := by
      rw [mul_pow]
      dsimp [T]
      rw [← Real.rpow_natCast (t ^ (-(Cloc + 5))) d, ← Real.rpow_mul ht.le]
      rw [show -(Cloc + 5) * (d : ℝ) = -(d : ℝ) * (Cloc + 5) by ring]
      ring

theorem union_prefactor_le (q : ℝ) (hq : 0 ≤ q) :
    2 * (q ^ 2 + q + 1) * (q ^ 2 + 1) ≤ 6 * (1 + q) ^ 4 := by
  nlinarith [pow_nonneg hq 3, pow_nonneg hq 4, sq_nonneg q]

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.clearingExponent_lt_budgetConcentrationExponent
#print axioms AndersonAC.AgentS6Budget.monitoring_card_polynomial
