import AndersonAC.AgentS6Budget.Numerical
import AndersonAC.AgentS6.Stretched
import AndersonAC.AgentS6.Monitor

noncomputable section
open Filter Topology

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

theorem compressed_prefactor_le {q B : ℝ} (hq : 0 ≤ q) (hB : 1 ≤ B) (hqb : q ≤ B) :
    8 * q ^ 2 + 2 * q + 2 ≤ 12 * B ^ 2 := by
  have hq2 := pow_le_pow_left₀ hq hqb 2
  nlinarith [sq_nonneg (B - 1)]

theorem compressed_union_small (d : ℕ) (hd : 3 ≤ d) (K Cloc cs : ℝ)
    (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hcs : 0 < cs) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ q : ℝ, 0 ≤ q →
      q ≤ K * 5 ^ d * t ^ (-(d : ℝ) * (Cloc + 5)) →
      (8 * q ^ 2 + 2 * q + 2) * Real.exp (-cs * t ^ (-budgetConcentrationExponent)) ≤
        (1 / 3) * Real.exp (-t ^ (-clearingExponent d)) := by
  let A : ℝ := K * 5 ^ d
  let p : ℝ := (d : ℝ) * (Cloc + 5)
  have hA : 1 ≤ A := by
    have h5 : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
    dsimp [A]
    nlinarith
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hev := poly_stretched_small (12 * A ^ 2) (2 * p) cs budgetConcentrationExponent
    (clearingExponent d) hcs (clearingExponent_pos d hd)
      (clearingExponent_lt_budgetConcentrationExponent d hd)
  have htone : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hev, self_mem_nhdsWithin, htone] with t he ht ht1
  have ht : 0 < t := ht
  have hpow : 1 ≤ t ^ (-p) := by
    rw [show (1 : ℝ) = t ^ (0 : ℝ) by simp]
    exact rpow_anti ht ht1.le (by linarith)
  intro q hq hqb
  have hB : 1 ≤ A * t ^ (-p) := by nlinarith
  have hqb' : q ≤ A * t ^ (-p) := by simpa only [A, p, neg_mul] using hqb
  have hbound := compressed_prefactor_le hq hB hqb'
  calc
    _ ≤ (12 * (A * t ^ (-p)) ^ 2) * Real.exp (-cs * t ^ (-budgetConcentrationExponent)) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = (12 * A ^ 2) * t ^ (-(2 * p)) * Real.exp (-cs * t ^ (-budgetConcentrationExponent)) := by
      have hid : (t ^ (-p)) ^ 2 = t ^ (-(2 * p)) := by
        rw [← Real.rpow_natCast (t ^ (-p)) 2, ← Real.rpow_mul ht.le]
        congr 1
        push_cast
        ring
      rw [mul_pow, hid]
      ring
    _ ≤ _ := he

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.compressed_union_small
