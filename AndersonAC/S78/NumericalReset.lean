import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open scoped Topology
open Filter
set_option autoImplicit false

namespace AndersonAC.SolS78

/-- The logarithmic inverse-row loss is dominated by any positive power. -/
theorem reset_log_power_tendsto (s : ℝ) (hs : 0 < s) :
    Tendsto (fun t : ℝ => Real.log (1 / t) * t ^ s) (𝓝[>] 0) (𝓝 0) := by
  simpa only [one_div, Real.log_inv, neg_mul, neg_zero] using
    (_root_.tendsto_log_mul_rpow_nhdsGT_zero hs).neg

/-- Uniform scalar smallness for the radius t^(.35δ) and lag t^(.36δ).
The threshold is chosen before the finite matrix size and state. -/
theorem reset_numerical_smallness (C δ : ℝ) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      0 ≤ C * Real.log (1 / t) ∧
      C * Real.log (1 / t) * (t ^ (0.36 * δ) + C * (t ^ (0.35 * δ)) ^ 2) ≤ t ^ (0.35 * δ) ∧
      C * Real.log (1 / t) * C * t ^ (0.35 * δ) ≤ 1 / 2 := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hu : Tendsto (fun t : ℝ => C * Real.log (1 / t) * t ^ (0.01 * δ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      tendsto_const_nhds.mul (reset_log_power_tendsto (0.01 * δ) (by positivity))
  have hv : Tendsto (fun t : ℝ => C ^ 2 * Real.log (1 / t) * t ^ (0.35 * δ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      tendsto_const_nhds.mul (reset_log_power_tendsto (0.35 * δ) (by positivity))
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0,
      C * Real.log (1 / t) * t ^ (0.01 * δ) ≤ 1 / 2 ∧
      C ^ 2 * Real.log (1 / t) * t ^ (0.35 * δ) ≤ 1 / 2 := by
    filter_upwards [hu.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht₁ ht₂
    exact ⟨ht₁.le, ht₂.le⟩
  obtain ⟨ε, hε, hbound⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
  intro t ht hsmall
  have htε : t < ε := lt_of_lt_of_le hsmall (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le hsmall (min_le_right _ _)
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht] using htε
  obtain ⟨h₁, h₂⟩ := hbound ⟨htball, ht⟩
  have hlog : 0 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos ht.le ht1.le)
  have hrpow : t ^ (0.36 * δ) = t ^ (0.35 * δ) * t ^ (0.01 * δ) := by
    rw [show (0.36 : ℝ) * δ = 0.35 * δ + 0.01 * δ by ring, Real.rpow_add ht]
  refine ⟨mul_nonneg hC0 hlog, ?_, ?_⟩
  · calc
      C * Real.log (1 / t) * (t ^ (0.36 * δ) + C * (t ^ (0.35 * δ)) ^ 2) =
          t ^ (0.35 * δ) *
            (C * Real.log (1 / t) * t ^ (0.01 * δ) + C ^ 2 * Real.log (1 / t) * t ^ (0.35 * δ)) := by
              rw [hrpow]
              ring
      _ ≤ t ^ (0.35 * δ) * ((1 / 2) + (1 / 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (Real.rpow_nonneg ht.le _)
      _ = t ^ (0.35 * δ) := by ring
  · convert h₂ using 1; ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.reset_log_power_tendsto
#print axioms AndersonAC.SolS78.reset_numerical_smallness
