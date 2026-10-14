import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open scoped Topology
open Filter
set_option autoImplicit false
namespace AndersonAC.SolS78

/-- The separated assembly halos make every fixed polynomial tail loss
smaller than any prescribed power, uniformly in the actual halo radius. -/
theorem assembly_exponential_tail (c P Q s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ (t R : ℝ), 0 < t → t < t₀ →
      t ^ (-1 - s) ≤ R → t ^ (-P) * Real.exp (-c * t * R) ≤ t ^ Q := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((P + Q) / s) c hc).comp
    (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hs))
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (t ^ (-s)) ^ ((P + Q) / s) * Real.exp (-c * t ^ (-s)) ≤ 1 := by
    filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht
    exact ht.le
  obtain ⟨ε, hε, hbound⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨ε, hε, ?_⟩
  intro t R ht hsmall hR
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
      using hsmall
  have hb := hbound ⟨htball, ht⟩
  change (t ^ (-s)) ^ ((P + Q) / s) * Real.exp (-c * t ^ (-s)) ≤ 1 at hb
  have hpower : (t ^ (-s)) ^ ((P + Q) / s) = t ^ (-P - Q) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    field_simp [hs.ne']
    <;> ring
  rw [hpower] at hb
  have hcancel : t * t ^ (-1 - s) = t ^ (-s) := by
    rw [show (-1 - s : ℝ) = -s - 1 by ring, Real.rpow_sub ht, Real.rpow_one]
    field_simp
  have hradius : t ^ (-s) ≤ t * R := by
    calc
      t ^ (-s) = t * t ^ (-1 - s) := hcancel.symm
      _ ≤ t * R := mul_le_mul_of_nonneg_left hR ht.le
  have hexp : Real.exp (-c * t * R) ≤ Real.exp (-c * t ^ (-s)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hradius hc.le
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le Q)
  have hproduct : t ^ Q * (t ^ (-P - Q) * Real.exp (-c * t ^ (-s))) =
      t ^ (-P) * Real.exp (-c * t ^ (-s)) := by
    rw [← mul_assoc, ← Real.rpow_add ht, show Q + (-P - Q) = -P by ring]
  rw [hproduct, mul_one] at hscaled
  exact (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht.le (-P))).trans hscaled

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_exponential_tail
