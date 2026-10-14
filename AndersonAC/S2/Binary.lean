import AndersonAC.S2.Definitions

/-! Absolute convergence and deterministic identities for the true sign series
in §2. Digit `k` here is digit `k+1` in the paper. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AndersonAC.S2

@[simp] theorem abs_signValue (a : Bool) : |signValue a| = 1 := by
  cases a <;> norm_num [signValue]

theorem hasSum_binary_weights (c : ℝ) :
    HasSum (fun k : ℕ => c / (2 : ℝ) ^ (k + 1)) c := by
  have h := (hasSum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (c / 2)
  convert h using 1
  · ext k
    simp only [div_eq_mul_inv, inv_pow, pow_succ, one_mul]
    ring
  · norm_num

theorem norm_binary_term (c : ℝ) (a : ℕ → Bool) (k : ℕ) :
    ‖c / (2 : ℝ) ^ (k + 1) * signValue (a k)‖ = |c| / (2 : ℝ) ^ (k + 1) := by
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_signValue, mul_one,
    abs_of_pos (by positivity : 0 < (2 : ℝ) ^ (k + 1))]

theorem binary_summable (coupling : ℝ) (a : ℕ → Bool) :
    Summable (fun k : ℕ => coupling / (2 : ℝ) ^ (k + 1) * signValue (a k)) := by
  apply (hasSum_binary_weights |coupling|).summable.of_norm_bounded
  intro k
  exact (norm_binary_term coupling a k).le

theorem binaryValue_bound (coupling : ℝ) (a : ℕ → Bool) :
    |binaryValue coupling a| ≤ |coupling| := by
  apply (binary_summable coupling a).hasSum.norm_le_of_bounded
    (hasSum_binary_weights |coupling|)
  intro k
  exact (norm_binary_term coupling a k).le

theorem binary_prefix_suffix (coupling : ℝ) (h : ℕ) (a : ℕ → Bool) :
    binaryValue coupling a = binaryPrefix coupling h a + binarySuffix coupling h a := by
  simpa only [binaryValue, binaryPrefix, binarySuffix, Nat.add_comm] using
    ((binary_summable coupling a).sum_add_tsum_nat_add h).symm

theorem binaryValue_measurable (coupling : ℝ) : Measurable (binaryValue coupling) := by
  apply Measurable.tsum
  intro k
  exact measurable_const.mul ((measurable_of_finite signValue).comp (measurable_pi_apply k))

theorem binarySuffix_eq_scaled (coupling : ℝ) (h : ℕ) (a : ℕ → Bool) :
    binarySuffix coupling h a = binaryValue (coupling / (2 : ℝ) ^ h) (fun k => a (h + k)) := by
  unfold binarySuffix binaryValue
  apply tsum_congr
  intro k
  rw [show h + k + 1 = h + (k + 1) by omega, pow_add]
  ring

theorem binarySuffix_measurable (coupling : ℝ) (h : ℕ) : Measurable (binarySuffix coupling h) := by
  change Measurable (fun a => binarySuffix coupling h a)
  simp_rw [binarySuffix_eq_scaled]
  apply (binaryValue_measurable _).comp
  exact Measurable.of_eval (fun k => measurable_pi_apply (h + k))

theorem binarySuffix_bound (coupling : ℝ) (h : ℕ) (a : ℕ → Bool) :
    |binarySuffix coupling h a| ≤ |coupling| / (2 : ℝ) ^ h := by
  rw [binarySuffix_eq_scaled]
  convert binaryValue_bound (coupling / (2 : ℝ) ^ h) (fun k => a (h + k)) using 1
  rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ h)]

end AndersonAC.S2
