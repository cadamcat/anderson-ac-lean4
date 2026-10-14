import AndersonAC.S2.Binary
import AndersonAC.S2.Scales
import AndersonAC.Prob.Binary

/-! Coupling, normalization and moment transports of the accepted WP04 law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AndersonAC.SolS2
open AndersonAC.S2

theorem uniformInterval_eq_blueprint (a : ℝ) :
    S2.uniformInterval a = Blueprint.uniformInterval (-a) a := by
  unfold S2.uniformInterval Blueprint.uniformInterval
  rw [show a - -a = 2 * a by ring]

theorem binarySuffix_eq_blueprint (c : ℝ) (h : ℕ) (a : ℕ → Bool) :
    binarySuffix c h a = c * Blueprint.binaryTail h a := by
  unfold binarySuffix Blueprint.binaryTail
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [Nat.add_comm h k]
  unfold signValue
  ring

theorem uniformInterval_moments {a : ℝ} (ha : 0 < a) :
    (∫ x, x ∂S2.uniformInterval a) = 0 ∧
      (∫ x, x ^ 2 ∂S2.uniformInterval a) = a ^ 2 / 3 := by
  have hab : -a ≤ a := by linarith
  have ha0 : 2 * a ≠ 0 := by positivity
  constructor
  · rw [S2.uniformInterval, integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, integral_id]
    simp
  · rw [S2.uniformInterval, integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, integral_pow]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * a),
      smul_eq_mul]
    norm_num
    field_simp
    ring

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2

theorem binary_suffix_uniform {coupling : ℝ} (hcoupling : 0 < coupling) (h : ℕ) :
    AuxiliaryLaw.map (binarySuffix coupling h) = uniformInterval (coupling / (2 : ℝ) ^ h) := by
  have hf : binarySuffix coupling h =
      (fun x : ℝ => coupling * x) ∘ Blueprint.binaryTail h := by
    funext a
    exact binarySuffix_eq_blueprint coupling h a
  rw [hf, ← Measure.map_map (measurable_const_mul coupling)
    (AndersonAC.MuseProb.measurable_binaryTail h)]
  change (Blueprint.bitLaw.map (Blueprint.binaryTail h)).map _ = _
  rw [AndersonAC.MuseProb.map_binaryTail,
    AndersonAC.MuseProb.map_uniformInterval_mul hcoupling (by
      have : 0 < ((2 : ℝ)⁻¹) ^ h := by positivity
      linarith), uniformInterval_eq_blueprint]
  simp only [mul_neg, inv_pow, div_eq_mul_inv]

theorem binary_uniform {coupling : ℝ} (hcoupling : 0 < coupling) :
    AuxiliaryLaw.map (binaryValue coupling) = uniformInterval coupling := by
  have hf : binarySuffix coupling 0 = binaryValue coupling := by
    funext a
    simp only [binarySuffix, Nat.zero_add, binaryValue]
  simpa only [hf, pow_zero, div_one] using binary_suffix_uniform hcoupling 0

theorem binary_suffix_moments (coupling : ℝ) (h : ℕ) :
    (∫ a, binarySuffix coupling h a ∂AuxiliaryLaw) = 0 ∧
    (∫ a, (binarySuffix coupling h a) ^ 2 ∂AuxiliaryLaw) =
      coupling ^ 2 / (4 : ℝ) ^ h / 3 := by
  have hm := uniformInterval_moments (a := 1 / (2 : ℝ) ^ h) (by positivity)
  rw [← binary_suffix_uniform (by norm_num : (0 : ℝ) < 1) h] at hm
  rw [integral_map_of_stronglyMeasurable (binarySuffix_measurable 1 h)
      (f := fun x : ℝ => x) measurable_id.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (binarySuffix_measurable 1 h)
      (f := fun x : ℝ => x ^ 2) (continuous_id.pow 2).stronglyMeasurable] at hm
  have hscale : ∀ a, binarySuffix coupling h a = coupling * binarySuffix 1 h a := by
    intro a
    rw [binarySuffix_eq_blueprint, binarySuffix_eq_blueprint, one_mul]
  constructor
  · simp_rw [hscale]
    rw [integral_const_mul, hm.1, mul_zero]
  · simp_rw [hscale, mul_pow]
    rw [integral_const_mul, hm.2, four_pow_eq_two_pow_sq]
    ring

theorem stage_variance {coupling : ℝ} {n : ℕ} (hn : initialScale coupling ≤ n) :
    coupling ^ 2 / (4 : ℝ) ^ (n - initialScale coupling) / 3 = varianceScale coupling n := by
  have hpow : (4 : ℝ) ^ n = 4 ^ initialScale coupling * 4 ^ (n - initialScale coupling) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  rw [varianceScale, scaleU, hpow]
  field_simp

theorem next_digit_amplitude {coupling : ℝ} (hcoupling : 0 < coupling) {n : ℕ}
    (hn : initialScale coupling ≤ n) :
    coupling / (2 : ℝ) ^ (n - initialScale coupling + 1) =
      Real.sqrt (3 * varianceScale coupling n / 4) := by
  rw [← stage_variance hn]
  have hsq : 3 * (coupling ^ 2 / (4 : ℝ) ^ (n - initialScale coupling) / 3) / 4 =
      (coupling / (2 : ℝ) ^ (n - initialScale coupling + 1)) ^ 2 := by
    rw [four_pow_eq_two_pow_sq, pow_succ]
    field_simp
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]

end AndersonAC.S2
