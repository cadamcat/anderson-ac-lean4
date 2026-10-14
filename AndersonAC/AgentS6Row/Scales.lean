import AndersonAC.S6.Definitions
import AndersonAC.L64.Arith
import AndersonAC.L64.Residual

noncomputable section
open Filter Topology

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

lemma nu_nonneg (d : ℕ) : 0 ≤ nu d := by unfold nu delta; positivity

lemma nu_le_one_hundredth (d : ℕ) : nu d ≤ 1 / 100 := by
  cases d with
  | zero => norm_num [nu]
  | succ d =>
      unfold nu delta
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (d + 1 : ℕ))]
      have hd : (1 : ℝ) ≤ (d + 1 : ℕ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.succ_pos d)
      norm_num
      linarith

lemma sqrt_fourthCap (t : ℝ) (ht : 0 < t) :
    Real.sqrt (fourthCap t) = t ^ ((1 + delta) / 2) := by
  unfold fourthCap
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
  congr 1
  ring

lemma scale_ratio (t : ℝ) (ht : 0 < t) :
    leverageScale t / Real.sqrt t = t ^ (1 / 2 + e0) := by
  unfold leverageScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht]
  congr 1
  ring

lemma scale_squared_ratio (t : ℝ) (ht : 0 < t) :
    (leverageScale t) ^ 2 / t = t ^ (1 + 2 * e0) := by
  unfold leverageScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  conv_lhs => rhs; rw [← Real.rpow_one t]
  rw [← Real.rpow_sub ht]
  congr 1
  push_cast
  ring

lemma core_fourth_ratio (d : ℕ) (t : ℝ) (ht : 0 < t) :
    coreCap d t * Real.sqrt (fourthCap t) = t ^ ((1 + delta) / 2 - nu d) := by
  rw [sqrt_fourthCap t ht]
  unfold coreCap
  rw [← Real.rpow_add ht]
  congr 1
  ring

lemma epsilonScale_lower (d : ℕ) (t : ℝ) (ht : 0 < t) :
    t ^ betaW ≤ epsilonScale d t ∧ Real.sqrt t ≤ epsilonScale d t := by
  have ha : 0 ≤ t ^ betaW := Real.rpow_nonneg ht.le _
  have hb : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hc : 0 ≤ coreCap d t * Real.sqrt (fourthCap t) := by
    unfold coreCap
    positivity
  unfold epsilonScale
  constructor <;> linarith

lemma coreCap_ge_one (d : ℕ) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ coreCap d t := by
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (neg_nonpos.mpr (nu_nonneg d))

/-- The explicit row error estimates require only these uniform smallness conditions. -/
theorem row_scales_small (d : ℕ) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Small t K ∧
      leverageScale t / Real.sqrt t ≤ 1 ∧
      Real.sqrt (fourthCap t) ≤ leverageScale t / Real.sqrt t ∧
      Real.sqrt t ≤ t ^ betaW ∧
      K / c * (t ^ betaW + 2 * coreCap d t * Real.sqrt (fourthCap t)) ≤ 1 ∧
      16 * KPhi K c * (leverageScale t) ^ 2 / t ≤ 1 / 4 := by
  have hpow : ∀ a : ℝ, 0 < a → Tendsto (fun t : ℝ => t ^ a) (𝓝[>] 0) (𝓝 0) := by
    intro a ha
    simpa only [Real.zero_rpow ha.ne'] using
      ((Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.mono_left nhdsWithin_le_nhds)
  have hβ := hpow betaW (by norm_num [betaW, delta])
  have hν := nu_le_one_hundredth d
  have hcore := hpow ((1 + delta) / 2 - nu d) (by unfold delta; linarith)
  have hsqrt := hpow (1 / 2) (by norm_num)
  have hratio := hpow (1 + 2 * e0) (by norm_num [e0, delta])
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 4 * K ^ 2 * Real.sqrt t ≤ 1 := by
    have hh := hsqrt.const_mul (4 * K ^ 2)
    simp only [mul_zero] at hh
    simpa only [Real.sqrt_eq_rpow] using hh.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hvn : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      K / c * (t ^ betaW + 2 * t ^ ((1 + delta) / 2 - nu d)) ≤ 1 := by
    have hh := (hβ.add (hcore.const_mul 2)).const_mul (K / c)
    simp only [mul_zero, add_zero] at hh
    exact hh.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hfro : ∀ᶠ t in 𝓝[>] (0 : ℝ), 16 * KPhi K c * t ^ (1 + 2 * e0) ≤ 1 / 4 := by
    have hh := hratio.const_mul (16 * KPhi K c)
    simp only [mul_zero] at hh
    exact hh.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall, hvn, hfro, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    with t hsmall hvn hfro ht
  obtain ⟨ht0, ht1⟩ := ht
  refine ⟨⟨ht0, ht1.le, hK, hsmall⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [scale_ratio t ht0]
    exact Real.rpow_le_one ht0.le ht1.le (by norm_num [e0, delta])
  · rw [sqrt_fourthCap t ht0, scale_ratio t ht0]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by norm_num [e0, delta])
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by norm_num [betaW, delta])
  · rw [mul_assoc 2, core_fourth_ratio d t ht0]
    exact hvn
  · rw [show 16 * KPhi K c * (leverageScale t) ^ 2 / t =
        16 * KPhi K c * ((leverageScale t) ^ 2 / t) by ring, scale_squared_ratio t ht0]
    exact hfro

end AndersonAC.AgentS6Row
