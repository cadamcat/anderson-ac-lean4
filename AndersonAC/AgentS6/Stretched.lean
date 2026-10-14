import Mathlib

/-! Stretched-exponential bookkeeping for the final union bounds of Proposition 6.6
(06-clearing.tex:1100–1110): a polynomial number of tests, each with tail `exp(-c t^{-a})`,
stays below `exp(-t^{-κ})/3` for small `t` whenever `0 < κ < a`. -/

noncomputable section
open Filter Topology

namespace AndersonAC.AgentS6

theorem poly_stretched_small (A p c a κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) (hκa : κ < a) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      A * t ^ (-p) * Real.exp (-c * t ^ (-a)) ≤ (1 / 3) * Real.exp (-t ^ (-κ)) := by
  have ha : 0 < a := hκ.trans hκa
  -- in the variable s = t⁻¹ → ∞
  have hs : ∀ᶠ s in atTop, (3 * |A| + 1) * s ^ p * Real.exp (-(c / 2) * s ^ a) ≤ 1 ∧
      s ^ κ ≤ (c / 2) * s ^ a ∧ 1 ≤ s := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / a) (c / 2) (by positivity)).comp
      (tendsto_rpow_atTop ha)
    have h1' : ∀ᶠ s in atTop, (s ^ a) ^ (p / a) * Real.exp (-(c / 2) * s ^ a) <
        1 / (3 * |A| + 1) := h1 (Iio_mem_nhds (by positivity))
    have h2 : ∀ᶠ s : ℝ in atTop, s ^ κ ≤ (c / 2) * s ^ a := by
      have hr := (tendsto_rpow_neg_atTop (show 0 < a - κ by linarith))
      have hev : ∀ᶠ s : ℝ in atTop, s ^ (-(a - κ)) ≤ c / 2 :=
        hr.eventually (Iic_mem_nhds (by positivity))
      filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with s hs hs0
      have e : s ^ κ = s ^ (-(a - κ)) * s ^ a := by
        rw [← Real.rpow_add hs0]; congr 1; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hs0.le _)
    filter_upwards [h1', h2, eventually_ge_atTop (1 : ℝ)] with s h1s h2s h3s
    refine ⟨?_, h2s, h3s⟩
    have hs0 : 0 < s := by linarith
    have e : (s ^ a) ^ (p / a) = s ^ p := by
      rw [← Real.rpow_mul hs0.le]; congr 1; field_simp
    rw [e] at h1s
    have hpos : 0 < 3 * |A| + 1 := by positivity
    rw [lt_div_iff₀ hpos] at h1s
    linarith
  have ht := tendsto_inv_nhdsGT_zero.eventually hs
  filter_upwards [ht, self_mem_nhdsWithin] with t ⟨h1, h2, h3⟩ ht0
  have ht0 : 0 < t := ht0
  have hinv : ∀ x : ℝ, t ^ (-x) = (t⁻¹) ^ x := fun x => by
    rw [Real.rpow_neg ht0.le, Real.inv_rpow ht0.le]
  rw [hinv, hinv, hinv]
  set s := t⁻¹
  have hs0 : 0 < s := inv_pos.mpr ht0
  have hE : Real.exp (-c * s ^ a) = Real.exp (-(c / 2) * s ^ a) * Real.exp (-(c / 2) * s ^ a) := by
    rw [← Real.exp_add]; ring_nf
  have hE2 : Real.exp (-(c / 2) * s ^ a) ≤ Real.exp (-s ^ κ) := by
    apply Real.exp_le_exp.mpr; linarith
  have hsp : 0 ≤ s ^ p := Real.rpow_nonneg hs0.le _
  have hA : A ≤ |A| := le_abs_self A
  have key : A * s ^ p * Real.exp (-(c / 2) * s ^ a) ≤ 1 / 3 := by
    have h1' : 3 * |A| * s ^ p * Real.exp (-(c / 2) * s ^ a) ≤ 1 := by
      have : 0 ≤ s ^ p * Real.exp (-(c / 2) * s ^ a) := by positivity
      nlinarith
    have : A * s ^ p * Real.exp (-(c / 2) * s ^ a) ≤ |A| * s ^ p * Real.exp (-(c / 2) * s ^ a) := by
      have : 0 ≤ s ^ p * Real.exp (-(c / 2) * s ^ a) := by positivity
      nlinarith
    linarith
  rw [hE]
  have hpos : 0 ≤ Real.exp (-(c / 2) * s ^ a) := (Real.exp_pos _).le
  calc A * s ^ p * (Real.exp (-(c / 2) * s ^ a) * Real.exp (-(c / 2) * s ^ a))
      = (A * s ^ p * Real.exp (-(c / 2) * s ^ a)) * Real.exp (-(c / 2) * s ^ a) := by ring
    _ ≤ (1 / 3) * Real.exp (-(c / 2) * s ^ a) := by
        rcases le_or_gt 0 (A * s ^ p * Real.exp (-(c / 2) * s ^ a)) with h | h
        · exact mul_le_mul_of_nonneg_right key hpos
        · nlinarith
    _ ≤ (1 / 3) * Real.exp (-s ^ κ) := by gcongr

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.poly_stretched_small
