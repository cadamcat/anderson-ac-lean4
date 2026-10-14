import AndersonAC.AgentS6.Margins

/-! Pivot location (06-clearing.tex:772–784, equation `clearing-proposed-location`):
a regularized weight at least `2 l_*` forces ordinary distance below `ℓ/2`, given projection
decay with the collapsed-distance comparison `d_T ≥ dist/2 - t^{-1.03}` and `ℓ ≥ t^{-4}/256`. -/

noncomputable section
open scoped Topology
open Filter Set

namespace AndersonAC.S6

open AndersonAC.AgentS6

/-- Pivot location at an explicit scale threshold, uniform in the index type. -/
theorem pivot_location_at {a L t : ℝ} (ha : 0 < a) (hL : 0 < L) (ht0 : 0 < t)
    (ht1 : t < min (1 / 64) (2 * (a / 1024) / L)) {ι : Type*} (m dist : ι → ℝ) (ell : ℝ)
    (hell : (1 / 256) * t ^ (-4 : ℤ) ≤ ell)
    (hm : ∀ i, m i ≤ L * Real.exp (-2 * a * t *
      max (dist i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0))
    (x : ι) (hx : 2 * leverageScale t ≤ m x) : dist x < ell / 2 := by
  set c := a / 1024 with hc
  have hc0 : 0 < c := by positivity
  have ht64 : t < 1 / 64 := lt_of_lt_of_le ht1 (min_le_left _ _)
  have htc : t < 2 * c / L := lt_of_lt_of_le ht1 (min_le_right _ _)
  by_contra hfar
  have hfar : ell / 2 ≤ dist x := le_of_not_gt hfar
  set s := t⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr ht0
  have hs64 : 64 < s := by
    rw [hs, lt_inv_comm₀ (by norm_num) ht0]; simpa using ht64
  have hs1 : 1 ≤ s := by linarith
  have hts : t * s = 1 := mul_inv_cancel₀ ht0.ne'
  have hz : t ^ (-4 : ℤ) = s ^ 4 := by rw [zpow_neg, hs, inv_pow]; norm_cast
  have hr : t ^ (-(103 / 100 : ℝ)) ≤ s ^ 2 := by
    rw [Real.rpow_neg ht0.le, ← Real.inv_rpow ht0.le, ← hs]
    calc s ^ (103 / 100 : ℝ) ≤ s ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
      _ = s ^ 2 := by norm_cast
  have hlev : 1 / s ^ 2 ≤ leverageScale t := by
    unfold leverageScale
    have : t ^ (2 : ℝ) ≤ t ^ (1 + e0) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 (by linarith) (by unfold e0 delta; norm_num)
    calc 1 / s ^ 2 = t ^ 2 := by rw [hs, one_div, inv_pow, inv_inv]
      _ = t ^ (2 : ℝ) := by norm_cast
      _ ≤ _ := this
  -- the exponent
  have hD : s ^ 4 / 2048 ≤ max (dist x / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0 := by
    have h1 : s ^ 4 / 512 ≤ dist x := by rw [hz] at hell; linarith
    have hs2 : 4096 ≤ s ^ 2 := by nlinarith
    have h2 : 2 * s ^ 2 ≤ s ^ 4 / 2048 := by
      have := mul_le_mul_of_nonneg_left hs2 (sq_nonneg s)
      have e : s ^ 4 = s ^ 2 * s ^ 2 := by ring
      rw [e]; nlinarith
    have h3 : 1 ≤ s ^ 2 := by nlinarith
    exact le_max_of_le_left (by linarith)
  have hmx := hm x
  have hexp : Real.exp (-2 * a * t * max (dist x / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) ≤
      Real.exp (-(c * s ^ 3)) := by
    apply Real.exp_le_exp.mpr
    have : 2 * a * t * (s ^ 4 / 2048) = c * s ^ 3 := by
      rw [hc]; have : t * s ^ 4 = s ^ 3 := by rw [show s ^ 4 = s * s ^ 3 by ring, ← mul_assoc, hts, one_mul]
      calc 2 * a * t * (s ^ 4 / 2048) = a / 1024 * (t * s ^ 4) := by ring
        _ = _ := by rw [this]
    have h2 := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 2 * a * t)
    linarith
  -- exp(c s³) > c s³ > (L/2) s²
  have hbig : L / 2 * s ^ 2 < Real.exp (c * s ^ 3) := by
    have h1 : c * s ^ 3 < Real.exp (c * s ^ 3) := by
      have := Real.add_one_le_exp (c * s ^ 3); linarith
    have h2 : L / 2 < c * s := by
      have e : t * L < 2 * c := by rwa [lt_div_iff₀ hL] at htc
      have e2 := mul_lt_mul_of_pos_left e hs0
      have e3 : s * (t * L) = L := by rw [← mul_assoc, mul_comm s t, hts, one_mul]
      linarith
    have h3 : L / 2 * s ^ 2 < c * s * s ^ 2 := mul_lt_mul_of_pos_right h2 (by positivity)
    nlinarith
  have hm2 : m x ≤ L * Real.exp (-(c * s ^ 3)) :=
    hmx.trans (mul_le_mul_of_nonneg_left hexp hL.le)
  have hfin : L * Real.exp (-(c * s ^ 3)) < 2 * (1 / s ^ 2) := by
    rw [Real.exp_neg]
    have hE : 0 < Real.exp (c * s ^ 3) := Real.exp_pos _
    rw [← div_eq_mul_inv, div_lt_iff₀ hE]
    have : 2 * (1 / s ^ 2) * Real.exp (c * s ^ 3) > 2 * (1 / s ^ 2) * (L / 2 * s ^ 2) :=
      mul_lt_mul_of_pos_left hbig (by positivity)
    have e : 2 * (1 / s ^ 2) * (L / 2 * s ^ 2) = L := by field_simp
    linarith
  linarith

theorem pivot_location {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℕ) (a L : ℝ)
    (ha : 0 < a) (hL : 0 < L) : Planned.pivot_location (ι := ι) d a L ha hL := by
  unfold Planned.pivot_location
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (1 / 64) (2 * (a / 1024) / L) by positivity)]
    with t ht
  intro m dist ell hell hm x hx
  exact pivot_location_at ha hL ht.1 ht.2 m dist ell hell hm x hx

end AndersonAC.S6

#print axioms AndersonAC.S6.pivot_location
