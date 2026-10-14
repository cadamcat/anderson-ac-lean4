import AndersonAC.AgentS6.Margins

/-! Summed one-row bias (06-clearing.tex:1007–1020, equation `clearing-bias-margins`): over at
most `n_h` heats with `Σ |v|² ≤ A t^{.27δ}`, the one-row biases sum to at most `l_*/4` for small
`t`, uniformly in the row and the heats. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace AndersonAC.AgentS6

open AndersonAC.S6

/-- `x ≤ √y` from `x² ≤ y`, `0 ≤ x`. -/
theorem le_sqrt_of_sq (x y : ℝ) (hx : 0 ≤ x) (h : x ^ 2 ≤ y) : x ≤ Real.sqrt y :=
  Real.le_sqrt_of_sq_le h |>.trans' le_rfl

theorem row_bias_sum (d : ℕ) (hd : 3 ≤ d) (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ (s : Finset ℕ) (v : ℕ → ℝ), (∀ k, 0 ≤ v k) →
      (s.card : ℝ) ≤ heatLimit t → ∑ k ∈ s, v k ^ 2 ≤ A * t ^ ((27 / 100) * delta) →
      ∑ k ∈ s, oneRowBias d t L (v k) ≤ leverageScale t / 4 := by
  obtain ⟨hlim, -⟩ := leverage_bias_margins d hd
  set P : ℝ → ℝ := fun t => t ^ ((265 / 1000) * delta) + t ^ ((27 / 100) * delta) +
    t ^ ((34 / 100) * delta) + t ^ (1 / 2 - (2 / 100) * delta) +
    t ^ (1 / 2 + (48 / 100) * delta - nu d) + t ^ ((345 / 1000) * delta) +
    t ^ ((42 / 100) * delta) with hP
  set M : ℝ := L * (1 + Real.sqrt A + A) with hM
  have hM0 : 0 ≤ M := by positivity
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), M * P t ≤ 1 / 4 := by
    have := (hlim.const_mul M)
    rw [mul_zero] at this
    exact this.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t hMP ht
  obtain ⟨ht0, ht1⟩ := ht
  intro s v hv hcard hS2
  set l := leverageScale t with hl
  set N : ℝ := (heatLimit t : ℝ)
  have hl0 : 0 < l := Real.rpow_pos_of_pos ht0 _
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hδ : delta = 1 / 100 := rfl
  have rp : ∀ a b : ℝ, t ^ a * t ^ b = t ^ (a + b) := fun a b => (Real.rpow_add ht0 a b).symm
  have hsqrt : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
  have hN : N ≤ t ^ (-1 - eh) := Nat.floor_le (Real.rpow_nonneg ht0.le _)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set S1 := ∑ k ∈ s, v k
  set S2 := ∑ k ∈ s, v k ^ 2
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun k _ => hv k
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  -- Cauchy–Schwarz
  have hCS : S1 ^ 2 ≤ N * (A * t ^ ((27 / 100) * delta)) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) v
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    calc S1 ^ 2 ≤ (s.card : ℝ) * S2 := h1
      _ ≤ N * (A * t ^ ((27 / 100) * delta)) := mul_le_mul hcard hS2 hS20 hN0
  have hNt : N * t ^ ((27 / 100) * delta) ≤ t ^ (-1 - eh + (27 / 100) * delta) := by
    rw [← rp]; exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg ht0.le _)
  have hS1sq : S1 ^ 2 ≤ A * t ^ (-1 - eh + (27 / 100) * delta) := by
    have := mul_le_mul_of_nonneg_left hNt hA
    nlinarith
  -- the five pieces
  have e1 : Real.sqrt t * t ^ betaW * S1 ≤ Real.sqrt A * t ^ ((265 / 1000) * delta) := by
    have hx : 0 ≤ Real.sqrt t * t ^ betaW * S1 := by positivity
    have hsq1 : (Real.sqrt t * t ^ betaW * S1) ^ 2 ≤ (Real.sqrt A * t ^ ((265 / 1000) * delta)) ^ 2 := by
      have hT : (Real.sqrt t * t ^ betaW) ^ 2 = t ^ (1 + 2 * betaW) := by
        rw [mul_pow, Real.sq_sqrt ht0.le, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
          ← Real.rpow_one_add' ht0.le]
        · congr 1; push_cast; ring
        · unfold betaW delta; norm_num
      have hT0 : 0 ≤ t ^ (1 + 2 * betaW) := Real.rpow_nonneg ht0.le _
      calc (Real.sqrt t * t ^ betaW * S1) ^ 2 = t ^ (1 + 2 * betaW) * S1 ^ 2 := by
            rw [mul_pow, hT]
        _ ≤ t ^ (1 + 2 * betaW) * (A * t ^ (-1 - eh + (27 / 100) * delta)) :=
            mul_le_mul_of_nonneg_left hS1sq hT0
        _ = A * t ^ (1 + 2 * betaW + (-1 - eh + (27 / 100) * delta)) := by
            rw [mul_left_comm, rp]
        _ = (Real.sqrt A * t ^ ((265 / 1000) * delta)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hA, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
            congr 2; unfold betaW eh delta; push_cast; ring
    exact (pow_le_pow_iff_left₀ hx (by positivity) (by norm_num)).mp hsq1
  have e2 : S2 ≤ A * t ^ ((27 / 100) * delta) := hS2
  have hcardN : (s.card : ℝ) * (l * epsilonScale d t) ≤ t ^ ((34 / 100) * delta) +
      t ^ (1 / 2 - (2 / 100) * delta) + t ^ (1 / 2 + (48 / 100) * delta - nu d) := by
    have hNl : N * l ≤ t ^ (-(2 / 100) * delta) := by
      calc N * l ≤ t ^ (-1 - eh) * l := mul_le_mul_of_nonneg_right hN hl0.le
        _ = t ^ (-(2 / 100) * delta) := by
          rw [hl, leverageScale, rp]; congr 1; unfold eh e0; ring
    have hε0 : 0 ≤ epsilonScale d t := by unfold epsilonScale coreCap; positivity
    have h1 : (s.card : ℝ) * (l * epsilonScale d t) ≤ t ^ (-(2 / 100) * delta) * epsilonScale d t := by
      calc (s.card : ℝ) * (l * epsilonScale d t) ≤ N * (l * epsilonScale d t) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (N * l) * epsilonScale d t := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hNl hε0
    refine h1.trans (le_of_eq ?_)
    unfold epsilonScale coreCap fourthCap
    rw [hsqrt, Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le, mul_add, mul_add, rp, rp, ← mul_assoc,
      rp, rp]
    congr 1
    · congr 1
      · congr 1; unfold betaW; ring
      · congr 1; ring
    · congr 1; ring
  have e4 : l * S1 / Real.sqrt t ≤ Real.sqrt A * t ^ ((345 / 1000) * delta) := by
    have hx : 0 ≤ l * S1 / Real.sqrt t := by positivity
    have hsq1 : (l * S1 / Real.sqrt t) ^ 2 ≤ (Real.sqrt A * t ^ ((345 / 1000) * delta)) ^ 2 := by
      have hT : (l / Real.sqrt t) ^ 2 = t ^ (1 + 2 * e0) := by
        rw [div_pow, Real.sq_sqrt ht0.le, hl, leverageScale, ← Real.rpow_natCast,
          ← Real.rpow_mul ht0.le, div_eq_iff ht0.ne', ← Real.rpow_add_one ht0.ne']
        congr 1; push_cast; ring
      have hT0 : 0 ≤ t ^ (1 + 2 * e0) := Real.rpow_nonneg ht0.le _
      calc (l * S1 / Real.sqrt t) ^ 2 = (l / Real.sqrt t) ^ 2 * S1 ^ 2 := by ring
        _ = t ^ (1 + 2 * e0) * S1 ^ 2 := by rw [hT]
        _ ≤ t ^ (1 + 2 * e0) * (A * t ^ (-1 - eh + (27 / 100) * delta)) :=
            mul_le_mul_of_nonneg_left hS1sq hT0
        _ = A * t ^ (1 + 2 * e0 + (-1 - eh + (27 / 100) * delta)) := by
            rw [mul_left_comm, rp]
        _ = (Real.sqrt A * t ^ ((345 / 1000) * delta)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hA, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
            congr 2; unfold e0 eh delta; push_cast; ring
    exact (pow_le_pow_iff_left₀ hx (by positivity) (by norm_num)).mp hsq1
  have e5 : (s.card : ℝ) * (l ^ 2 / t) ≤ t ^ ((42 / 100) * delta) := by
    calc (s.card : ℝ) * (l ^ 2 / t) ≤ N * (l ^ 2 / t) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ t ^ (-1 - eh) * (l ^ 2 / t) := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = t ^ ((42 / 100) * delta) := by
        rw [hl, leverageScale, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
          ← Real.rpow_sub_one ht0.ne', rp]
        congr 1; unfold eh e0; push_cast; ring
  -- assemble
  have hsum : ∑ k ∈ s, oneRowBias d t L (v k) =
      L * l * (Real.sqrt t * t ^ betaW * S1 + S2 + (s.card : ℝ) * (l * epsilonScale d t) +
        l * S1 / Real.sqrt t + (s.card : ℝ) * (l ^ 2 / t)) := by
    have h1 : ∑ k ∈ s, oneRowBias d t L (v k) = ∑ k ∈ s,
        (L * l * (Real.sqrt t * t ^ betaW) * v k + L * l * v k ^ 2 +
          L * l * (l * epsilonScale d t) + L * l * (l / Real.sqrt t) * v k +
            L * l * (l ^ 2 / t)) :=
      Finset.sum_congr rfl fun k _ => by unfold oneRowBias; rw [← hl]; ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp only [S1, S2, ← Finset.mul_sum]
    ring
  rw [hsum]
  have hsqA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hp : ∀ x : ℝ, 0 ≤ t ^ x := fun x => Real.rpow_nonneg ht0.le x
  have hbr : Real.sqrt t * t ^ betaW * S1 + S2 + (s.card : ℝ) * (l * epsilonScale d t) +
      l * S1 / Real.sqrt t + (s.card : ℝ) * (l ^ 2 / t) ≤ (1 + Real.sqrt A + A) * P t := by
    simp only [hP]
    nlinarith [hp ((265 / 1000) * delta), hp ((27 / 100) * delta), hp ((34 / 100) * delta),
      hp (1 / 2 - (2 / 100) * delta), hp (1 / 2 + (48 / 100) * delta - nu d),
      hp ((345 / 1000) * delta), hp ((42 / 100) * delta)]
  have hLl : 0 ≤ L * l := by positivity
  calc L * l * (Real.sqrt t * t ^ betaW * S1 + S2 + (s.card : ℝ) * (l * epsilonScale d t) +
        l * S1 / Real.sqrt t + (s.card : ℝ) * (l ^ 2 / t))
      ≤ L * l * ((1 + Real.sqrt A + A) * P t) := mul_le_mul_of_nonneg_left hbr hLl
    _ = l * (M * P t) := by rw [hM]; ring
    _ ≤ l * (1 / 4) := mul_le_mul_of_nonneg_left hMP hl0.le
    _ = l / 4 := by ring

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.row_bias_sum
