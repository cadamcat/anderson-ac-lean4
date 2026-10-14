import AndersonAC.AgentS6.Margins

/-! Running heat prestates from the distortion budgets and the start slack
(06-clearing.tex:862–870): the fourth-power part of `clearing-prestate` from
`clearing-fourth-distortion`, the initial factor `.8` and the margin `.09δ`; the lag and
diagonal parts from the entry budget and the uniform start lag `qlag → 0`. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace AndersonAC.AgentS6

open AndersonAC.S6

/-- Two-point convexity of `x ↦ x⁴` with weights `24/25`, `1/25`. -/
theorem pow4_split (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 4 ≤ (15625 / 13824) * a ^ 4 + 15625 * b ^ 4 := by
  have hc := (convexOn_pow (𝕜 := ℝ) 4).2 (show a * (25 / 24) ∈ Ici (0 : ℝ) from
    mul_nonneg ha (by norm_num)) (show b * 25 ∈ Ici (0 : ℝ) from mul_nonneg hb (by norm_num))
    (show (0 : ℝ) ≤ 24 / 25 by norm_num) (show (0 : ℝ) ≤ 1 / 25 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hc
  have e1 : 24 / 25 * (a * (25 / 24)) + 1 / 25 * (b * 25) = a + b := by ring
  rw [e1] at hc
  nlinarith [hc]

theorem scaled_entry_le {ι : Type*} (t : ℝ) (g0 hg : Matrix ι ι ℂ) (i j : ι) :
    ‖scaledInverse t hg i j‖ ≤ ‖scaledInverse t g0 i j‖ + ‖scaledInverse t (hg - g0) i j‖ := by
  have : scaledInverse t hg i j = scaledInverse t g0 i j + scaledInverse t (hg - g0) i j := by
    simp [scaledInverse, Matrix.smul_apply, Matrix.sub_apply, mul_sub]
  rw [this]; exact norm_add_le _ _

end AndersonAC.AgentS6

namespace AndersonAC.S6

open AndersonAC.AgentS6

/-- Running prestates satisfy `clearing-prestate` with constant `3K+1` (06-clearing.tex:862–870). -/
theorem prestate_from_budgets (K : ℝ) (hK : 1 ≤ K) (q : ℝ → ℝ)
    (hq : Tendsto q (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Planned.prestate_from_budgets K hK q hq := by
  unfold Planned.prestate_from_budgets
  have hsmall := tendsto_rpow_zero (a := (9 / 100) * delta) (by unfold delta; norm_num)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    hq.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hsmall.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 200000 by norm_num))]
    with t ht hqt hsm
  obtain ⟨ht0, ht1⟩ := ht
  have hqt : q t ≤ 1 := hqt
  have hsm : t ^ ((9 / 100) * delta) ≤ 1 / 200000 := hsm
  intro n r g0 hg hr hfourth hlag hbudget
  have hE : entryBudget t ≤ t ^ betaW :=
    rpow_anti ht0 ht1.le (by unfold betaW delta; norm_num)
  have hβ : 0 ≤ t ^ betaW := Real.rpow_nonneg ht0.le _
  have hβ1 : t ^ betaW ≤ 1 := Real.rpow_le_one ht0.le ht1.le (by unfold betaW delta; norm_num)
  have hlag' : ∀ i, ‖hg i i - r i‖ ≤ 2 * t ^ betaW := by
    intro i
    have h1 := hbudget.1 i i
    have h2 := hlag i
    have : ‖hg i i - r i‖ ≤ ‖hg i i - g0 i i‖ + ‖g0 i i - r i‖ := by
      calc ‖hg i i - r i‖ = ‖(hg i i - g0 i i) + (g0 i i - r i)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    nlinarith
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have h1 : ‖hg i i‖ ≤ ‖r i‖ + ‖hg i i - r i‖ := by
      calc ‖hg i i‖ = ‖r i + (hg i i - r i)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have := hlag' i
    have := hr i
    nlinarith
  · have := hlag' i
    nlinarith
  · have hdist := fourth_distortion t g0 hg ht0 hbudget i
    have hstart := hfourth i
    unfold fourthRow at hdist hstart ⊢
    have hterm : ∀ j, ‖scaledInverse t hg i j‖ ^ 4 ≤
        (15625 / 13824) * ‖scaledInverse t g0 i j‖ ^ 4 +
          15625 * ‖scaledInverse t (hg - g0) i j‖ ^ 4 := by
      intro j
      calc ‖scaledInverse t hg i j‖ ^ 4 ≤
          (‖scaledInverse t g0 i j‖ + ‖scaledInverse t (hg - g0) i j‖) ^ 4 :=
            pow_le_pow_left₀ (norm_nonneg _) (scaled_entry_le t g0 hg i j) 4
        _ ≤ _ := pow4_split _ _ (norm_nonneg _) (norm_nonneg _)
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hH : t ^ (1 + (109 / 100) * delta) = fourthCap t * t ^ ((9 / 100) * delta) := by
      unfold fourthCap; rw [← Real.rpow_add ht0]; congr 1; ring
    have hcap : 0 ≤ fourthCap t := Real.rpow_nonneg ht0.le _
    rw [hH] at hdist
    have h3 : fourthCap t * t ^ ((9 / 100) * delta) ≤ fourthCap t * (1 / 200000) :=
      mul_le_mul_of_nonneg_left hsm hcap
    nlinarith

end AndersonAC.S6

#print axioms AndersonAC.S6.prestate_from_budgets
