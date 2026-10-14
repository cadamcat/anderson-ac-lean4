import AndersonAC.AgentS78.Construction.TileTrial
import AndersonAC.S45.ConcentrationPackageProof

/-!
# the first-trial bound of the tile block

* `tileTrialBound_of_crossing`: the S45 route — a `TrialInputs` whose crossing contains the
  first-trial failure gives `exp(−t^{−c})` by `S45.one_trial` (Lemma 5.6 with
  Golden–Thompson, `AgentS45.one_trial_proof`, `AgentS45.goldenThompson_S45`).
* `tile_first_trial_bound`: the birth bound `birthBound c j` for every good record
  (05:766–772; scale `t ≍ 4^{−j}` by `S78.stage_scale_comparison`), from the analytic
  core `TileTrialBoundStatement`. Aborted records enter a halted block and never fail.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw)

/-- The sweep scale is positive. -/
theorem sweepScale_pos_first {u : ℝ} (hu : 0 < u) (m j : ℕ) : 0 < sweepScale u m j := by
  unfold sweepScale stageScale
  split_ifs <;> positivity

/-- `t ≤ 8 · 4^{−j}` for the sweep with post-sweep index `n₀ < j ≤ m + 1`
(by `S78.stage_scale_comparison`). -/
theorem sweepScale_le {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {m j : ℕ} (hj0 : 0 < j)
    (hj : j ≤ m + 1) : sweepScale u m j ≤ 8 / (4 : ℝ) ^ j := by
  unfold sweepScale
  split_ifs with hf
  · have hjm : j = m + 1 := le_antisymm hj hf
    have h := (stage_scale_comparison u m m hu le_rfl).2
    calc stageScale u m m ≤ 2 / (4 : ℝ) ^ m := h
      _ = 8 / (4 : ℝ) ^ j := by rw [hjm, pow_succ]; field_simp; norm_num
  · have hjm : j - 1 ≤ m := by unfold IsFinalSweep at hf; omega
    have h := (stage_scale_comparison u (j - 1) m hu hjm).2
    calc stageScale u (j - 1) m ≤ 2 / (4 : ℝ) ^ (j - 1) := h
      _ = 8 / (4 : ℝ) ^ j := by
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]; field_simp; norm_num

/-- `exp(−t^{−c}) ≤ birthBound (c/2) j` when `0 < t ≤ 8 · 4^{−j}` and `j ≥ 3`. -/
theorem exp_le_birthBound {c t : ℝ} (hc : 0 < c) (ht : 0 < t) {j : ℕ} (hj : 3 ≤ j)
    (htj : t ≤ 8 / (4 : ℝ) ^ j) :
    Real.exp (-S45.power t (-c)) ≤ birthBound (c / 2) j := by
  unfold birthBound
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  set s : ℝ := (4 : ℝ) ^ ((j : ℝ) / 2) with hs
  have hs0 : 0 ≤ s := by positivity
  have hss : s * s = (4 : ℝ) ^ j := by
    rw [hs, ← Real.rpow_add (by norm_num : (0 : ℝ) < 4), add_halves, Real.rpow_natCast]
  have h64 : (64 : ℝ) ≤ (4 : ℝ) ^ j := by
    calc (64 : ℝ) = (4 : ℝ) ^ 3 := by norm_num
      _ ≤ (4 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hs8 : 8 ≤ s := by nlinarith
  have h4j : 0 < (4 : ℝ) ^ j := by positivity
  -- 4^{c j / 2} = s^c
  have hlhs : (4 : ℝ) ^ (c / 2 * (j : ℝ)) = s ^ c := by
    rw [hs, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]; ring_nf
  -- t^{-c} = (t⁻¹)^c ≥ (4^j / 8)^c ≥ s^c
  have hinv : s ≤ t⁻¹ := by
    have h1 : (4 : ℝ) ^ j / 8 ≤ t⁻¹ := by
      rw [le_inv_comm₀ (by positivity) ht]
      calc t ≤ 8 / (4 : ℝ) ^ j := htj
        _ = ((4 : ℝ) ^ j / 8)⁻¹ := by rw [inv_div]
    have h2 : s ≤ (4 : ℝ) ^ j / 8 := by
      rw [← hss, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]; nlinarith
    linarith
  rw [hlhs]
  unfold S45.power
  rw [Real.rpow_eq_pow, Real.rpow_neg ht.le, ← Real.inv_rpow ht.le]
  exact Real.rpow_le_rpow hs0 hinv hc.le

/-- **The S45 route.** `TileCrossingStatement → TileTrialBoundStatement`, by
`S45.one_trial` (proved with Golden–Thompson). -/
theorem tileTrialBound_of_crossing (d : ℕ) (C : ℝ) (h : TileCrossingStatement d C) :
    TileTrialBoundStatement d C := by
  obtain ⟨C', hC', t0, ht0, hcross⟩ := h
  obtain ⟨c, hc, t1, ht1, hone⟩ :=
    AgentS45.one_trial_proof AgentS45.goldenThompson_S45 (2 * d + 1) C' hC'
  refine ⟨c, hc, min t0 t1, lt_min ht0 ht1, ?_⟩
  intro m P j T M x hu hj hjm hM hab hx ht
  obtain ⟨ℱ, s, a, hsub⟩ := hcross m P j T M x hu hj hjm hM hab hx (lt_of_lt_of_le ht (min_le_left _ _))
  exact hone (RandomSources (Torus d m) M) (sourcesLaw (Torus d m) M) ℱ s _ a _
    (sweepScale_pos_first (lt_trans (by norm_num) hu.1) m j) (lt_of_lt_of_le ht (min_le_right _ _))
    hsub

/-- An aborted record enters a halted block, whose first trial never fails. -/
theorem localFirstFail_aborted {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ) (x : RunRecord d m)
    (hab : x.aborted = true) : localFirstFail M (tileBlock P j T) x = ∅ := by
  ext ω
  simp only [localFirstFail, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_and]
  intro k hk
  rcases k with _ | k
  · simp [localState_zero, tileBlock, hab, initScratch]
  · have := hk 0 (Nat.succ_pos k)
    simp [localState_zero, tileBlock, hab, initScratch] at this

/-- The first-trial bound of the tile block. For each `C ≥ 1`, given the analytic
analytic core `TileTrialBoundStatement d C`, there are `c > 0` and `N` such that for every
box with `n₀ ≥ N`, `u ∈ (1/4, 1]`, every plan with these `n₀, u`, every sweep index
`n₀ < j ≤ m + 1` (the final sweep is `j = m + 1`), tile `T`, order sizes and good record `x`,
the first trial fails with probability at most `birthBound c j`. -/
theorem tile_first_trial_bound (d : ℕ) (C : ℝ) (hcore : TileTrialBoundStatement d C) :
    ∃ c > 0, ∃ N : ℕ, ∀ n₀ ≥ N, ∀ (m : ℕ) (u : ℝ), u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ (P : TilePlan d m), P.n₀ = n₀ → P.u = u →
      ∀ j, n₀ < j → j ≤ m + 1 → ∀ (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ),
      TileOrderSizes P j T M → ∀ x ∈ TileGood C P j T,
      sourcesLaw (Torus d m) M (localFirstFail M (tileBlock P j T) x) ≤
        ENNReal.ofReal (birthBound c j) := by
  obtain ⟨c, hc, t0, ht0, hcore⟩ := hcore
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < t0 / 8)
    (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨c / 2, by positivity, max N₁ 2, ?_⟩
  intro n₀ hn₀ m u hu P hPn hPu j hj hjm T M hM x hx
  by_cases hab : x.aborted = true
  · rw [localFirstFail_aborted P j T M x hab]; simp
  have hab' : x.aborted = false := by simpa using hab
  have hu' : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 := hPu ▸ hu
  have htpos := sweepScale_pos_first (lt_trans (by norm_num) hu'.1) m j
  have htle := sweepScale_le hu' (by omega : 0 < j) hjm
  have hj3 : 3 ≤ j := by have := le_max_right N₁ 2; omega
  have hjN : N₁ ≤ j := by have := le_max_left N₁ 2; omega
  have hsmall : sweepScale P.u m j < t0 := by
    have h4 : (4 : ℝ) ^ N₁ ≤ (4 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hjN
    have hq : (1 / 4 : ℝ) ^ N₁ = 1 / (4 : ℝ) ^ N₁ := by rw [one_div_pow]
    rw [hq] at hN₁
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ N₁ := by positivity
    have : 8 / (4 : ℝ) ^ j ≤ 8 / (4 : ℝ) ^ N₁ := by
      apply div_le_div_of_nonneg_left (by norm_num) h4pos h4
    have h8 : 8 / (4 : ℝ) ^ N₁ < t0 := by
      rw [div_lt_iff₀ h4pos]; rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 8), div_mul_eq_mul_div,
        one_mul, div_lt_iff₀ h4pos] at hN₁; linarith
    linarith
  have hbound := hcore m P j T M x hu' (hPn ▸ hj) hjm hM hab' (hx hab') hsmall
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  exact exp_le_birthBound hc htpos hj3 htle

end AndersonAC.AgentS78
