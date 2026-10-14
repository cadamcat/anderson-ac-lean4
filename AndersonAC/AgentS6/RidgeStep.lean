import AndersonAC.AgentS6.LeverageFacts
import AndersonAC.AgentS6.HeatDrift

/-! Ridge decreases do not raise the potential (06-clearing.tex:656–668,
equation `clearing-ridge-monotonicity`), for the trial's ridge rule `chooseRidge`. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace AndersonAC.S6

/-- Equation `clearing-ridge-monotonicity`. -/
theorem ridge_potential_monotone {R : Type*} [Fintype R] (l : ℝ) (m n : R → ℝ) (hl : 0 ≤ l)
    (hm : ∀ i, 0 ≤ m i) (hincr : ∀ i, m i ≤ n i) (hcap : ∀ i, n i ≤ 2 * l) :
    Planned.ridge_potential_monotone l m n hl hm hincr hcap := by
  have key : potential l n - potential l m - (-6 * l * (totalWeight n - totalWeight m)) =
      ∑ i, (n i - m i) * (n i + m i - 4 * l) := by
    unfold potential squareWeight totalWeight
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hterm : ∑ i, (n i - m i) * (n i + m i - 4 * l) ≤ 0 :=
    Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (by linarith [hincr i]) (by linarith [hcap i, hincr i])
  have h1 : potential l n - potential l m ≤ -6 * l * (totalWeight n - totalWeight m) := by
    linarith
  refine ⟨h1, ?_⟩
  have : 0 ≤ totalWeight n - totalWeight m := by
    unfold totalWeight
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by linarith [hincr i]
  nlinarith

end AndersonAC.S6

namespace AndersonAC.AgentS6

open AndersonAC.S6

variable {B : Type*} [Fintype B] [DecidableEq B]

theorem maxWeight_leverage_antitone {n : ℕ} (C : Matrix (Fin n) B ℂ) {s τ : ℝ} (hs : 0 < s)
    (hsτ : s ≤ τ) : maxWeight (leverage C τ) ≤ maxWeight (leverage C s) :=
  maxWeight_le (AndersonAC.AgentS6.maxWeight_nonneg _) fun i =>
    (leverage_antitoneOn C i hs (lt_of_lt_of_le hs hsτ) hsτ).trans (le_maxWeight _ i)

/-- One application of the ridge rule never raises `Φ` (06-clearing.tex:656–668). -/
theorem ridge_step {n : ℕ} (C : Matrix (Fin n) B ℂ) {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ)
    (hτ' : 0 < chooseRidge C l τ) :
    potential l (leverage C (chooseRidge C l τ)) ≤ potential l (leverage C τ) := by
  unfold chooseRidge at hτ' ⊢
  split_ifs at hτ' ⊢ with h
  · set S : Set ℝ := {s : ℝ | 0 < s ∧ 2 * l ≤ maxWeight (leverage C s)} with hS
    have hthr : ridgeThreshold C l = sSup S := rfl
    have hbdd : ∀ s ∈ S, s ≤ τ := by
      intro s hs
      by_contra hlt'
      have hlt := lt_of_not_ge hlt'
      have := maxWeight_leverage_antitone C hτ hlt.le
      linarith [hs.2]
    have hle : ridgeThreshold C l ≤ τ := by
      rw [hthr]; exact Real.sSup_le hbdd hτ.le
    set τ' := ridgeThreshold C l
    have hcap : ∀ i, leverage C τ' i ≤ 2 * l := by
      intro j
      by_contra hgt'
      have hgt := lt_of_not_ge hgt'
      have hcont : ContinuousAt (fun s => leverage C s j) τ' :=
        (leverage_continuousOn C j).continuousAt (Ioi_mem_nhds hτ')
      have hev : ∀ᶠ s in 𝓝 τ', 2 * l < leverage C s j :=
        hcont.eventually (lt_mem_nhds hgt)
      obtain ⟨s, hs1, hs2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Ioi τ' ∈ 𝓝[>] τ')).exists
      have hsS : s ∈ S := ⟨lt_trans hτ' hs2, le_trans hs1.le (le_maxWeight _ j)⟩
      have : s ≤ sSup S := le_csSup ⟨τ, hbdd⟩ hsS
      rw [← hthr] at this
      exact absurd hs2 (not_lt.mpr this)
    have hmon := ridge_potential_monotone l (leverage C τ) (leverage C τ') hl.le
      (fun i => leverage_nonneg C hτ.le i)
      (fun i => leverage_antitoneOn C i hτ' hτ hle) hcap
    exact hmon.2
  · exact le_rfl

/-- After a ridge lowering by `chooseRidge` to a positive ridge, every leverage is at most
`2 l` (06-clearing.tex:996–1001, "immediately after the most recent ridge lowering"). -/
theorem chooseRidge_cap {n : ℕ} (C : Matrix (Fin n) B ℂ) {l τ : ℝ} (hτ : 0 < τ)
    (hτ' : 0 < chooseRidge C l τ) :
    chooseRidge C l τ = τ ∨ ∀ i, leverage C (chooseRidge C l τ) i ≤ 2 * l := by
  unfold chooseRidge at hτ' ⊢
  split_ifs at hτ' ⊢ with h
  · right
    set S : Set ℝ := {s : ℝ | 0 < s ∧ 2 * l ≤ maxWeight (leverage C s)} with hS
    have hthr : ridgeThreshold C l = sSup S := rfl
    have hbdd : ∀ s ∈ S, s ≤ τ := by
      intro s hs
      by_contra hlt'
      have hlt := lt_of_not_ge hlt'
      have := maxWeight_leverage_antitone C hτ hlt.le
      linarith [hs.2]
    set τ' := ridgeThreshold C l
    intro j
    by_contra hgt'
    have hgt := lt_of_not_ge hgt'
    have hcont : ContinuousAt (fun s => leverage C s j) τ' :=
      (leverage_continuousOn C j).continuousAt (Ioi_mem_nhds hτ')
    have hev : ∀ᶠ s in 𝓝 τ', 2 * l < leverage C s j :=
      hcont.eventually (lt_mem_nhds hgt)
    obtain ⟨s, hs1, hs2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi τ' ∈ 𝓝[>] τ')).exists
    have hsS : s ∈ S := ⟨lt_trans hτ' hs2, le_trans hs1.le (le_maxWeight _ j)⟩
    have : s ≤ sSup S := le_csSup ⟨τ, hbdd⟩ hsS
    rw [← hthr] at this
    exact absurd hs2 (not_lt.mpr this)
  · left; rfl

end AndersonAC.AgentS6

#print axioms AndersonAC.S6.ridge_potential_monotone
#print axioms AndersonAC.AgentS6.ridge_step
#print axioms AndersonAC.AgentS6.chooseRidge_cap
