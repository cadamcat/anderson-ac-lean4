import AndersonAC.S78Hist.Scalar

open AndersonAC.SolS78hist
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

theorem close_history_recursion_proof (d : ℕ) (hd : 3 ≤ d) (c C : ℝ)
    (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ n₀ J, N ≤ n₀ → ∀ Z : ℕ → ℝ, (∀ j, 0 ≤ Z j) → Z n₀ = 0 →
      (∀ j, n₀ < j → j ≤ J → Z j ≤ recursionBound d n₀ j c C Z) →
      ∀ j, n₀ ≤ j → j ≤ J → Z j ≤ birthBound (historyExponent d c) j := by
  obtain ⟨N, hN, hleaf, hbranch⟩ := scalar_bounds d hd c C hc hC
  have ha : historyAlpha d < 1 := (parameters d hd c hc).2.1
  refine ⟨N, ?_⟩
  intro n₀ J hn₀ Z hZ hinit hrec j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hJ
    by_cases heq : j = n₀
    · subst j
      rw [hinit]
      exact Real.exp_nonneg _
    · have hn₀j : n₀ < j := by omega
      have hl := hleaf n₀ j hn₀ hn₀j
      have hz := hrec j hn₀j hJ
      unfold recursionBound at hz
      by_cases hr : n₀ ≤ historyEarlier d j
      · rw [if_pos hr] at hz
        have hrj := earlier_lt d j ha (by omega)
        have hp := ih (historyEarlier d j) hrj hr (hrj.le.trans hJ)
        have hb := hbranch n₀ j (Z (historyEarlier d j)) hn₀ hn₀j hr
          (hZ (historyEarlier d j)) hp
        linarith
      · rw [if_neg hr, add_zero] at hz
        have hnonneg : 0 ≤ birthBound (historyExponent d c) j := Real.exp_nonneg _
        linarith

end AndersonAC.SolS78
