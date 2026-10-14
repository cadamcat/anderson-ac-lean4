import AndersonAC.AgentS6.CrossNorm
import AndersonAC.AgentS6.RidgeStep
import AndersonAC.S6RidgeInit.RidgeInitial

/-! At the trial start every leverage is at most `2 l_*` (06-clearing.tex:680–688, 996–1001:
"at initialization ... its leverage was at most `2l_*`"): the start ridge `l_*^{-2}` gives
`m_* ≤ l_*² < 2l_*`, and a lowering stops at `2l_*`. -/

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

theorem initial_weights_cap {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
    {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))} (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ht1 : t ≤ 1) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (hstop : 0 < q.stop ω)
    (i : Fin n) :
    trialWeights t (r ω) (q.state 0 ω) (q.ridge 0 ω) i ≤ 2 * leverageScale t := by
  set l := leverageScale t
  set C := trialCross t (r ω) (q.state 0 ω)
  have hl : 0 < l := Real.rpow_pos_of_pos ht _
  have hl1 : l ≤ 1 := Real.rpow_le_one ht.le ht1 (by unfold e0 delta; norm_num)
  have hτ : 0 < l ^ (-2 : ℤ) := zpow_pos hl _
  have h0 := q.running_ridge 0 ω hstop
  rw [q.start_ridge ω] at h0 ⊢
  rcases chooseRidge_cap C hτ h0 with h | h
  · rw [h]
    have hC := trialCross_norm_le_one ht (r ω) hr (q.state 0 ω)
    obtain ⟨h1, h2⟩ := AndersonAC.SolS6.ridgeInitial_proof _ _ C l hl (by linarith) hC
    calc leverage C (l ^ (-2 : ℤ)) i ≤ maxWeight (leverage C (l ^ (-2 : ℤ))) := le_maxWeight _ i
      _ ≤ l ^ 2 := h1
      _ ≤ 2 * l := h2.le
  · exact h i

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.initial_weights_cap
