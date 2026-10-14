import AndersonAC.AgentS6Budget.ScalarVectorTail
import AndersonAC.AgentS6Budget.RankOne

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def streamEvent {D : ℕ} (N : ℕ) (a : ℝ) (X : ℕ → Ω → EuclideanSpace ℂ (Fin D)) : Set Ω :=
  {ω | ∃ m ≤ N, a < ‖∑ k ∈ Finset.range m, X k ω‖}

theorem streamEvent_measurable {D : ℕ} (N : ℕ) (a : ℝ)
    (X : ℕ → Ω → EuclideanSpace ℂ (Fin D)) (hX : ∀ k, StronglyMeasurable (X k)) :
    MeasurableSet (streamEvent N a X) := by
  have heq : streamEvent N a X = ⋃ m : ℕ, ⋃ (_ : m ≤ N),
      {ω | a < ‖∑ k ∈ Finset.range m, X k ω‖} := by
    ext ω
    simp [streamEvent]
  rw [heq]
  apply MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => ?_
  have hm : StronglyMeasurable (fun ω => ∑ k ∈ Finset.range m, X k ω) := by
    have he : (fun ω => ∑ k ∈ Finset.range m, X k ω) = ∑ k ∈ Finset.range m, X k := by
      funext ω
      simp
    rw [he]
    exact Finset.stronglyMeasurable_sum _ (fun k _ => hX k)
  exact measurableSet_lt measurable_const hm.norm.measurable

theorem scalar_vector_tail_of_squares (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (c : ℝ) (hconc : VectorConcentrationInput μ F c)
    (D N : ℕ) (A : ℕ → Ω → ℂ) (U : ℕ → Ω → EuclideanSpace ℂ (Fin D))
    (L M S H a : ℝ) (hL : 0 < L) (hM : 0 ≤ M)
    (hS : 0 < S) (hH : 0 < H) (ha : 0 < a)
    (hAm : ∀ k, StronglyMeasurable[F (k + 1)] (A k))
    (hUm : ∀ k, StronglyMeasurable[F k] (U k))
    (hAL : ∀ k ω, ‖A k ω‖ ≤ L) (hUH : ∀ k ω, ‖U k ω‖ ≤ H)
    (hAM : ∀ k, ∀ᵐ ω ∂μ, ‖μ[A k | F k] ω‖ ≤ M)
    (hUS : ∀ ω, ∑ k ∈ Finset.range N, ‖U k ω‖ ^ 2 ≤ S)
    (hbias : M * Real.sqrt ((N : ℝ) * S) ≤ a / 2) :
    ∀ᵐ ω ∂μ, conditionalProbability μ (F 0)
      (streamEvent N a (fun k ω => A k ω • U k ω)) ω ≤
      2 * (D + 1) * Real.exp
        (-c * min ((a / 2) ^ 2 / (4 * (L ^ 2 * S))) ((a / 2) / (2 * (L * H)))) := by
  have hUR : ∀ ω, ∑ k ∈ Finset.range N, ‖U k ω‖ ≤ Real.sqrt ((N : ℝ) * S) := by
    intro ω
    have h := sum_norm_le_sqrt_card_mul_square (Finset.range N) (fun k => U k ω)
    simp only [Finset.card_range] at h
    exact h.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hUS ω) (Nat.cast_nonneg N)))
  exact scalar_vector_tail μ F c hconc D N A U L M (Real.sqrt ((N : ℝ) * S)) S H a
    hL hM (Real.sqrt_nonneg _) hS hH ha hAm hUm hAL hUH hAM hUR hUS hbias

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.scalar_vector_tail_of_squares
