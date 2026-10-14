import AndersonAC.AgentS6Row.Predictable
import AndersonAC.AgentS6Row.Conditional
import AndersonAC.AgentS6.Potential

noncomputable section
open MeasureTheory Matrix Finset

namespace AndersonAC.AgentS6Row

open AndersonAC.S6

lemma leverage_le_card {R B : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
    (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) (i : R) : leverage C τ i ≤ Fintype.card B := by
  have hsum : leverage C τ i ≤ ∑ j, leverage C τ j :=
    Finset.single_le_sum (fun j _ => AndersonAC.AgentS6.leverage_nonneg C hτ.le j) (Finset.mem_univ i)
  exact hsum.trans (AndersonAC.AgentS6.totalWeight_leverage_le C hτ)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

set_option maxHeartbeats 1000000 in
lemma recorded_increment_integrable (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) (i : Fin n) :
    Integrable (fun ω => recordedLeverageIncrement q k ω i) μ := by
  classical
  have hw0 : Measurable (fun ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i) :=
    (AndersonAC.AgentS6.measurable_weights q (k := k) (j := k) le_rfl i).mono (q.history.le k) le_rfl
  have hw1 : Measurable (fun ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω) i) :=
    (AndersonAC.AgentS6.measurable_weights q (k := k + 1) (j := k) (Nat.le_succ k) i).mono
      (q.history.le (k + 1)) le_rfl
  have hE : MeasurableSet (survivorEvent q k i) := q.history.le k _ (survivorEvent_measurable q k i)
  have he := recordedIncrement_eq_indicator q k i
  have hfm : Measurable (fun ω => recordedLeverageIncrement q k ω i) := by
    rw [he]
    exact (hw1.sub hw0).indicator hE
  have hb : ∀ ω, |recordedLeverageIncrement q k ω i| ≤ (core.card : ℝ) := by
    intro ω
    rw [congrFun he ω]
    by_cases hω : ω ∈ survivorEvent q k i
    · rw [Set.indicator_of_mem hω]
      have hτ := q.running_ridge k ω hω.1
      have hpost0 := AndersonAC.AgentS6.leverage_nonneg (trialCross t (r ω) (q.state (k + 1) ω)) hτ.le i
      have hpre0 := AndersonAC.AgentS6.leverage_nonneg (trialCross t (r ω) (q.state k ω)) hτ.le i
      have hpost := leverage_le_card (trialCross t (r ω) (q.state (k + 1) ω)) (q.ridge k ω) hτ i
      have hpre := leverage_le_card (trialCross t (r ω) (q.state k ω)) (q.ridge k ω) hτ i
      rw [Fintype.card_coe] at hpost hpre
      change |leverage (trialCross t (r ω) (q.state (k + 1) ω)) (q.ridge k ω) i -
        leverage (trialCross t (r ω) (q.state k ω)) (q.ridge k ω) i| ≤ (core.card : ℝ)
      rw [abs_le]
      constructor <;> linarith only [hpost0, hpre0, hpost, hpre]
    · rw [Set.indicator_of_notMem hω, abs_zero]
      positivity
  exact Integrable.of_bound hfm.aestronglyMeasurable (core.card : ℝ)
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

lemma recorded_increment_condExp_off (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) (i : Fin n) :
    ∀ᵐ ω ∂μ, ω ∉ survivorEvent q k i →
      μ[(fun ω => recordedLeverageIncrement q k ω i) | q.history k] ω = 0 := by
  apply condExp_supported (q.history.le k) (survivorEvent q k i) (survivorEvent_measurable q k i)
    _ (recorded_increment_integrable q μ k i)
  intro ω hω
  rw [congrFun (recordedIncrement_eq_indicator q k i) ω, Set.indicator_of_notMem hω]

end AndersonAC.AgentS6Row
