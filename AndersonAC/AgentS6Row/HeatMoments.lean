import AndersonAC.AgentS6Row.Conditional
import AndersonAC.L64.Residual

open MeasureTheory

namespace AndersonAC.AgentS6Row

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {m : MeasurableSpace Ω}

/-- Restrict conditional residual moments to a predictable running event. -/
theorem condExp_masked_residual_moments
    (hm : m ≤ mΩ) (E : Set Ω) (hE : MeasurableSet[m] E) (t : ℝ)
    (ξ η : Ω → ℝ) (hξI : Integrable ξ μ) (hξsqI : Integrable (fun ω => ξ ω ^ 2) μ)
    (hmean : ∀ᵐ ω ∂μ, ω ∈ E → μ[ξ | m] ω = 0)
    (hsecond : ∀ᵐ ω ∂μ, ω ∈ E → μ[(fun ω => ξ ω ^ 2) | m] ω = t - η ω) :
    μ[E.indicator ξ | m] =ᵐ[μ] 0 ∧
      μ[E.indicator (fun ω => ξ ω ^ 2) | m] =ᵐ[μ]
        (fun ω => t * E.indicator (fun _ => (1 : ℝ)) ω - E.indicator η ω) := by
  have hce1 := condExp_indicator hξI hE
  have hce2 := condExp_indicator hξsqI hE
  refine ⟨?_, ?_⟩
  · filter_upwards [hmean, hce1] with ω hmω hc
    by_cases hω : ω ∈ E
    · rw [hc, Set.indicator_of_mem hω, hmω hω]
      simp
    · rw [hc, Set.indicator_of_notMem hω]
      simp
  · filter_upwards [hsecond, hce2] with ω hsω hc
    by_cases hω : ω ∈ E
    · rw [hc, Set.indicator_of_mem hω, hsω hω]
      simp [Set.indicator_of_mem hω]
    · rw [hc, Set.indicator_of_notMem hω]
      simp [Set.indicator_of_notMem hω]

end AndersonAC.AgentS6Row
