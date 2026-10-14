import AndersonAC.S78.Definitions
import AndersonAC.S78Chrono.Chrono

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
namespace AndersonAC.SolS78

/-- Field-wise transport between the helper and section birth-process records. -/
theorem chronological_joint_for_section {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : AndersonAC.S78.BirthProcess Ω) (c : ℝ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ,
      μ[(B.event n).indicator (fun _ => (1 : ℝ)) | B.history n] ω ≤
        AndersonAC.S78.birthBound c (B.scale n)) (S : Finset ℕ) :
    μ (⋂ n ∈ S, B.event n) ≤
      ENNReal.ofReal (∏ n ∈ S, AndersonAC.S78.birthBound c (B.scale n)) :=
  chronological_joint_proof μ ⟨B.history, B.event, B.scale, B.adapted⟩ c hbound S

end AndersonAC.SolS78
#print axioms AndersonAC.SolS78.chronological_joint_for_section
