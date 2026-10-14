import AndersonAC.S45.TrialInputsProof
import AndersonAC.S45.MatrixProbProof

/-! `ordered_trial_inputs` made unconditional with luna-s45prob's
`conditionalCenteringFixed_proof`. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

theorem ordered_trial_inputs_proof :
    ∀ (d : ℕ) (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (s M : ℕ) (t : ℝ) (a : OrderedRawBounds μ ℱ s M t C),
    0 < t → t < t0 → 0 < M → (M : ℝ) ≤ C * power t (-6 * (d : ℝ)) →
    (∑ i, (a.dimension i : ℝ)) ≤ C * power t (-6 * (d : ℝ)) →
    ∃ b : TrialInputs μ ℱ s d t C', b.kind = a.kind ∧ b.dimension = a.dimension ∧
      (∀ i k ω, HEq (b.raw i k ω) (a.raw i k ω)) :=
  ordered_trial_inputs_of conditionalCenteringFixed_proof

end AndersonAC.AgentS45
