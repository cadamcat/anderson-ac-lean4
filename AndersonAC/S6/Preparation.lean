import AndersonAC.AgentS6.Final
import AndersonAC.AgentS6Budget.Final
import AndersonAC.AgentS6Cap.CapTail

/-! Proposition 6.6 with the proved distortion-budget and leverage-cap tails. -/

noncomputable section
open MeasureTheory Filter

namespace AndersonAC.S6

open AndersonAC.AgentS6
universe u

theorem preparation_of_small_component_of_cap_tail
    (hCap : CapTailStatement.{u})
    {Ω : Type u} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    Planned.preparation_of_small_component d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε
      hqlag hε hεpos :=
  preparation_of_small_component_of_concentration_tails budgetTail_proof hCap
    d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε hqlag hε hεpos

/-- Proposition 6.6, with both concentration failure modes discharged. The
trial, local input, vector concentration and running-event drift input are
the hypotheses of the original planned statement. -/
theorem preparation_of_small_component
    {Ω : Type u} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    Planned.preparation_of_small_component d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε
      hqlag hε hεpos :=
  preparation_of_small_component_of_cap_tail capTail_proof
    d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε hqlag hε hεpos

end AndersonAC.S6

#print axioms AndersonAC.S6.preparation_of_small_component_of_cap_tail
#print axioms AndersonAC.S6.preparation_of_small_component
