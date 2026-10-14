import AndersonAC.AgentS6.Count
import AndersonAC.AgentS6.Frozen
import AndersonAC.S2.WardPackage
import AndersonAC.S6Heat.HeatCount

/-! Proposition 6.6 (06-clearing.tex:826–850) from: the §2 Ward input, Lemma 6.5
(`HeatCountStatement`), and the two frozen concentration failure modes
(`BudgetTailStatement`, `CapTailStatement`). The heat-limit mode is proved here. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace AndersonAC.S6

open AndersonAC.AgentS6

universe u

theorem preparation_of_small_component_of (hWard : AndersonAC.Blueprint.WardInput)
    (hHC : AndersonAC.SolS6.HeatCountStatement.{u})
    (hBudget : BudgetTailStatement.{u}) (hCap : CapTailStatement.{u})
    {Ω : Type u} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    Planned.preparation_of_small_component d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε
      hqlag hε hεpos :=
  preparation_of_modes hWard d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε hqlag hε hεpos
    (countTail_of_heatCount hHC d hd c K Cloc cConc μ qlag ε hε hεpos)
    (hBudget Ω d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε hqlag hε hεpos)
    (hCap Ω d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε hqlag hε hεpos)

/-- The same with the proved §2 Ward package (WP03, `main`). -/
theorem preparation_of_small_component_of_tails
    (hHC : AndersonAC.SolS6.HeatCountStatement.{u})
    (hBudget : BudgetTailStatement.{u}) (hCap : CapTailStatement.{u})
    {Ω : Type u} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    Planned.preparation_of_small_component d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε
      hqlag hε hεpos :=
  preparation_of_small_component_of AndersonAC.Blueprint.Packages.ward hHC hBudget hCap
    d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε hqlag hε hεpos

/-- The same with the proved Lemma 6.5 (luna-s6heat) and Ward package: only the two frozen
concentration failure modes remain as hypotheses. -/
theorem preparation_of_small_component_of_concentration_tails
    (hBudget : BudgetTailStatement.{u}) (hCap : CapTailStatement.{u})
    {Ω : Type u} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (hc : 0 < c) (hK : 1 ≤ K) (hCloc : 0 ≤ Cloc) (hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    Planned.preparation_of_small_component d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε
      hqlag hε hεpos :=
  preparation_of_small_component_of_tails AndersonAC.SolS6.heatCount_proof hBudget hCap
    d hd c K Cloc cConc hc hK hCloc hConc μ qlag ε hqlag hε hεpos

end AndersonAC.S6

#print axioms AndersonAC.S6.preparation_of_small_component_of
#print axioms AndersonAC.S6.preparation_of_small_component_of_tails
#print axioms AndersonAC.S6.preparation_of_small_component_of_concentration_tails
