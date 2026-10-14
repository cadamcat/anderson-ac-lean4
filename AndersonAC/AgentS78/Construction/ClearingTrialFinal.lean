import AndersonAC.AgentS78.Construction.ClearingTrialResidual
import AndersonAC.AgentS78Geo.Geo
import AndersonAC.S6.UniformPreparation
import AndersonAC.AgentS6Lev2.Final

/-!
# the clearing first-trial bound, joined

`clearingTrialH_of_geometry` with its inputs supplied:
the geometry by `AgentS78Geo.clearingGeometry_proof` (`geo := clearingGeo d Ctr`),
the uniform Proposition 6.6 by `S6.preparationUniform_proof` and the uniform
drift contract by `AgentS6.leverageDriftUniform_proof` (at universe 0).
The blueprint `ConcentrationInput` stays a hypothesis.
-/

open Filter
open scoped Topology
open AndersonAC.AgentS78Geo (clearingGeo)

namespace AndersonAC.AgentS78

/-- The S6 uniform preparation statement is the consumer's. -/
theorem preparationUniform_of_S6 :
    AndersonAC.S6.PreparationUniformStatement → PreparationUniformStatement :=
  fun h => h

/-- The AgentS6 uniform drift statement at universe 0 is the consumer's. -/
theorem leverageDriftUniform_of_AgentS6 :
    AndersonAC.AgentS6.LeverageDriftUniformStatement.{0} → LeverageDriftUniformStatement :=
  fun h => h

theorem preparationUniform_proof : PreparationUniformStatement :=
  preparationUniform_of_S6 AndersonAC.S6.preparationUniform_proof

theorem leverageDriftUniform_proof : LeverageDriftUniformStatement :=
  leverageDriftUniform_of_AgentS6 AndersonAC.AgentS6.leverageDriftUniform_proof.{0}

/-- **clearing trial bound: the clearing first-trial bound (query-history variant)** for the geometry
`clearingGeo d Ctr`, conditional only on the blueprint concentration input. -/
theorem clearingTrialH_proof (d : ℕ) (hd : 3 ≤ d)
    (hconc : AndersonAC.Blueprint.ConcentrationInput)
    (cP CP : ℝ) (qlag : ℝ → ℝ) (hcP : 0 < cP) (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (Ctr : ℝ) (hCtr : 1 ≤ Ctr) :
    ClearingTrialStatementH d (ClearingGood d cP CP qlag (clearingGeo d Ctr)) :=
  clearingTrialH_of_geometry hd preparationUniform_proof leverageDriftUniform_proof hconc
    cP CP qlag hqlag (clearingGeo d Ctr)
    (AndersonAC.AgentS78Geo.clearingGeometry_proof hd cP CP hcP qlag Ctr hCtr)

/-- `ClearingTrialStatementH` extends `ClearingTrialStatement` so both carry
the query-history hypothesis). -/
theorem clearingTrial_of_H (d : ℕ) (good : ∀ {m : ℕ}, ℕ → ℝ → ℝ → ℕ → Set (RunRecord d m)) :
    ClearingTrialStatementH d good → ClearingTrialStatement d good :=
  fun h => h

/-- **clearing trial bound (contract form).** -/
theorem clearingTrial_proof (d : ℕ) (hd : 3 ≤ d)
    (hconc : AndersonAC.Blueprint.ConcentrationInput)
    (cP CP : ℝ) (qlag : ℝ → ℝ) (hcP : 0 < cP) (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (Ctr : ℝ) (hCtr : 1 ≤ Ctr) :
    ClearingTrialStatement d (ClearingGood d cP CP qlag (clearingGeo d Ctr)) :=
  clearingTrial_of_H d _ (clearingTrialH_proof d hd hconc cP CP qlag hcP hqlag Ctr hCtr)

end AndersonAC.AgentS78
