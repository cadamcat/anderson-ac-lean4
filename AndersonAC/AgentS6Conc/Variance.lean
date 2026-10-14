import AndersonAC.AgentS6Conc.Support
import AndersonAC.AgentS6Conc.ScalarIdentity

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS6Conc

theorem convex_posSemidef {n : Type*} [Fintype n] [DecidableEq n] :
    Convex ℝ {A : Matrix n n ℂ | A.PosSemidef} := by
  rw [convex_iff_add_mem]
  intro A hA B hB a b ha hb hab
  change A.PosSemidef at hA
  change B.PosSemidef at hB
  change (a • A + b • B).PosSemidef
  exact (hA.smul ha).add (hB.smul hb)

theorem scalarIdentity_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {a : ℝ} (ha : 0 ≤ a) : ((a : ℝ) • (1 : Matrix n n ℂ)).PosSemidef := by
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one ha

theorem condExp_posSemidef_ae {Ω n : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    (X : Ω → Matrix n n ℂ) (hX : Integrable X μ)
    (hpos : ∀ᵐ ω ∂μ, (X ω).PosSemidef) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).PosSemidef := by
  exact (convex_posSemidef).condExp_mem hm hX Matrix.posSemidef_is_closed hpos

theorem condExp_scalarIdentity_ae {Ω n : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {μ : Measure Ω} {f : Ω → ℝ} (hm : m ≤ mΩ) (hf : Integrable f μ) :
    μ[fun ω => (f ω : ℂ) • (1 : Matrix n n ℂ) | m] =ᵐ[μ]
      fun ω => (μ[f | m] ω : ℂ) • (1 : Matrix n n ℂ) := by
  have h := (scalarIdentityCLM n).comp_condExp_comm (m := m) hf
  simpa [Function.comp_def, scalarIdentityCLM_apply] using h.symm

end AndersonAC.AgentS6Conc

end
