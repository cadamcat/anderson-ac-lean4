import AndersonAC.Blueprint.SpectralInputs

/-! Shared §9 definitions for proof modules. This file has no proof
placeholders and is independent of the Phase 1 statement inventory. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology

namespace AndersonAC.SolS9

def borelTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  AndersonAC.Blueprint.borelTransform μ z

def verticalBoundary (g : ℂ → ℂ) (E : ℝ) (w : ℂ) : Prop :=
  AndersonAC.Blueprint.HasBoundary g E w

def finiteBoundary (g : ℂ → ℂ) (E : ℝ) : Prop :=
  ∃ w : ℂ, verticalBoundary g E w

def positiveBoundary (g : ℂ → ℂ) (E : ℝ) : Prop :=
  AndersonAC.Blueprint.FinitePositiveBoundary g E

def siteVector {d : ℕ} (x : Site d) : StateSpace d := AndersonAC.Blueprint.delta x

end AndersonAC.SolS9

/- Compatibility aliases for the frozen section-worker records. They share
   the actual Blueprint definitions and introduce no proof assumptions. -/
namespace AndersonAC.S9
abbrev borelTransform := AndersonAC.SolS9.borelTransform
abbrev verticalBoundary := AndersonAC.SolS9.verticalBoundary
abbrev finiteBoundary := AndersonAC.SolS9.finiteBoundary
abbrev positiveBoundary := AndersonAC.SolS9.positiveBoundary
abbrev siteVector {d : ℕ} (x : OAI.Anderson.Site d) := AndersonAC.SolS9.siteVector x
end AndersonAC.S9
