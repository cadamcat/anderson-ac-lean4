import Mathlib

open MeasureTheory
open scoped ENNReal
namespace AndersonAC.SolS45

/-- helper contract: Ville's inequality for a nonnegative real
supermartingale, with an infinite horizon and only a.e. nonnegativity. -/
def VilleStatement : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (D b : ℝ),
    Supermartingale Z ℱ μ →
    (∀ n, ∀ᵐ ω ∂μ, 0 ≤ Z n ω) →
    (∀ᵐ ω ∂μ, Z 0 ω ≤ D) → 0 ≤ D → 0 < b →
    μ {ω | ∃ n : ℕ, b ≤ Z n ω} ≤ ENNReal.ofReal (D / b)

end AndersonAC.SolS45
