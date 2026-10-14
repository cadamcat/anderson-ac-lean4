import AndersonAC.S6.Supported
import AndersonAC.S6.CoreAlgebra

/-! Numeric transport from a supported scattering change to the scaled inverse. -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

def CompletionBoundsStatement : Prop :=
  ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (t c l : ℝ) (p : R → ℝ) (C : Matrix R B ℂ) (dg ds : Matrix R R ℂ),
    0 < t → 0 < c → 0 ≤ l → (∀ i, c ≤ p i) →
    ‖ds‖ ≤ 2 → AndersonAC.S6.rangeProjection C * ds = ds → ds.IsSymm →
    ds = (2 * Complex.I * (t : ℂ)) •
      (AndersonAC.S6.sqrtDamping p * dg * AndersonAC.S6.sqrtDamping p) →
    (∀ i, AndersonAC.S6.projectionWeight C i ≤ 2 * l) →
    (∀ i j, ‖dg i j‖ ≤ 2 * l / (t * c)) ∧
    (∀ i, AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t dg) i ≤ 2 * l / (t * c ^ 2)) ∧
    (∀ i, AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse t dg) i ≤
      8 * l ^ 3 / (t ^ 2 * c ^ 4)) ∧
    AndersonAC.S6.hsSq (AndersonAC.S6.scaledInverse t dg) ≤
      (Fintype.card B : ℝ) / (t * c ^ 2)

end AndersonAC.SolS6
