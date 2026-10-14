import AndersonAC.S6.Projection

/-! Frozen independent helper contracts for full-range clearing.
Each helper proves a `_proof` theorem with exactly one of these propositions.
There are no new axioms or planning holes here. -/
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
open Filter

namespace AndersonAC.SolS6

/-- Paper §6, lines 340–358; every nonzero singular direction survives the limit. -/
def RidgeLimitStatement : Prop :=
  ∀ (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ),
    Tendsto (AndersonAC.S6.ridgeProjection C) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (AndersonAC.S6.rangeProjection C))

/-- Paper §6, lines 357–362; fixed-matrix positive-ridge derivative and sign. -/
def RidgeDerivativeStatement : Prop :=
  ∀ (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ) (i : Fin n) (τ : ℝ), 0 < τ →
    HasDerivAt (fun s => AndersonAC.S6.leverage C s i)
      (-((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
        (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re) τ ∧
    0 ≤ ((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
      (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re

/-- Paper §6, lines 138–167; symmetric norm-bounded change supported in Ran C. -/
def SupportedChangeBoundStatement : Prop :=
  ∀ (b n : ℕ) (C : Matrix (Fin n) (Fin b) ℂ) (D : Matrix (Fin n) (Fin n) ℂ),
    ‖D‖ ≤ 2 → AndersonAC.S6.rangeProjection C * D = D → D.IsSymm →
    D = AndersonAC.S6.rangeProjection C * D * (AndersonAC.S6.rangeProjection C).map star ∧
    (∀ i j, ‖D i j‖ ≤ 2 * Real.sqrt
      (AndersonAC.S6.projectionWeight C i * AndersonAC.S6.projectionWeight C j)) ∧
    (∀ i, AndersonAC.S6.sqRow D i ≤ 4 * AndersonAC.S6.projectionWeight C i) ∧
    AndersonAC.S6.hsSq D ≤ 4 * (b : ℝ)

end AndersonAC.SolS6
