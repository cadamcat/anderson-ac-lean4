import AndersonAC.S45.JoinsProof
import AndersonAC.S45.JFourthProof
import AndersonAC.S45.FormDualityProof
import AndersonAC.S45.LagProof
import AndersonAC.S45.LaplacianBoundsProof

/-! Proposition 4.8 (`AndersonAC.S45.ordinary_increment_estimates`,
04-sweep.tex:1167–1245) assembled from `J_bounds`, `laplacian_bounds`, and
`lag_bounds`, with their stated types. The proved input `analytic_prestate_proof`,
`fourth_bounds_proof` and `increment_pullback_proof` are plugged in.
Never imports `Statements.lean`. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45
open AndersonAC.S45

theorem incrementPullback_holds : IncrementPullbackStmt :=
  fun {P H} _ _ _ _ S L B D W Wstar C σ hC hσ hL hneutral hD hB hdual hstack =>
    @increment_pullback_proof P H _ _ _ _ S L B D W Wstar C σ hC hσ hL hneutral hD hB hdual
      hstack

theorem ordinary_increment_estimates_of_bounds
    (hJ : JBoundsStmt) (hLap : LaplacianBoundsStmt) (hLag : LagBoundsStmt) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
      ∀ (P H Ω : Type) [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
        [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (t : ℝ) (s : State P) (Λplus W Wstar : Form P) (S cols : Finset P)
        (B : Matrix P H ℝ) (ξ : P → Ω → ℝ),
        t < t0 → Prestate t C Λplus Wstar s → rowNorm (s.P t) ≤ C * logFactor t →
        (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
        (∀ f, qform (s.D t) f ≤ C * W f) →
        (∀ v, W (B *ᵥ v) ≤ C * l2sq v) →
        (∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y) →
        FamilyTable μ t C C' s S cols B ξ :=
  ordinary_increment_estimates_from_helpers analytic_prestate_proof hJ hLap hLag
    fourth_bounds_proof incrementPullback_holds

/-- Proposition 4.8 with the proved `lag_bounds_proof` plugged in; only
`J_bounds` and `laplacian_bounds` remain as hypotheses. -/
theorem ordinary_increment_estimates_of_J_lap
    (hJ : JBoundsStmt) (hLap : LaplacianBoundsStmt) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
      ∀ (P H Ω : Type) [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
        [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (t : ℝ) (s : State P) (Λplus W Wstar : Form P) (S cols : Finset P)
        (B : Matrix P H ℝ) (ξ : P → Ω → ℝ),
        t < t0 → Prestate t C Λplus Wstar s → rowNorm (s.P t) ≤ C * logFactor t →
        (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
        (∀ f, qform (s.D t) f ≤ C * W f) →
        (∀ v, W (B *ᵥ v) ≤ C * l2sq v) →
        (∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y) →
        FamilyTable μ t C C' s S cols B ξ :=
  ordinary_increment_estimates_of_bounds hJ hLap lag_bounds_proof

/-- Proposition 4.8 with `lag_bounds_proof` and `laplacian_bounds_proof`
plugged in; only `J_bounds` remains as a hypothesis. -/
theorem ordinary_increment_estimates_of_J (hJ : JBoundsStmt) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
      ∀ (P H Ω : Type) [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
        [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (t : ℝ) (s : State P) (Λplus W Wstar : Form P) (S cols : Finset P)
        (B : Matrix P H ℝ) (ξ : P → Ω → ℝ),
        t < t0 → Prestate t C Λplus Wstar s → rowNorm (s.P t) ≤ C * logFactor t →
        (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
        (∀ f, qform (s.D t) f ≤ C * W f) →
        (∀ v, W (B *ᵥ v) ≤ C * l2sq v) →
        (∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y) →
        FamilyTable μ t C C' s S cols B ξ :=
  ordinary_increment_estimates_of_J_lap hJ laplacian_bounds_proof

/-- Proposition 4.8 (`AndersonAC.S45.ordinary_increment_estimates`),
unconditional: all component estimates are proved. -/
theorem ordinary_increment_estimates_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P H Ω : Type) [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℝ) (s : State P) (Λplus W Wstar : Form P) (S cols : Finset P)
    (B : Matrix P H ℝ) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → rowNorm (s.P t) ≤ C * logFactor t →
    (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    (∀ f, qform (s.D t) f ≤ C * W f) →
    (∀ v, W (B *ᵥ v) ≤ C * l2sq v) →
    (∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y) →
    FamilyTable μ t C C' s S cols B ξ :=
  ordinary_increment_estimates_of_J J_bounds_proof

end AndersonAC.AgentS45
