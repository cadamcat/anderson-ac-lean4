import AndersonAC.S6.Statements

/-! Remaining bounded ridge obligations for the section integration. -/
noncomputable section
open scoped Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

def RidgeAlgebraStatement : Prop :=
  ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ),
    AndersonAC.S6.Planned.ridge_calculus C τ hτ

def RidgeGenericLimitsStatement : Prop :=
  ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ),
    AndersonAC.S6.Planned.ridge_limit C ∧
    (∀ (i : R) (τ : ℝ) (hτ : 0 < τ), AndersonAC.S6.Planned.ridge_derivative C i τ hτ) ∧
    (∀ i : R, AndersonAC.S6.Planned.ridge_continuous_monotone C i)

def RidgeSelectionStatement : Prop :=
  ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (l : ℝ) (hl : 0 < l),
    AndersonAC.S6.Planned.ridge_threshold_measurable (B := B) (R := R) l hl ∧
    (∀ (C : Matrix R B ℂ) (hlarge : 2 * l <
      AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C)),
      AndersonAC.S6.Planned.ridge_threshold C l hl hlarge)

def RidgeInitialStatement : Prop :=
  ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l) (hsmall : l < 2) (hC : ‖C‖ ≤ 1),
    AndersonAC.S6.Planned.ridge_initial C l hl hsmall hC

end AndersonAC.SolS6
