import AndersonAC.S6.Ridge

/-! Scalar part of the ridge-selection contract, independent of measurability. -/
namespace AndersonAC.SolS6

def RidgeThresholdStatement : Prop :=
  ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l)
    (hlarge : 2 * l < AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C)),
    AndersonAC.S6.Planned.ridge_threshold C l hl hlarge

end AndersonAC.SolS6
