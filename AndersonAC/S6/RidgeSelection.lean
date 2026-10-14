import AndersonAC.S6.RidgeThresholdStatement
import AndersonAC.S6RidgeThresh.Proof
import AndersonAC.S6RidgeSel.RidgeSelection

/-! Ridge threshold and measurable selection with the section's public names. -/
noncomputable section

namespace AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem ridge_threshold (C : Matrix R B ℂ) (l : ℝ)
    (hl : 0 < l) (hlarge : 2 * l < maxWeight (projectionWeight C)) :
    Planned.ridge_threshold C l hl hlarge :=
  AndersonAC.SolS6.ridgeThreshold_scalar_proof B R C l hl hlarge

theorem ridge_threshold_measurable (l : ℝ) (hl : 0 < l) :
    Planned.ridge_threshold_measurable (B := B) (R := R) l hl :=
  (AndersonAC.SolS6.ridgeSelection_proof B R l hl).1

end AndersonAC.S6
#print axioms AndersonAC.S6.ridge_threshold
#print axioms AndersonAC.S6.ridge_threshold_measurable
