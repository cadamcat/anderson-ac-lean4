import AndersonAC.S6.RidgeThresholdStatement
import AndersonAC.S6RidgeThresh.Proof

namespace AndersonAC.SolS6

theorem ridgeThreshold_proof : RidgeThresholdStatement := by
  intro B R instB instDecB instR instDecR C l hl hlarge
  exact ridgeThreshold_scalar_proof B R C l hl hlarge

example : RidgeThresholdStatement := ridgeThreshold_proof

#print axioms ridgeThreshold_proof

end AndersonAC.SolS6
