import AndersonAC.AgentS78.InitialStage
import AndersonAC.S3H.BottomResolvent
import AndersonAC.S3H.Ray
import AndersonAC.S3H.Polar

/-!
WP10 initial stage with the §3 bottom-resolvent input discharged
(luna-s3bottom f1e0fe2, muse-s3ray 55ae4ad, muse-s3polar 531e79d, via lane/agent-s3).
The only remaining hypothesis is `S3.LargeSymbolDecayWStatement` (luna-s3symlarge).
-/

namespace AndersonAC.AgentS78

theorem initial_stage_of_decay (hLD : AndersonAC.S3.LargeSymbolDecayWStatement) {d : ℕ}
    (hd : 3 ≤ d) (e₂ : ℝ) (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    type_of% (initial_stage (AndersonAC.S3.bottomResolvent_of_helpers AndersonAC.S3.rayEstimates_proof
      AndersonAC.S3.polarRayBound_proof) hLD hd e₂ he₂) :=
  initial_stage (AndersonAC.S3.bottomResolvent_of_helpers AndersonAC.S3.rayEstimates_proof
    AndersonAC.S3.polarRayBound_proof) hLD hd e₂ he₂

end AndersonAC.AgentS78
