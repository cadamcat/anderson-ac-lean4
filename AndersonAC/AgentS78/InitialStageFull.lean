import AndersonAC.AgentS78.StageInduction
import AndersonAC.S3.LargeSymbol
import AndersonAC.S3.Package
import AndersonAC.S3H.LayerCake
import AndersonAC.S3H.PeriodicQuadrature
import AndersonAC.S3H.Fourier

/-!
certificate construction initial stage and stage induction with every §3 input discharged:
`S3.LargeSymbolDecayWStatement` from the helper estimates
(`largeSymbolDecayW_of_helpers`) and the bottom-resolvent estimate in
`InitialStageBR.lean`.
-/

namespace AndersonAC.AgentS78

theorem largeSymbolDecayW_proof : AndersonAC.S3.LargeSymbolDecayWStatement :=
  AndersonAC.S3.largeSymbolDecayW_of_helpers AndersonAC.S3.torusFourier_proof
    AndersonAC.S3.periodicGridQuadrature_proof
    (AndersonAC.S3.bottomResolvent_of_helpers AndersonAC.S3.rayEstimates_proof
      AndersonAC.S3.polarRayBound_proof)
    AndersonAC.S3.jointShellK_proof AndersonAC.S3.layerCake_proof

/-- Unconditional certificate construction initial stage. -/
theorem initial_stage_unconditional {d : ℕ} (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    type_of% (initial_stage_of_decay largeSymbolDecayW_proof hd e₂ he₂) :=
  initial_stage_of_decay largeSymbolDecayW_proof hd e₂ he₂

/-- Unconditional stage invariant along every pathwise history from initialization. -/
theorem stage_bounds_of_initial_unconditional {d : ℕ} (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) (C : ℝ) (hC : 1 ≤ C) :
    type_of% (stage_bounds_of_initial largeSymbolDecayW_proof hd e₂ he₂ C hC) :=
  stage_bounds_of_initial largeSymbolDecayW_proof hd e₂ he₂ C hC

end AndersonAC.AgentS78
