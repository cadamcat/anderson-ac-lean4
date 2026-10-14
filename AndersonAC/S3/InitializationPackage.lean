import AndersonAC.S3.Final
import AndersonAC.S3.LargeSymbol
import AndersonAC.S3H.LayerCake
import AndersonAC.Blueprint.Interfaces

/-!
WP05: `Packages.initialization`, proved with every §3 helper discharged, and the
normalized §3 endpoint (planned `initialization_normalized`) unconditionally.
-/

noncomputable section

namespace AndersonAC.S3

theorem largeSymbolDecayW_proof : LargeSymbolDecayWStatement :=
  largeSymbolDecayW_of_helpers torusFourier_proof periodicGridQuadrature_proof
    bottomResolvent_proof jointShellK_proof layerCake_proof

theorem initialization_normalized_proof {d : ℕ} (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    type_of% (initialization_normalized_of_decay largeSymbolDecayW_proof hd e₂ he₂) :=
  initialization_normalized_of_decay largeSymbolDecayW_proof hd e₂ he₂

theorem initializationInput_proof {e₂ : ℝ} (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    AndersonAC.Blueprint.InitializationInput e₂ :=
  initializationInput_of_BR_decay bottomResolvent_proof largeSymbolDecayW_proof he₂

end AndersonAC.S3

theorem AndersonAC.Blueprint.Packages.initialization :
    ∃ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) ∧ AndersonAC.Blueprint.InitializationInput e₂ :=
  ⟨1 / 200, by norm_num, AndersonAC.S3.initializationInput_proof (by norm_num)⟩

#print axioms AndersonAC.Blueprint.Packages.initialization
#print axioms AndersonAC.S3.initialization_normalized_proof
