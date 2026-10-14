import AndersonAC.AgentS78.Construction.FinishClosed2
import AndersonAC.AgentS78.Construction.ClearingBlockCheck
import AndersonAC.S78.Certificates

/-!
# Final certificate join

`uniformCertificateInput_of_tileTrial` proves
`∀ e₂ ∈ (0, 1/100), ∀ d ≥ 3, S78.UniformCertificateInput d e₂` from the tile trial one-trial contract
alone (clearing-block measurability, `clearingBlock_measurable`, is plugged in).
`certificates_of_tileTrial`: the exact type of `Packages.certificates` from the same input, via
`Packages.certificates_of_uniform_input`.

Given `TileMonitorBoundsStatement2`, the one-trial contract is
`tileTrialBound_of_crossing d C (tileCrossing_of_pieces2 d C tileSlotDescription_proof
tileSlotLaw_proof (hmonitor bounds C hC) (tileFailCrossing_of_transfer d C (tileTransfer_proof d C hC)))`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- construction input from the tile trial one-trial contract. -/
theorem uniformCertificateInput_of_tileTrial
    (hTTB : ∀ d : ℕ, 3 ≤ d → ∀ C : ℝ, 1 ≤ C → TileTrialBoundStatement d C) :
    ∀ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) → ∀ d : ℕ, 3 ≤ d → UniformCertificateInput d e₂ :=
  fun e₂ he d hd => uniformCertificateInput_closedMT d hd e₂ he
    (fun _ n₀ j u y => clearingBlock_measurable n₀ j u y) (hTTB d hd)

/-- Certificate package type from the tile-trial bound. -/
theorem certificates_of_tileTrial
    (hTTB : ∀ d : ℕ, 3 ≤ d → ∀ C : ℝ, 1 ≤ C → TileTrialBoundStatement d C) :
    (∀ {e₂ : ℝ}, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) → AndersonAC.Blueprint.WardInput → AndersonAC.Blueprint.BinaryInput → AndersonAC.Blueprint.InitializationInput e₂ → AndersonAC.Blueprint.ConcentrationInput → AndersonAC.Blueprint.DeletionInput → AndersonAC.Blueprint.ScatteringInput → AndersonAC.Blueprint.ResetInput → AndersonAC.Blueprint.CertificateFamily e₂) :=
  AndersonAC.Blueprint.Packages.certificates_of_uniform_input
    (uniformCertificateInput_of_tileTrial hTTB)

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.uniformCertificateInput_of_tileTrial
#print axioms AndersonAC.AgentS78.certificates_of_tileTrial
