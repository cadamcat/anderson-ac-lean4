import AndersonAC.AgentS78.Construction.FinishClosed2
import AndersonAC.AgentS78.Construction.ClearingBlockCheck
import AndersonAC.S78.Certificates

/-!
# WP10: the final join (lead, agent-s78con4)

`uniformCertificateInput_of_tileTrial`: sol-s78's target
`∀ e₂ ∈ (0, 1/100), ∀ d ≥ 3, S78.UniformCertificateInput d e₂` from the C4a one-trial contract
alone (clearing-block measurability, `clearingBlock_measurable`, is plugged in).
`certificates_of_tileTrial`: the exact type of `Packages.certificates` from the same input, via
`Packages.certificates_of_uniform_input` (lane/sol-s78 1935ab3).

When A2 (`TileMonitorBoundsStatement2`, luna-s78a2 / agent-s78a2) lands, the one-trial contract is
`tileTrialBound_of_crossing d C (tileCrossing_of_pieces2 d C tileSlotDescription_proof
tileSlotLaw_proof (hA2 C hC) (tileFailCrossing_of_transfer d C (tileTransfer_proof d C hC)))`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- sol-s78's construction input from the C4a one-trial contract. -/
theorem uniformCertificateInput_of_tileTrial
    (hTTB : ∀ d : ℕ, 3 ≤ d → ∀ C : ℝ, 1 ≤ C → TileTrialBoundStatement d C) :
    ∀ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) → ∀ d : ℕ, 3 ≤ d → UniformCertificateInput d e₂ :=
  fun e₂ he d hd => uniformCertificateInput_closedMT d hd e₂ he
    (fun _ n₀ j u y => clearingBlock_measurable n₀ j u y) (hTTB d hd)

/-- **The frozen WP10 package type** from the C4a one-trial contract. -/
theorem certificates_of_tileTrial
    (hTTB : ∀ d : ℕ, 3 ≤ d → ∀ C : ℝ, 1 ≤ C → TileTrialBoundStatement d C) :
    (∀ {e₂ : ℝ}, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) → AndersonAC.Blueprint.WardInput → AndersonAC.Blueprint.BinaryInput → AndersonAC.Blueprint.InitializationInput e₂ → AndersonAC.Blueprint.ConcentrationInput → AndersonAC.Blueprint.DeletionInput → AndersonAC.Blueprint.ScatteringInput → AndersonAC.Blueprint.ResetInput → AndersonAC.Blueprint.CertificateFamily e₂) :=
  AndersonAC.Blueprint.Packages.certificates_of_uniform_input
    (uniformCertificateInput_of_tileTrial hTTB)

end AndersonAC.AgentS78

#print axioms AndersonAC.AgentS78.uniformCertificateInput_of_tileTrial
#print axioms AndersonAC.AgentS78.certificates_of_tileTrial
