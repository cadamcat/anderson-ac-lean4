import AndersonAC.AgentS78.Construction.TileCoreA2Bounds
import AndersonAC.AgentS78.Construction.WP10Join

/-! WP10: the certificates package. The C4a one-trial bound is assembled from the slot
description (A0), the slot law (A1), the monitor bounds (A2, input constant 2) and the
transfer step (A3b); the random multiscale construction then gives the uniform certificate
input, and `certificates_of_uniform_input` the frozen package type. -/
set_option autoImplicit false
noncomputable section

namespace AndersonAC.Blueprint.Packages

open AndersonAC.AgentS78

theorem certificates {e₂ : ℝ} (he : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hw : WardInput) (hb : BinaryInput) (hi : InitializationInput e₂)
    (hc : ConcentrationInput) (hd : DeletionInput) (hs : ScatteringInput)
    (hr : ResetInput) : CertificateFamily e₂ :=
  certificates_of_tileTrial
    (fun d _ C hC => tileTrialBound_of_crossing d C
      (tileCrossing_of_pieces2 d C tileSlotDescription_proof tileSlotLaw_proof
        (tileMonitorBounds2_proof d C hC)
        (tileFailCrossing_of_transfer d C (tileTransfer_proof d C hC))))
    he hw hb hi hc hd hs hr

end AndersonAC.Blueprint.Packages

#print axioms AndersonAC.Blueprint.Packages.certificates
