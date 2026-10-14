import AndersonAC.S9.HelperStatements
import AndersonAC.S9Inf.BoundaryMeasurable

noncomputable section

namespace AndersonAC.SolS9

theorem BoundarySetMeasurableInput_proof : BoundarySetMeasurableInput := by
  intro Ξ _ g hmeas hcont
  have h := AndersonAC.SolS9Inf.boundaryEventMeasurability_proof (Ξ × ℝ)
    (fun p => g p.1 p.2) hmeas (fun p => hcont p.1 p.2)
  exact ⟨h.1, h.2.1⟩

end AndersonAC.SolS9
