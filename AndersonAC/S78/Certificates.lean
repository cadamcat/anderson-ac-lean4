import AndersonAC.S78.Statements
import AndersonAC.Blueprint.Interfaces

/-! The frozen WP10 package type with the remaining construction input explicit.
The construction owner supplies UniformCertificateInput uniformly in dimension
and in each admissible energy parameter. -/
set_option autoImplicit false
noncomputable section

namespace AndersonAC.Blueprint.Packages

theorem certificates_of_uniform_input
    (hengine : ∀ e₂ : ℝ, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) →
      ∀ d : ℕ, 3 ≤ d → AndersonAC.S78.UniformCertificateInput d e₂) :
    (∀ {e₂ : ℝ}, e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) → AndersonAC.Blueprint.WardInput → AndersonAC.Blueprint.BinaryInput → AndersonAC.Blueprint.InitializationInput e₂ → AndersonAC.Blueprint.ConcentrationInput → AndersonAC.Blueprint.DeletionInput → AndersonAC.Blueprint.ScatteringInput → AndersonAC.Blueprint.ResetInput → AndersonAC.Blueprint.CertificateFamily e₂) := by
  intro e₂ he _hw _hb _hi _hc _hd _hs _hr
  exact AndersonAC.S78.certificate_family_of_uniform_input e₂ (hengine e₂ he)

end AndersonAC.Blueprint.Packages

#print axioms AndersonAC.Blueprint.Packages.certificates_of_uniform_input
#print AndersonAC.Blueprint.Packages.certificates_of_uniform_input
