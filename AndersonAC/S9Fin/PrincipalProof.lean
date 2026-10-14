import AndersonAC.S9Fin.Principal
import AndersonAC.S9Diag.Diag

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9

namespace AndersonAC.SolS9

theorem true_principal_invertible_ae_proof (d m : ℕ) (coupling E : ℝ) (hcoupling : 0 < coupling) :
    ∀ᵐ ω ∂torusLaw d m, allPrincipalInvertible (periodicHamiltonian coupling ω) E :=
  true_principal_invertible_ae_of_diagonal diagonalInvertibility_proof d m coupling E hcoupling

end AndersonAC.SolS9
