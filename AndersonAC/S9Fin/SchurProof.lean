import AndersonAC.S9Fin.Schur
import AndersonAC.S9Schur.Schur

noncomputable section
open AndersonAC.S9

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem active_resolvent_compression_proof (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) (hprincipal : allPrincipalInvertible H E) (A : Finset n) :
    (activeSchur H E A - (η * Complex.I) • 1)⁻¹ =
      dampingFunction η (compress A ((H - (E : ℂ) • 1)⁻¹)) := by
  exact active_resolvent_compression_of_schur schurCompression_proof H hH E η hη
    hprincipal A

end AndersonAC.SolS9
