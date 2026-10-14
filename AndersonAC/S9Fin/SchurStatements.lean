import AndersonAC.S9Fin.Core

noncomputable section
open AndersonAC.S9

namespace AndersonAC.SolS9

universe u

/-- Inverting the full matrix and its eliminated block identifies the active
Schur inverse with the compression of the full inverse. Empty blocks are allowed. -/
def SchurCompressionStatement : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (E : ℝ) (A : Finset n),
    IsUnit (H - (E : ℂ) • 1) →
    IsUnit (compress (Finset.univ \ A) (H - (E : ℂ) • 1)) →
    IsUnit (activeSchur H E A) ∧
      (activeSchur H E A)⁻¹ = compress A ((H - (E : ℂ) • 1)⁻¹)

end AndersonAC.SolS9
