import Mathlib

/-! Frozen helper request: Schur row/column bound for the localization commutator.
Paper: 06-clearing.tex, lines 226–234. The norm is the Euclidean operator norm.
No new axiom or proof hole is introduced by this proposition. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

def SchurNormBoundStatement : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) (u v : ℝ),
    0 ≤ u → 0 ≤ v →
    (∀ i, ∑ j, ‖A i j‖ ≤ u) → (∀ j, ∑ i, ‖A i j‖ ≤ v) →
    ‖A‖ ≤ Real.sqrt (u * v)

end AndersonAC.SolS6
