import AndersonAC.S78.Definitions
import AndersonAC.Blueprint.FiniteInputs

/-! helper contract for the row and relative energy outputs of §7.4.
This is a proposition to prove, not an axiom. WardInput is an explicit argument.
-/
set_option autoImplicit false
namespace AndersonAC.SolS78

/-- The diagonal fixed point is supplied by the contraction step. -/
def ResetVariation : Prop :=
  AndersonAC.Blueprint.WardInput →
  ∀ (c C : ℝ), 0 < c → 1 ≤ C →
    ∃ C' a₀ : ℝ, 0 < C' ∧ 0 < a₀ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
        (M : Matrix ι ι ℂ) (r ζ : ι → ℂ) (t : ℝ),
      0 < t → (∀ i j, M i j = M j i ∧ (M i j).im = 0) →
      (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ ‖r i‖ ≤ C) →
      (∀ i, (AndersonAC.S78.resetInverse M r t i i).im ≤ C) →
      ‖ζ‖ ≤ a₀ →
      (∀ i, AndersonAC.S78.resetInverse M (r + ζ) t i i = (r + ζ) i) →
      AndersonAC.S78.ResetOutput M r ζ t C' ∧
      (∀ i, c / 2 ≤ ((r + ζ) i).im ∧ ((r + ζ) i).im ≤ 2 * C) ∧
      C' * ‖ζ‖ ≤ 1 / 2

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.ResetVariation
