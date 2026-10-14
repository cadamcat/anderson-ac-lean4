import AndersonAC.S78.MatrixReset
import AndersonAC.S78.ResetVariation

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

/-- The full reset conclusion follows from the matrix fixed point and the
separately supplied uniform row/form variation theorem. -/
theorem diagonal_reset_of_variation (hw : AndersonAC.Blueprint.WardInput)
    (hv : ResetVariation) (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ),
      0 < t → t < t₀ → (∀ i j, M i j = M j i ∧ (M i j).im = 0) →
      (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ ‖r i‖ ≤ C) →
      (∀ i, (AndersonAC.S78.resetInverse M r t i i).im ≤ C) →
      AndersonAC.S78.matrixNorm (AndersonAC.S78.squareKernel
        ((Real.sqrt t : ℂ) • AndersonAC.S78.resetInverse M r t)) < 1 / 2 →
      (∀ v : ι → ℂ, ‖((1 - AndersonAC.S78.squareKernel
        ((Real.sqrt t : ℂ) • AndersonAC.S78.resetInverse M r t))⁻¹).mulVec v‖ ≤
        C * Real.log (1 / t) * ‖v‖) →
      ‖AndersonAC.S78.resetLag M r t‖ ≤ t ^ (0.36 * AndersonAC.S78.delta) →
      ∃ ζ : ι → ℂ, ‖ζ‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) ∧
        AndersonAC.S78.ResetOutput M r ζ t C' ∧
        (∀ i, c / 2 ≤ ((r + ζ) i).im ∧ ((r + ζ) i).im ≤ 2 * C) := by
  obtain ⟨C', a₀, hC', ha₀, hvar⟩ := hv hw c C hc hC
  obtain ⟨t₀, ht₀, hreset⟩ := diagonal_reset_exists c C a₀ hc hC ha₀
  refine ⟨C', t₀, hC', ht₀, ?_⟩
  intro ι _ _ _ M r t ht hsmall hM hr hdiag hK hP hlag
  obtain ⟨ζ, hζ, hζa, hfixed, hdamping⟩ :=
    hreset ι M r t ht hsmall hM hr hdiag hK hP hlag
  exact ⟨ζ, hζ, (hvar ι M r ζ t ht hM hr hdiag hζa hfixed).1, hdamping⟩

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.diagonal_reset_of_variation
