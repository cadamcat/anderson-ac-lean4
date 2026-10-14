import AndersonAC.S6RidgeLim.RidgeLimitGeneric
import AndersonAC.S6RidgeLim.RidgeDerivativeGeneric

/-! Generic finite-index ridge limits and inverse-square monotonicity. -/

noncomputable section

open Filter
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

/-- The exact contract, expanded here so the proof does not import its
sorry-carrying statement module. -/
theorem ridgeGenericLimits_proof :
    ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
      (C : Matrix R B ℂ),
      Tendsto (AndersonAC.S6.ridgeProjection C) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (AndersonAC.S6.rangeProjection C)) ∧
      (∀ (i : R) (τ : ℝ) (hτ : 0 < τ),
        HasDerivAt (fun s => AndersonAC.S6.leverage C s i)
          (-((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
            (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re) τ ∧
        0 ≤ ((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
          (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re) ∧
      (∀ i : R,
        ContinuousOn (fun τ => AndersonAC.S6.leverage C τ i) (Set.Ioi 0) ∧
        AntitoneOn (fun τ => AndersonAC.S6.leverage C τ i) (Set.Ioi 0) ∧
        ((∃ b, C i b ≠ 0) →
          StrictAntiOn (fun τ => AndersonAC.S6.leverage C τ i) (Set.Ioi 0))) := by
  intro B R hB hBdec hR hRdec C
  refine ⟨AndersonAC.SolS6RidgeLim.ridgeLimit_proof B R C, ?_, ?_⟩
  · intro i τ hτ
    exact AndersonAC.SolS6RidgeLim.ridgeDerivative_proof C i τ hτ
  · intro i
    let f : ℝ → ℝ := fun τ => AndersonAC.S6.leverage C τ i
    have hD : ∀ τ, 0 < τ →
        HasDerivAt f
          (-((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
            (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re) τ := by
      intro τ hτ
      simpa [f] using
        (AndersonAC.SolS6RidgeLim.ridgeDerivative_proof C i τ hτ).1
    have hQ : ∀ τ, 0 < τ →
        0 ≤ ((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
          (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re := by
      intro τ hτ
      exact (AndersonAC.SolS6RidgeLim.ridgeDerivative_proof C i τ hτ).2
    have hcont : ContinuousOn f (Set.Ioi 0) := by
      intro τ hτ
      exact (hD τ (Set.mem_Ioi.mp hτ)).continuousAt.continuousWithinAt
    refine ⟨hcont, ?_, ?_⟩
    · apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ)) hcont
      · intro τ hτ
        have hτmem : τ ∈ Set.Ioi (0 : ℝ) := by
          simpa only [interior_Ioi] using hτ
        exact (hD τ (Set.mem_Ioi.mp hτmem)).differentiableAt.differentiableWithinAt
      · intro τ hτ
        have hτmem : τ ∈ Set.Ioi (0 : ℝ) := by
          simpa only [interior_Ioi] using hτ
        rw [(hD τ (Set.mem_Ioi.mp hτmem)).deriv]
        exact neg_nonpos.mpr (hQ τ (Set.mem_Ioi.mp hτmem))
    · intro hrow
      apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ)) hcont
      intro τ hτ
      have hτmem : τ ∈ Set.Ioi (0 : ℝ) := by
        simpa only [interior_Ioi] using hτ
      have hτpos : 0 < τ := Set.mem_Ioi.mp hτmem
      rw [(hD τ hτpos).deriv]
      exact neg_neg_of_pos
        (AndersonAC.SolS6RidgeLim.ridge_projection_pos_of_row_nonzero
          B R C τ hτpos i hrow)

end AndersonAC.SolS6
