import AndersonAC.S78.TaylorReset
import AndersonAC.S78.NumericalReset

set_option autoImplicit false
namespace AndersonAC.SolS78

/-- Uniform reset existence after the matrix remainder and inverse-row estimates
have been supplied. The scalar cutoff precedes every finite active type. -/
theorem reset_from_uniform_taylor (C δ : ℝ) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
      (diagonal : (ι → ℂ) → ι → ℂ) (r : ι → ℂ)
      (K P : Matrix ι ι ℂ) (R : (ι → ℂ) → ι → ℂ) (t : ℝ),
      0 < t → t < t₀ → (1 - K) * P = 1 →
      (∀ v : ι → ℂ, ‖P.mulVec v‖ ≤ C * Real.log (1 / t) * ‖v‖) →
      (∀ z, ‖z‖ ≤ t ^ (0.35 * δ) → diagonal z = diagonal 0 + K.mulVec z + R z) →
      (∀ z, ‖z‖ ≤ t ^ (0.35 * δ) → ‖R z‖ ≤ C * ‖z‖ ^ 2) →
      (∀ z w, ‖z‖ ≤ t ^ (0.35 * δ) → ‖w‖ ≤ t ^ (0.35 * δ) →
        ‖R z - R w‖ ≤ C * t ^ (0.35 * δ) * ‖z - w‖) →
      ‖diagonal 0 - r‖ ≤ t ^ (0.36 * δ) →
      ∃ ζ : ι → ℂ, ‖ζ‖ ≤ t ^ (0.35 * δ) ∧ diagonal ζ = r + ζ := by
  obtain ⟨t₀, ht₀, hsmallness⟩ := reset_numerical_smallness C δ hC hδ
  refine ⟨t₀, ht₀, ?_⟩
  intro ι _ _ diagonal r K P R t ht hlt hP hnorm htaylor hR hRlip hlag
  obtain ⟨hL, himage, hsmall⟩ := hsmallness t ht hlt
  apply reset_of_taylor diagonal r K P R (t ^ (0.35 * δ)) (C * Real.log (1 / t)) C
      (Real.rpow_nonneg ht.le _) hL (le_trans (by norm_num) hC) hP hnorm htaylor hR hRlip
  · calc
      C * Real.log (1 / t) * (‖diagonal 0 - r‖ + C * (t ^ (0.35 * δ)) ^ 2) ≤
          C * Real.log (1 / t) * (t ^ (0.36 * δ) + C * (t ^ (0.35 * δ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hlag le_rfl) hL
      _ ≤ t ^ (0.35 * δ) := himage
  · exact hsmall

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.reset_from_uniform_taylor
