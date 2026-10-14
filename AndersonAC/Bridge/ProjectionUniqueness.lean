import AndersonAC.Bridge.Characterization

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal lp Topology
open AndersonAC.Blueprint AndersonChallenge

namespace AndersonAC.LunaBridge

variable {d : ℕ} {T : Operator d}

/-- Norms of spectral projections are determined by the vector measures. -/
theorem projection_norm_eq_of_vectorMeasure_eq (S₁ S₂ : SpectralResolution T)
    {B : Set ℝ} (hB : MeasurableSet B) (v : StateSpace d) :
    ‖S₁.projection B v‖ = ‖S₂.projection B v‖ := by
  have hmeas : S₁.vectorMeasure v = S₂.vectorMeasure v :=
    vectorMeasure_unique S₁ S₂ v
  have h1 := S₁.vectorMeasure_apply v B hB
  have h2 := S₂.vectorMeasure v B
  -- Actually use hmeas to relate
  have hBeq : S₁.vectorMeasure v B = S₂.vectorMeasure v B := by rw [hmeas]
  rw [h1] at hBeq
  have h2' : S₂.vectorMeasure v B = ENNReal.ofReal (‖S₂.projection B v‖ ^ 2) :=
    S₂.vectorMeasure_apply v B hB
  rw [h2'] at hBeq
  have hsq : ‖S₁.projection B v‖ ^ 2 = ‖S₂.projection B v‖ ^ 2 := by
    have := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp hBeq
    exact this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Spectral projections on measurable sets are unique. -/
theorem projection_unique (S₁ S₂ : SpectralResolution T) {B : Set ℝ}
    (hB : MeasurableSet B) : S₁.projection B = S₂.projection B := by
  classical
  -- Self-adjointness as symmetry of the underlying linear maps
  have hsym1 : ((S₁.projection B : StateSpace d →L[ℂ] StateSpace d) :
      StateSpace d →ₗ[ℂ] StateSpace d).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (S₁.projection_selfAdjoint B hB)
  have hsym2 : ((S₂.projection B : StateSpace d →L[ℂ] StateSpace d) :
      StateSpace d →ₗ[ℂ] StateSpace d).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (S₂.projection_selfAdjoint B hB)
  -- Idempotence pointwise
  have hidem1 : ∀ v : StateSpace d, S₁.projection B (S₁.projection B v)
      = S₁.projection B v := by
    intro v
    have h := S₁.projection_idempotent hB
    have hv : (S₁.projection B * S₁.projection B) v = S₁.projection B v := by
      rw [h]
    simpa using hv
  have hidem2 : ∀ v : StateSpace d, S₂.projection B (S₂.projection B v)
      = S₂.projection B v := by
    intro v
    have h := S₂.projection_idempotent hB
    have hv : (S₂.projection B * S₂.projection B) v = S₂.projection B v := by
      rw [h]
    simpa using hv
  -- Diagonal identity: ⟪P v, v⟫ = (‖P v‖ : ℂ)^2
  have hdiag1 : ∀ v : StateSpace d,
      inner ℂ (S₁.projection B v) v = ((‖S₁.projection B v‖ : ℝ) : ℂ) ^ 2 := by
    intro v
    have hsymm : inner ℂ (S₁.projection B v) v
        = inner ℂ v (S₁.projection B v) := hsym1 v v
    have hself : inner ℂ (S₁.projection B v) (S₁.projection B v)
        = inner ℂ v (S₁.projection B v) := by
      have h0 := hsym1 v (S₁.projection B v)
      -- h0 : ⟪↑P v, P v⟫ = ⟪v, ↑P (P v)⟫; both coercions agree with CLM application
      simpa [hidem1 v] using h0
    rw [hsymm]
    rw [← hself]
    exact inner_self_eq_norm_sq_to_K _
  have hdiag2 : ∀ v : StateSpace d,
      inner ℂ (S₂.projection B v) v = ((‖S₂.projection B v‖ : ℝ) : ℂ) ^ 2 := by
    intro v
    have hsymm : inner ℂ (S₂.projection B v) v
        = inner ℂ v (S₂.projection B v) := hsym2 v v
    have hself : inner ℂ (S₂.projection B v) (S₂.projection B v)
        = inner ℂ v (S₂.projection B v) := by
      have h0 := hsym2 v (S₂.projection B v)
      simpa [hidem2 v] using h0
    rw [hsymm]
    rw [← hself]
    exact inner_self_eq_norm_sq_to_K _
  -- Difference has vanishing diagonal
  have hnorm : ∀ v : StateSpace d,
      ‖S₁.projection B v‖ = ‖S₂.projection B v‖ :=
    projection_norm_eq_of_vectorMeasure_eq S₁ S₂ hB
  have hDdiag : ∀ v : StateSpace d,
      inner ℂ ((S₁.projection B - S₂.projection B : Operator d) v) v = 0 := by
    intro v
    have hsub : (S₁.projection B - S₂.projection B : Operator d) v
        = S₁.projection B v - S₂.projection B v := by
      simp
    rw [hsub, inner_sub_left, hdiag1 v, hdiag2 v, hnorm v, sub_self]
  -- Vanishing diagonal for a symmetric operator forces it to be zero
  have hDsymm : (((S₁.projection B - S₂.projection B : Operator d)) :
      StateSpace d →ₗ[ℂ] StateSpace d).IsSymmetric := by
    have h1 : (((S₁.projection B : Operator d)) :
        StateSpace d →ₗ[ℂ] StateSpace d).IsSymmetric := hsym1
    have h2 : (((S₂.projection B : Operator d)) :
        StateSpace d →ₗ[ℂ] StateSpace d).IsSymmetric := hsym2
    have hsub : (((S₁.projection B - S₂.projection B : Operator d)) :
        StateSpace d →ₗ[ℂ] StateSpace d)
        = ((S₁.projection B : Operator d) : StateSpace d →ₗ[ℂ] StateSpace d)
          - ((S₂.projection B : Operator d) : StateSpace d →ₗ[ℂ] StateSpace d) := by
      ext v
      simp
    rw [hsub]
    exact h1.sub h2
  have hDzero : (((S₁.projection B - S₂.projection B : Operator d)) :
      StateSpace d →ₗ[ℂ] StateSpace d) = 0 := by
    have hiff := LinearMap.IsSymmetric.inner_map_self_eq_zero hDsymm
    -- hiff : (∀ x, ⟪D x, x⟫ = 0) ↔ D = 0
    apply hiff.mp
    intro x
    -- Linear-map application agrees with CLM application
    exact hDdiag x
  -- From linear-map vanishing to CLM equality
  have hpointwise : ∀ v : StateSpace d,
      S₁.projection B v = S₂.projection B v := by
    intro v
    have hlin : (((S₁.projection B - S₂.projection B : Operator d)) :
        StateSpace d →ₗ[ℂ] StateSpace d) v = 0 := by
      rw [hDzero]
      simp
    simp at hlin
    exact sub_eq_zero.mp hlin
  exact ContinuousLinearMap.ext fun v => hpointwise v

end AndersonAC.LunaBridge
