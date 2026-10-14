import AndersonAC.S9Inf.Nonvanishing

/-! Polarization transfers scalar Borel-transform boundary uniqueness to
the actual Anderson off-diagonal Green kernel. -/

noncomputable section

open OAI.Anderson MeasureTheory Filter
open scoped Topology

namespace AndersonAC.SolS9Inf

theorem polarization_difference {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (R : AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω))
    (z : ℂ) (hz : 0 < z.im) :
    AndersonAC.Blueprint.borelTransform (R.spectral.vectorMeasure (basis x + basis y)) z -
      AndersonAC.Blueprint.borelTransform (R.spectral.vectorMeasure (basis x - basis y)) z =
        4 * scalarGreen coupling ω x y z := by
  have hplus := R.resolvent_eq (basis x + basis y) z hz
  have hminus := R.resolvent_eq (basis x - basis y) z hz
  change inner ℂ (basis x + basis y)
      (green (hamiltonian coupling ω) z (basis x + basis y)) = _ at hplus
  change inner ℂ (basis x - basis y)
      (green (hamiltonian coupling ω) z (basis x - basis y)) = _ at hminus
  rw [← hplus, ← hminus]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  have hsym := scalarGreen_symmetric coupling ω z hz.ne' x y
  dsimp [scalarGreen] at hsym ⊢
  rw [← hsym]
  ring

end AndersonAC.SolS9Inf

namespace AndersonAC.SolS9

open AndersonAC.SolS9Inf

theorem offDiagonal_boundary_nonzero_proof {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (hxy : x ≠ y)
    (R : AndersonAC.Blueprint.ResolvedOperator (hamiltonian coupling ω))
    (B : AndersonAC.Blueprint.BoundaryInput) :
    ∀ᵐ E ∂volume, ∃ w : ℂ, hasBoundary (scalarGreen coupling ω x y) E w ∧ w ≠ 0 := by
  let μ := R.spectral.vectorMeasure (basis x + basis y)
  let ν := R.spectral.vectorMeasure (basis x - basis y)
  have hμ : IsFiniteMeasure μ := R.spectral.finite_vectorMeasure _
  have hν : IsFiniteMeasure ν := R.spectral.finite_vectorMeasure _
  have hnonzero : ∃ z : ℂ, 0 < z.im ∧
      AndersonAC.Blueprint.borelTransform μ z - AndersonAC.Blueprint.borelTransform ν z ≠ 0 := by
    obtain ⟨z, hz, hG⟩ := offDiagonal_not_identically_zero_proof coupling ω x y hxy
    refine ⟨z, hz, ?_⟩
    rw [polarization_difference coupling ω x y R z hz]
    exact mul_ne_zero (by norm_num) hG
  filter_upwards [B.difference_nonzero μ ν hμ hν hnonzero] with E hE
  obtain ⟨w, hw, hwne⟩ := hE
  refine ⟨w / 4, ?_, div_ne_zero hwne (by norm_num)⟩
  have hlim := hw.div_const (4 : ℂ)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [polarization_difference coupling ω x y R _ (by simpa using (show 0 < η from hη))]
  simp

end AndersonAC.SolS9
