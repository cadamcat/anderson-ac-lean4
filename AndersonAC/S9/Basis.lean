import AndersonAC.S9.Core

/-! Basis-measure absolute continuity implies purity of the spectral
restriction, as in §9:561–567. -/

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal

namespace AndersonAC.SolS9

theorem basis_ac_implies_purelyACOn {d : ℕ} {T : StateSpace d →L[ℂ] StateSpace d}
    (S : SpectralResolution T) (I : Set ℝ) (hI : MeasurableSet I)
    (hbasis : ∀ x : Site d, (S.vectorMeasure (siteVector x)).restrict I ≪ volume) :
    S.purelyACOn I := by
  intro v
  rw [← S.vectorMeasure_projection hI]
  apply (S.mem_acVectors_iff _).mpr
  intro B hB hnull
  have hx : ∀ x : Site d, S.projection B (S.projection I (siteVector x)) = 0 := by
    intro x
    have hAC : S.vectorMeasure (S.projection I (siteVector x)) ≪ volume := by
      rw [S.vectorMeasure_projection hI]
      exact hbasis x
    exact (S.mem_acVectors_iff _).mp hAC B hB hnull
  have hzero : S.projection B * S.projection I = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro x
    apply ContinuousLinearMap.ext
    intro c
    change S.projection B (S.projection I (lp.single 2 x c)) = 0
    have heq : lp.single 2 x c = c • siteVector x := by
      simp [siteVector, AndersonAC.Blueprint.delta, ← lp.single_smul, smul_eq_mul]
    rw [heq, map_smul, map_smul, hx, smul_zero]
  change (S.projection B * S.projection I) v = 0
  rw [hzero]
  rfl

end AndersonAC.SolS9
