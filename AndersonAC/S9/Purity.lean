import AndersonAC.Blueprint.SpectralInputs

/-! Conditional singular-mass exclusion from §9.
The exceptional set is fixed by the complementary configuration, before
averaging the own-site value. This module does not import the statement
inventory and uses no unproved analytic result.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace AndersonAC.SolS9

/-- A zero average on each complementary configuration gives a zero mass
under the true product law. -/
theorem conditional_averaging_null {Ξ Own : Type*} [MeasurableSpace Ξ] [MeasurableSpace Own]
    (ν : Measure Ξ) [SFinite ν] (κ : Measure Own) [SFinite κ]
    (μ : Ξ → Own → Measure ℝ) (B : Ξ → Set ℝ)
    (hmeas : Measurable (fun p : Ξ × Own => μ p.1 p.2 (B p.1)))
    (hnull : ∀ᵐ ξ ∂ν, ∫⁻ s, μ ξ s (B ξ) ∂κ = 0) :
    ∀ᵐ p ∂ν.prod κ, μ p.1 p.2 (B p.1) = 0 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmeas measurable_const)).mpr
  filter_upwards [hnull] with ξ hξ
  exact (lintegral_eq_zero_iff
    (hmeas.comp (measurable_const.prodMk measurable_id))).mp hξ

/-- Absolute continuity on a complement-fixed set, together with a zero
averaged mass on its complement, gives purity on the whole interval. -/
theorem conditional_purity {Ξ Own : Type*} [MeasurableSpace Ξ] [MeasurableSpace Own]
    (ν : Measure Ξ) [SFinite ν] (κ : Measure Own) [SFinite κ]
    (μ : Ξ → Own → Measure ℝ) (I : Set ℝ) (S : Ξ → Set ℝ)
    (hI : MeasurableSet I) (hS : ∀ ξ, MeasurableSet (S ξ))
    (hsub : ∀ ξ, S ξ ⊆ I)
    (hmeas : Measurable (fun p : Ξ × Own => μ p.1 p.2 (I \ S p.1)))
    (hac : ∀ᵐ ξ ∂ν, ∀ s, (μ ξ s).restrict (S ξ) ≪ volume)
    (haverage : ∀ᵐ ξ ∂ν, ∫⁻ s, μ ξ s (I \ S ξ) ∂κ = 0) :
    ∀ᵐ p ∂ν.prod κ, (μ p.1 p.2).restrict I ≪ volume := by
  have hnull := conditional_averaging_null ν κ μ (fun ξ => I \ S ξ) hmeas haverage
  have hgood := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := κ)).ae hac
  filter_upwards [hnull, hgood] with p hp hAC
  have hzero : (μ p.1 p.2).restrict (I \ S p.1) = 0 :=
    Measure.restrict_eq_zero.mpr hp
  have heq := (μ p.1 p.2).restrict_inter_add_sdiff I (hS p.1)
  rw [Set.inter_eq_right.mpr (hsub p.1), hzero, add_zero] at heq
  rw [← heq]
  exact hAC p.2

end AndersonAC.SolS9
