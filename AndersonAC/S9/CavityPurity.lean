import AndersonAC.S9.Cavity
import AndersonAC.S9.Purity

/-! The conditional purity principle at §9:513–562, with the spectral
boundary criterion and own-site averaging supplied explicitly. The set S
depends only on the complementary configuration. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace AndersonAC.SolS9

theorem conditional_purity_from_cavity {Ξ Own : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Own]
    (ν : Measure Ξ) [SFinite ν] (κ : Measure Own) [SFinite κ]
    (μ : Ξ → Own → Measure ℝ) (M : Ξ → ℂ → ℂ) (V : Own → ℝ)
    (I : Set ℝ) (S : Ξ → Set ℝ) (B : AndersonAC.Blueprint.BoundaryInput)
    (hI : MeasurableSet I) (hS : ∀ ξ, MeasurableSet (S ξ))
    (hsub : ∀ ξ, S ξ ⊆ I)
    (hfinite : ∀ ξ s, IsFiniteMeasure (μ ξ s))
    (hcavity : ∀ ξ s z, 0 < z.im →
      borelTransform (μ ξ s) z = ((V s : ℂ) - M ξ z)⁻¹)
    (hpositive : ∀ ξ E, E ∈ S ξ → positiveBoundary (M ξ) E)
    (hfull : ∀ᵐ ξ ∂ν, volume (I \ S ξ) = 0)
    (hmeas : Measurable (fun p : Ξ × Own => μ p.1 p.2 (I \ S p.1)))
    (haveraging : ∀ ξ (A : Set ℝ), MeasurableSet A → volume A = 0 →
      ∫⁻ s, μ ξ s A ∂κ = 0) :
    ∀ᵐ p ∂ν.prod κ, (μ p.1 p.2).restrict I ≪ volume := by
  have hboundary : ∀ ξ s E, E ∈ S ξ → finiteBoundary (borelTransform (μ ξ s)) E := by
    intro ξ s E hE
    obtain ⟨w, hw, _⟩ := cavity_positive_boundary_all (M ξ)
      (fun t z => ((t : ℂ) - M ξ z)⁻¹) E (hpositive ξ E hE)
      (by intros; rfl) (V s)
    refine ⟨w, ?_⟩
    change Tendsto (fun η : ℝ => ((V s : ℂ) - M ξ ((E : ℂ) + η * Complex.I))⁻¹)
      (𝓝[>] 0) (𝓝 w) at hw
    change Tendsto (fun η : ℝ => borelTransform (μ ξ s) ((E : ℂ) + η * Complex.I))
      (𝓝[>] 0) (𝓝 w)
    apply hw.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (hcavity ξ s _ (by simpa using hη)).symm
  apply conditional_purity ν κ μ I S hI hS hsub hmeas
  · exact ae_of_all _ fun ξ s =>
      B.criterion (μ ξ s) (hfinite ξ s) (S ξ) (hS ξ) (hboundary ξ s)
  · filter_upwards [hfull] with ξ hξ
    exact haveraging ξ (I \ S ξ) (hI.diff (hS ξ)) hξ

end AndersonAC.SolS9
