import AndersonAC.S9Fin.Core

noncomputable section
open MeasureTheory AndersonAC.S9

namespace AndersonAC.SolS9

universe u v

/-- The true cutoff rank is measurable before conditioning or selecting any
certificate. The Hermitian proof supplied to the eigenbasis is immaterial. -/
def WindowRankMeasurableStatement : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (Ξ : Type v) [MeasurableSpace Ξ] (H : Ξ → Matrix n n ℂ)
    (hH : ∀ ξ, (H ξ).IsHermitian), Measurable H →
    ∀ E δ : ℝ, Measurable (fun ξ => (windowRank (H ξ) (hH ξ) E δ : ℝ))

end AndersonAC.SolS9
