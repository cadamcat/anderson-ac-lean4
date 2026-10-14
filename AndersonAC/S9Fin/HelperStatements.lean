import AndersonAC.S9Fin.Core

noncomputable section
open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9

/-- Independent diffuse diagonal coordinates make every fixed finite matrix invertible
almost surely. A coordinate induction/Fubini proof suffices; no adaptive selection. -/
def DiagonalInvertibilityStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (K : Matrix n n ℂ)
    (coupling : ℝ), 0 < coupling →
    ∀ᵐ ω : n → SingleSite ∂Measure.pi (fun _ : n => uniformSite),
      IsUnit (K + (coupling : ℂ) • Matrix.diagonal (fun i => ((ω i : ℝ) : ℂ)))

end AndersonAC.SolS9
