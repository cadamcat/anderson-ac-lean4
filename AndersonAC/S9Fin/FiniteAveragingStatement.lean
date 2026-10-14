import AndersonAC.S9Fin.Core

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9

namespace AndersonAC.SolS9

universe u

/-- Finite-height own-site averaging under the true uniform product law.
The background Hermitian matrix is deterministic and may have a diagonal. -/
def FiniteScalarAveragingStatement : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (hK : K.IsHermitian) (coupling E η : ℝ),
    0 < coupling → 0 < η → ∀ i : n,
      (∫ ω : n → SingleSite,
        scalarQ (K + (coupling : ℂ) • Matrix.diagonal (fun j => ((ω j : ℝ) : ℂ))) E η i
        ∂Measure.pi (fun _ : n => uniformSite)) ≤ Real.pi / (2 * coupling)

end AndersonAC.SolS9
