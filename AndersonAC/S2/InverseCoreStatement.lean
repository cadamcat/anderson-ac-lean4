import AndersonAC.S2.Definitions

/-! Identifies the neutral inverse and its variational formula. -/
noncomputable section
open scoped ComplexOrder
open AndersonAC.S2
universe u

namespace AndersonAC.SolS2

def InverseCore : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ), ConnectedLaplacian D →
    ∀ (y : ι → ℂ), Neutral y →
      (D.mulVec ((laplacianPseudoInverse D).mulVec y) = y ∧
        Neutral ((laplacianPseudoInverse D).mulVec y)) ∧
      quadraticForm (laplacianPseudoInverse D) y =
        sSup (Set.range (fun f : ι → ℂ => 2 * (pairing y f).re - quadraticForm D f))

end AndersonAC.SolS2
