import AndersonAC.S9Inf.HelperStatements

/-! law-construction helper for the finite/infinite comparison. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9Inf

def RootCouplingLawStatement : Prop :=
  ∀ d m : ℕ, ∃ μ : Measure (TorusConfiguration d m × Configuration d),
    IsProbabilityMeasure μ ∧ μ.map Prod.fst = torusLaw d m ∧
    μ.map Prod.snd = disorderLaw d ∧
    ∀ᵐ p ∂μ, ∀ x : Site d,
      (∀ j : Fin d, |x j| ≤ ((sideLength m / 4 : ℕ) : ℤ)) →
        (p.1 (fun j => (x j : ZMod (sideLength m))) : ℝ) = potential p.2 x

end AndersonAC.SolS9Inf
