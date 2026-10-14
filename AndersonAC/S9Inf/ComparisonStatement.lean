import AndersonAC.S9Inf.HelperStatements

/-! Raw, definitionally exact form of the frozen volume comparison. -/

noncomputable section

open OAI.Anderson Filter

namespace AndersonAC.SolS9Inf

def FiniteInfiniteComparisonStatement : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ coupling : ℝ,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ m in atTop,
      ∀ (E η : ℝ), η ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (ωm : TorusConfiguration d m) (ω : Configuration d),
        (∀ x : Site d, (∀ j : Fin d, |x j| ≤ (sideLength m / 4 : ℕ)) →
          (ωm (fun j => (x j : ZMod (sideLength m))) : ℝ) = potential ω x) →
        ‖(periodicHamiltonian coupling ωm - ((E : ℂ) + η * Complex.I) • 1)⁻¹ 0 0 -
          AndersonAC.Blueprint.diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)‖ ≤
          C * (sideLength m : ℝ) ^ (d - 1) * η⁻¹ ^ 2 *
            Real.exp (-c * η * sideLength m)

end AndersonAC.SolS9Inf
