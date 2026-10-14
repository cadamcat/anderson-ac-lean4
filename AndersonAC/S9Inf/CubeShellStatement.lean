import AndersonAC.S9Inf.HelperStatements

/-! The finite boundary layer needed by the direct column comparison. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

def LatticeCubeShellStatement : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ R : ℕ,
    ∃ S : Finset (Site d),
      (∀ x : Site d, x ∈ S ↔
        (∀ j : Fin d, |x j| ≤ (R : ℤ) + 1) ∧
        ∃ j : Fin d, (R : ℤ) ≤ |x j|) ∧
      S.card ≤ 4 * d * (2 * R + 3) ^ (d - 1) ∧
      ∀ x ∈ S, R ≤ latticeDistance 0 x

end AndersonAC.SolS9Inf
