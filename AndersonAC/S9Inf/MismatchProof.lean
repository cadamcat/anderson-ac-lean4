import AndersonAC.S9Inf.Mismatch
import AndersonAC.S9Inf.PotentialContinuous

/-! Fixed-energy Anderson positivity mismatch theorem. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9

open AndersonAC.SolS9Inf

theorem positivity_mismatch_null_proof
    (d : ℕ) (coupling E : ℝ) (hcoupling : 0 < coupling)
    (x y : Site d) (hxy : x ≠ y)
    (hadmissible : ∀ᵐ ω ∂disorderLaw d,
      (∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g) ∧
      (∃ k : ℂ, hasBoundary (scalarGreen coupling ω y y) E k) ∧
      ∃ a : ℂ, hasBoundary (scalarGreen coupling ω x y) E a ∧ a ≠ 0) :
    disorderLaw d {ω | positiveScalarBoundary coupling E x ω ∧
      zeroScalarBoundary coupling E y ω} = 0 :=
  positivity_mismatch_null_of_potential potentialStrongContinuity_proof
    d coupling E hcoupling x y hxy hadmissible

end AndersonAC.SolS9
