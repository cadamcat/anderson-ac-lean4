import AndersonAC.S9Inf.BoundaryProbabilityCore
import AndersonAC.S9Inf.ReadoutDefinitions

/-! Positive boundary probability statement. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson AndersonAC.S9
open scoped Topology

namespace AndersonAC.SolS9

open AndersonAC.SolS9Inf

theorem boundary_positive_probability_proof (d : ℕ) (coupling E ε : ℝ)
    (b : CertificateBounds) (η : ℕ → ℝ) (hη : comparableHeights η) (hε : 0 < ε)
    (hfinite : ∀ᵐ ω ∂disorderLaw d, finiteBoundary (diagonalGreen coupling ω 0) E)
    (hlower : columnConstant b / 8 ≤ liminf (fun m => ∫ ω,
      truncatedReadout b ε (diagonalGreen coupling ω 0
        ((E : ℂ) + η m * Complex.I)).im ∂disorderLaw d) atTop) :
    0 < disorderLaw d {ω | positiveBoundary (diagonalGreen coupling ω 0) E} := by
  have hc : 0 < columnConstant b := by
    unfold columnConstant comparisonConstant
    have hcompare : 0 < 1 + (b.B + 1) / b.pMin :=
      add_pos zero_lt_one (div_pos (by linarith [b.B_nonneg]) b.pMin_pos)
    exact div_pos b.qMin_pos
      (mul_pos (lt_of_lt_of_le b.pMin_pos b.pMin_le_pMax) (sq_pos_of_pos hcompare))
  apply positive_boundary_probability_of_liminf (disorderLaw d)
    (fun ω η => diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)) η
    (comparable_heights_tendsto η hη) _ _ hfinite
    (columnConstant b) (2 * cutMultiplier ε) (columnConstant b / 8)
    hc.le (by unfold cutMultiplier; positivity) (by positivity) hlower
  · intro n
    exact measurable_scalarGreen_of_potential potentialStrongContinuity_proof coupling 0 0 _
      (by simpa using hη.1 n)
  · intro n ω
    exact green_quadratic_im_nonneg _ (hamiltonian_isSelfAdjoint coupling ω) _
      (by simpa using hη.1 n) (basis 0)

end AndersonAC.SolS9
