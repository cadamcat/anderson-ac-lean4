import AndersonAC.S9Inf.InfiniteReadout
import AndersonAC.S9Inf.ComparisonProof

noncomputable section

open MeasureTheory Filter OAI.Anderson AndersonAC.S9
open scoped Topology

namespace AndersonAC.SolS9

theorem infinite_root_readout_proof (d : ℕ) (hd : 3 ≤ d) (coupling E ε : ℝ)
    (b : CertificateBounds) (η : ℕ → ℝ) (hη : comparableHeights η)
    (hε : 0 < ε)
    (hfinite : ∀ᶠ m in atTop, columnConstant b / 8 ≤
      ∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E (η m) 0)
        ∂torusLaw d m) :
    columnConstant b / 8 ≤ liminf (fun m => ∫ ω,
      truncatedReadout b ε (diagonalGreen coupling ω 0
        ((E : ℂ) + η m * Complex.I)).im ∂disorderLaw d) atTop :=
  AndersonAC.SolS9Inf.infinite_root_readout_of_comparison
    finite_infinite_resolvent_comparison_proof d hd coupling E ε b η hη hε hfinite

end AndersonAC.SolS9
