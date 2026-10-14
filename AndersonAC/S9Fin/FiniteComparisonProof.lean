import AndersonAC.S9Fin.Comparison
import AndersonAC.S9Fin.CutColumn
import AndersonAC.S9Fin.Expectation
import AndersonAC.S9Rank.WindowRankMeasurable

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem finite_cut_comparison_proof [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (b : CertificateBounds) (hprincipal : allPrincipalInvertible H E)
    (hcert : matrixCertificate H E η b) :
    columnConstant b / 2 - 8 * (windowRank H hH E (ε * η) : ℝ) /
      (η * Fintype.card n) ≤
      (∑ i, truncatedReadout b ε (scalarQ H E η i)) / Fintype.card n := by
  exact finite_cut_comparison_of_cut_columns H hH E η ε hη hε b hprincipal hcert
    (fun A i => cut_column_proof H hH E η ε hη hε.1 hprincipal A i)

theorem finite_truncated_average_proof (d m : ℕ) (coupling E η ε : ℝ)
    (hcoupling : 0 < coupling) (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (b : CertificateBounds)
    (hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian) :
    columnConstant b / 2 * (torusLaw d m (trueCertificateEvent d m coupling E η b)).toReal -
      8 * (∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E (ε * η) : ℝ)
        ∂torusLaw d m) / (η * Fintype.card (Torus d m)) ≤
      ∫ ω, (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
        Fintype.card (Torus d m) ∂torusLaw d m := by
  exact finite_truncated_average_of_inputs windowRankMeasurable_proof
    d m coupling E η ε hcoupling hη hε b hH
    (fun ω hprincipal hcert => finite_cut_comparison_proof
      (periodicHamiltonian coupling ω) (hH ω) E η ε hη hε b hprincipal hcert)

end AndersonAC.SolS9
