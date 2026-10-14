import AndersonAC.S9Fin.PoissonDomination
import AndersonAC.S9FiniteAvg.Finite
import AndersonAC.S9Fin.FiniteComparisonProof
import AndersonAC.S9Fin.RootReadout

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9
open scoped ENNReal

namespace AndersonAC.SolS9

theorem finite_wegner_proof (d m : ℕ) (coupling E δ : ℝ) (hcoupling : 0 < coupling) (hδ : 0 ≤ δ)
    (hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian) :
    ∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E δ : ℝ) ∂torusLaw d m ≤
      (Fintype.card (Torus d m) : ℝ) * δ / coupling := by
  exact finite_wegner_of_inputs windowRankMeasurable_proof finiteScalarAveraging_proof
    finitePoissonDomination_proof d m coupling E δ hcoupling hδ hH

theorem finite_root_readout_proof (d m : ℕ) (coupling E η ε : ℝ) (hcoupling : 0 < coupling) (hη : 0 < η)
    (b : CertificateBounds) (hε : 0 < ε)
    (hεsmall : ε ≤ min 1 (columnConstant b * coupling / 64))
    (hcert : (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (trueCertificateEvent d m coupling E η b)) :
    columnConstant b / 8 ≤ ∫ ω, truncatedReadout b ε
      (scalarQ (periodicHamiltonian coupling ω) E η 0) ∂torusLaw d m := by
  let hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian :=
    periodicHamiltonian_isHermitian_proof d m coupling
  have hεI : ε ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨hε, hεsmall.trans (min_le_left _ _)⟩
  exact finite_root_readout_of_estimates d m coupling E η ε hcoupling hη b hε hεsmall hcert hH
    (finite_truncated_average_proof d m coupling E η ε hcoupling hη hεI b hH)
    (finite_wegner_proof d m coupling E (ε * η) hcoupling (mul_pos hε hη).le hH)

end AndersonAC.SolS9
