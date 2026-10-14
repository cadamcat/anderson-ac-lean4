import AndersonAC.S9Inf.AllSitesDefinitions
import AndersonAC.S9Inf.InfiniteReadoutProof
import AndersonAC.S9Inf.BoundaryAdmissibility
import AndersonAC.S9Fin.FinalProof

/-! The all-sites statement derived from finite certificates. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson AndersonAC.S9
open scoped Topology

namespace AndersonAC.SolS9

open AndersonAC.SolS9Inf

theorem all_sites_positive_proof (d : ℕ) (hd : 3 ≤ d) (coupling : ℝ) (hcoupling : 0 < coupling)
    (a b : ℝ) (hab : a < b) (R : ResolvedAnderson d coupling) (B : BoundaryTheory)
    (hcertificate : halfProbabilityCertificates d coupling (Set.Ioo a b)) :
    ∀ᵐ E ∂volume.restrict (Set.Ioo a b),
      ∀ᵐ ω ∂disorderLaw d, allSitesPositive coupling E ω := by
  obtain ⟨bounds, η, hη, hcert⟩ := hcertificate
  let ε := min 1 (columnConstant bounds * coupling / 64)
  have hε : 0 < ε := lt_min (by norm_num)
    (div_pos (mul_pos (columnConstant_pos_proof bounds) hcoupling) (by norm_num))
  have hinfinite (E : ℝ) (hE : E ∈ Set.Ioo a b) :
      columnConstant bounds / 8 ≤ liminf (fun m => ∫ ω,
        truncatedReadout bounds ε (diagonalGreen coupling ω 0
          ((E : ℂ) + η m * Complex.I)).im ∂disorderLaw d) atTop := by
    apply infinite_root_readout_proof d hd coupling E ε bounds η hη hε
    filter_upwards [hcert E hE] with m hm
    exact finite_root_readout_proof d m coupling E (η m) ε hcoupling (hη.1 m)
      bounds hε le_rfl hm
  have hroot : ∀ᵐ E ∂volume.restrict (Set.Ioo a b),
      0 < disorderLaw d {ω | positiveScalarBoundary coupling E 0 ω} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (s := Set.Ioo a b) (boundaryGood_ae_energy coupling R.resolved B)]
      with E hE hgood
    exact boundary_positive_probability_proof d coupling E ε bounds η hη hε
      (hgood.mono (fun ω hω => hω.1 0)) (hinfinite E hE)
  exact all_sites_positive_ae_energy_of_root_probability (by omega) coupling hcoupling
    R.resolved B (Set.Ioo a b) hroot

end AndersonAC.SolS9
