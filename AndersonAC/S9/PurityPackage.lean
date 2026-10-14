import AndersonAC.S9.SitePurity
import AndersonAC.S9.SpectrumReadout
import AndersonAC.S9.ReadoutPackage
import AndersonAC.S9.Basis

noncomputable section
open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

namespace AndersonAC.Blueprint.Packages

open AndersonAC.SolS9 AndersonAC.SolS9Inf

theorem purity : PurityInput := by
  intro spectral B averaging d hd coupling hc I hI hn hb hpositive
  let R := resolvedAnderson spectral d coupling
  have hsite : ∀ᵐ ω ∂disorderLaw d, ∀ x : Site d,
      ((R.resolved ω).spectral.vectorMeasure (siteVector x)).restrict I ≪ volume := by
    apply ae_all_iff.mpr
    intro x
    exact site_purity_of_positive coupling hc R B I hI.measurableSet x
      (hpositive.mono fun E hE => hE.mono fun ω hω => hω x)
  have hroot : ∀ᵐ ω ∂disorderLaw d, ∀ᵐ E ∂volume.restrict I,
      positiveBoundary (diagonalGreen coupling ω 0) E := by
    apply (Measure.ae_ae_comm
      (scalarGreen_boundary_joint_measurable_of_potential potentialStrongContinuity_proof
        coupling 0 0).2.1).mpr
    exact hpositive.mono fun E hE => hE.mono fun ω hω => hω 0
  filter_upwards [hsite, hroot] with ω hω hωroot
  apply (acRegion_iff _ hI.measurableSet).mpr
  refine ⟨?_, (R.resolved ω).spectral,
    basis_ac_implies_purelyACOn _ I hI.measurableSet hω, ?_⟩
  · exact positive_boundary_spectrum _ (hamiltonian_isSelfAdjoint coupling ω)
      (siteVector 0) I hI hωroot
  · let μ := (R.resolved ω).spectral.vectorMeasure (siteVector 0)
    letI : IsFiniteMeasure μ := (R.resolved ω).spectral.finite_vectorMeasure _
    have hpμ : ∀ᵐ E ∂volume.restrict I, positiveBoundary (borelTransform μ) E := by
      filter_upwards [hωroot] with E hE
      obtain ⟨w, hw, hwpos⟩ := hE
      refine ⟨w, hw.congr' ?_, hwpos⟩
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact (R.resolved ω).resolvent_eq _ _ (by simpa using hη)
    have hmass := positive_boundary_mass μ I hI hn hpμ
    intro hz
    have hzero : μ I = 0 := by
      rw [(R.resolved ω).spectral.vectorMeasure_apply _ I hI.measurableSet, hz]
      simp
    rw [hzero] at hmass
    exact lt_irrefl _ hmass


end AndersonAC.Blueprint.Packages
