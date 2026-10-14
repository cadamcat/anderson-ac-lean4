import AndersonAC.S9.SiteAveraging
import AndersonAC.S9.CavityPurity
import AndersonAC.S9Restore.RestoreSiteLaw
import AndersonAC.S9Inf.BoundaryAdmissibility

noncomputable section
open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

set_option maxHeartbeats 800000

namespace AndersonAC.SolS9
open AndersonAC.SolS9Inf

theorem site_purity_of_positive {d : ℕ} (coupling : ℝ) (hc : 0 < coupling)
    (R : AndersonAC.S9.ResolvedAnderson d coupling) (B : AndersonAC.Blueprint.BoundaryInput)
    (I : Set ℝ) (hI : MeasurableSet I) (x : Site d)
    (hpos : ∀ᵐ E ∂volume.restrict I, ∀ᵐ ω ∂disorderLaw d,
      positiveBoundary (AndersonAC.Blueprint.diagonalGreen coupling ω x) E) :
    ∀ᵐ ω ∂disorderLaw d, ((R.resolved ω).spectral.vectorMeasure (siteVector x)).restrict I ≪ volume := by
  let ν := complementLaw d x
  letI : IsProbabilityMeasure ν := by dsimp [ν, complementLaw]; infer_instance
  let μ := fun ξ s => (R.resolved (restoreSite x ξ s)).spectral.vectorMeasure (siteVector x)
  let S := fun ξ => {E : ℝ | E ∈ I ∧ positiveBoundary (siteCavity coupling x ξ) E}
  have hsj : MeasurableSet {p : ComplementConfiguration d x × ℝ | p.2 ∈ S p.1} :=
    (hI.preimage measurable_snd).inter (siteCavity_boundary_measurable coupling x)
  have hs (ξ) : MeasurableSet (S ξ) := hsj.preimage measurable_prodMk_left
  have hgmeas : MeasurableSet {p : Configuration d × ℝ |
      positiveBoundary (AndersonAC.Blueprint.diagonalGreen coupling p.1 x) p.2} :=
    (scalarGreen_boundary_joint_measurable_of_potential potentialStrongContinuity_proof
      coupling x x).2.1
  have hωE : ∀ᵐ ω ∂disorderLaw d, ∀ᵐ E ∂volume.restrict I,
      positiveBoundary (AndersonAC.Blueprint.diagonalGreen coupling ω x) E :=
    (Measure.ae_ae_comm hgmeas).mpr hpos
  have hpE : ∀ᵐ p ∂ν.prod uniformSite, ∀ᵐ E ∂volume.restrict I,
      positiveBoundary (AndersonAC.Blueprint.diagonalGreen coupling (restoreSite x p.1 p.2) x) E :=
    (ae_restoreSite_iff d x (RestoreSiteLawInput_proof d x) _).mpr hωE
  have hξsE := Measure.ae_ae_of_ae_prod hpE
  have hfull : ∀ᵐ ξ ∂ν, volume (I \ S ξ) = 0 := by
    filter_upwards [hξsE] with ξ hξ
    have hmmap : Measurable (fun p : SingleSite × ℝ => (restoreSite x ξ p.1, p.2)) :=
      (((measurable_restoreSite x).comp
        ((measurable_const : Measurable (fun _ : SingleSite × ℝ => ξ)).prodMk
          measurable_fst)).prodMk measurable_snd)
    have hownmeas : MeasurableSet {p : SingleSite × ℝ |
        positiveBoundary (AndersonAC.Blueprint.diagonalGreen coupling (restoreSite x ξ p.1) x) p.2} :=
      hgmeas.preimage (f := fun p : SingleSite × ℝ => (restoreSite x ξ p.1, p.2)) hmmap
    have hEown : ∀ᵐ E ∂volume.restrict I, ∀ᵐ s ∂uniformSite,
        positiveBoundary (AndersonAC.Blueprint.diagonalGreen coupling (restoreSite x ξ s) x) E :=
      (Measure.ae_ae_comm hownmeas).mp hξ
    have hfinite := ae_restrict_of_ae (s := I)
      (siteCavity_finite_ae coupling x ξ (R.resolved (restoreSite x ξ zeroSite)) B)
    have hgood : ∀ᵐ E ∂volume.restrict I, E ∈ S ξ := by
      filter_upwards [hEown, hfinite, ae_restrict_mem hI] with E hE hF hEI
      refine ⟨hEI, ?_⟩
      exact cavity_im_pos_of_ae_positive uniformSite (fun s => coupling * (s : ℝ))
        (uniformOwnSite_no_atoms coupling hc.ne') (siteCavity coupling x ξ)
        (fun s => AndersonAC.Blueprint.diagonalGreen coupling (restoreSite x ξ s) x) E
        (siteCavity_im_pos coupling x ξ) hF (siteCavity_identity coupling x ξ) hE
    have hbad : (volume.restrict I) (S ξ)ᶜ = 0 := by
      exact ae_iff.mp hgood
    rw [Measure.restrict_apply (hs ξ).compl] at hbad
    simpa only [Set.diff_eq, Set.inter_comm] using hbad
  have hm : ∀ A : Set ℝ, MeasurableSet A →
      Measurable (fun p : ComplementConfiguration d x × SingleSite => μ p.1 p.2 A) := by
    intro A hA
    exact (R.measure_measurable x A hA).comp (measurable_restoreSite x)
  have hp : ∀ ξ s, IsProbabilityMeasure (μ ξ s) := by
    intro ξ s
    constructor
    change (R.resolved (restoreSite x ξ s)).spectral.vectorMeasure (siteVector x) Set.univ = 1
    rw [(R.resolved _).spectral.vectorMeasure_univ, siteVector_norm]
    norm_num
  have hac : ∀ᵐ p ∂ν.prod uniformSite, (μ p.1 p.2).restrict I ≪ volume := by
    apply conditional_purity_from_cavity ν uniformSite μ (siteCavity coupling x)
      (fun s => coupling * (s : ℝ)) I S B hI hs (fun ξ E hE => hE.1)
      (fun ξ s => (R.resolved _).spectral.finite_vectorMeasure _) _
      (fun ξ E hE => hE.2) hfull
      (measurable_varying_mass μ hp hm I hI S hsj)
      (fun ξ A hA hn => site_averaging_null coupling hc x ξ R A hA hn)
    intro ξ s z hz
    exact ((R.resolved _).resolvent_eq _ _ hz).symm.trans
      (siteCavity_identity coupling x ξ s z hz)
  exact (ae_restoreSite_iff d x (RestoreSiteLawInput_proof d x) _).mp hac

end AndersonAC.SolS9
