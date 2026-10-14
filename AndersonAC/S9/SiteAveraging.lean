import AndersonAC.S9.CavityMeasurable
import AndersonAC.S9.MeasureAveraging
import AndersonAC.S9.IntervalAveraging
import AndersonAC.S9.SharpPoisson
import AndersonAC.S9Inf.AllSitesDefinitions
import AndersonAC.Transport.Law

noncomputable section
open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

namespace AndersonAC.SolS9

theorem site_averaging_null {d : ℕ} (coupling : ℝ) (hc : 0 < coupling)
    (x : Site d) (ξ : ComplementConfiguration d x)
    (R : AndersonAC.S9.ResolvedAnderson d coupling)
    (A : Set ℝ) (hA : MeasurableSet A) (hnull : volume A = 0) :
    ∫⁻ s, (R.resolved (restoreSite x ξ s)).spectral.vectorMeasure (siteVector x) A
      ∂uniformSite = 0 := by
  let μ := fun s => (R.resolved (restoreSite x ξ s)).spectral.vectorMeasure (siteVector x)
  have hm (B : Set ℝ) (hB : MeasurableSet B) : Measurable (fun s => μ s B) :=
    (R.measure_measurable x B hB).comp
      ((measurable_restoreSite x).comp (measurable_const.prodMk measurable_id))
  have hp (s : SingleSite) : IsProbabilityMeasure (μ s) := by
    constructor
    change (R.resolved (restoreSite x ξ s)).spectral.vectorMeasure (siteVector x) Set.univ = 1
    rw [(R.resolved _).spectral.vectorMeasure_univ, siteVector_norm]
    norm_num
  have hbound := averaging_from_transform_bound boundedPoisson_from_finite
    uniformSite μ hm hp (2 * coupling)⁻¹ (by positivity)
  have hb : ∀ E η : ℝ, 0 < η →
      (∫ s, (borelTransform (μ s) ((E : ℂ) + η * Complex.I)).im ∂uniformSite) ≤
        Real.pi * (2 * coupling)⁻¹ := by
    intro E η hη
    let z : ℂ := (E : ℂ) + η * Complex.I
    have hz : 0 < z.im := by simpa [z] using hη
    let w := siteCavity coupling x ξ z
    have hw : 0 < w.im := siteCavity_im_pos coupling x ξ z hz
    have heq : (fun s : SingleSite => (borelTransform (μ s) z).im) =
        fun s : SingleSite => cauchyKernel w.re w.im (coupling * (s : ℝ)) := by
      funext s
      rw [show borelTransform (μ s) z =
          AndersonAC.Blueprint.diagonalGreen coupling (restoreSite x ξ s) x z from
        ((R.resolved _).resolvent_eq _ _ hz).symm,
        siteCavity_identity coupling x ξ s z hz]
      exact imaginary_cavity_kernel w _
    rw [heq]
    have hmap := AndersonAC.LunaTransport.siteAffine_map (a := -coupling) (b := coupling)
      (by linarith)
    have haff : AndersonAC.LunaTransport.siteAffine (-coupling) coupling =
        fun s : SingleSite => coupling * (s : ℝ) := by
      funext s
      simp [AndersonAC.LunaTransport.siteAffine, AndersonAC.Blueprint.intervalCenter,
        AndersonAC.Blueprint.intervalCoupling]
    rw [haff] at hmap
    have hmeas : Measurable (fun s : SingleSite => coupling * (s : ℝ)) := by fun_prop
    have hk : AEStronglyMeasurable (cauchyKernel w.re w.im)
        (uniformSite.map (fun s : SingleSite => coupling * (s : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      unfold cauchyKernel
      apply Continuous.div
      · exact continuous_const
      · fun_prop
      · intro s
        exact ne_of_gt (by positivity)
    rw [← integral_map hmeas.aemeasurable hk, hmap]
    simpa [div_eq_mul_inv, sub_neg_eq_add, two_mul] using
      uniformInterval_cauchy_bound (-coupling) coupling w.re w.im (by linarith) hw
  have h := hbound hb A hA
  rw [hnull, mul_zero] at h
  exact le_zero_iff.mp h

end AndersonAC.SolS9
