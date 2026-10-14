import AndersonAC.S9.SiteCavity
import AndersonAC.S9.BoundaryMeasurable
import AndersonAC.S9Inf.AndersonGreen
import AndersonAC.S9Inf.PotentialContinuous
import Mathlib.Probability.Kernel.MeasurableLIntegral

noncomputable section
open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

namespace AndersonAC.SolS9
open AndersonAC.SolS9Inf

theorem measurable_restoreSite {d : ℕ} (x : Site d) :
    Measurable (fun p : ComplementConfiguration d x × SingleSite => restoreSite x p.1 p.2) :=
  (restoreSiteEquiv d x).measurable

theorem siteCavity_boundary_measurable {d : ℕ} (coupling : ℝ) (x : Site d) :
    MeasurableSet {p : ComplementConfiguration d x × ℝ |
      positiveBoundary (siteCavity coupling x p.1) p.2} := by
  apply (BoundarySetMeasurableInput_proof (ComplementConfiguration d x)
    (fun ξ E η => siteCavity coupling x ξ ((E : ℂ) + η * Complex.I)) ?_ ?_).2
  · intro η hη
    have hg := (continuous_height_joint_scalarGreen_of_potential
      potentialStrongContinuity_proof coupling η hη x x).measurable
    have hm : Measurable (fun p : ComplementConfiguration d x × ℝ =>
        (restoreSite x p.1 zeroSite, p.2)) :=
      ((measurable_restoreSite x).comp (measurable_fst.prodMk measurable_const)).prodMk measurable_snd
    exact (hg.comp hm).inv.neg
  · intro ξ E
    have hg := continuousOn_height_scalarGreen_of_potential
      potentialStrongContinuity_proof coupling E (restoreSite x ξ zeroSite) x x
    apply (hg.inv₀ ?_).neg
    intro η hη
    apply ne_of_apply_ne Complex.im
    exact ne_of_gt (resolvent_im_pos _ (hamiltonian_isSelfAdjoint _ _) _ (by simpa using hη) _
      (basis_ne_zero x))

theorem measurable_varying_mass {Ξ Own : Type*} [MeasurableSpace Ξ] [MeasurableSpace Own]
    (μ : Ξ → Own → Measure ℝ) (hprob : ∀ ξ s, IsProbabilityMeasure (μ ξ s))
    (hm : ∀ A : Set ℝ, MeasurableSet A → Measurable (fun p : Ξ × Own => μ p.1 p.2 A))
    (I : Set ℝ) (hI : MeasurableSet I) (S : Ξ → Set ℝ)
    (hS : MeasurableSet {p : Ξ × ℝ | p.2 ∈ S p.1}) :
    Measurable (fun p : Ξ × Own => μ p.1 p.2 (I \ S p.1)) := by
  let κ : ProbabilityTheory.Kernel (Ξ × Own) ℝ :=
    ⟨fun p => μ p.1 p.2, Measure.measurable_of_measurable_coe (fun p : Ξ × Own => μ p.1 p.2) hm⟩
  letI : ProbabilityTheory.IsMarkovKernel κ := ⟨fun p => hprob p.1 p.2⟩
  have hs : MeasurableSet {p : (Ξ × Own) × ℝ | p.2 ∈ I \ S p.1.1} :=
    (hI.preimage measurable_snd).diff
      (hS.preimage (measurable_fst.fst.prodMk measurable_snd))
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) hs

end AndersonAC.SolS9
