import AndersonAC.S9Fin.CountingMeasure

noncomputable section
open MeasureTheory AndersonAC.S9
open scoped ENNReal

namespace AndersonAC.SolS9

def finitePoissonKernel (E η t : ℝ) : ℝ := η / ((t - E) ^ 2 + η ^ 2)

lemma finitePoissonKernel_measurable (E η : ℝ) : Measurable (finitePoissonKernel E η) := by
  unfold finitePoissonKernel
  fun_prop

lemma finitePoissonKernel_nonneg (E η t : ℝ) (hη : 0 < η) :
    0 ≤ finitePoissonKernel E η t := by
  unfold finitePoissonKernel
  positivity

/-- The uniform eta-inverse bound justifies taking the imaginary part
through the finite-measure integral. -/
lemma borelTransform_im_eq_finitePoisson (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E η : ℝ) (hη : 0 < η) :
    (AndersonAC.Blueprint.borelTransform μ ((E : ℂ) + η * Complex.I)).im =
      ∫ t, finitePoissonKernel E η t ∂μ := by
  let z : ℂ := (E : ℂ) + η * Complex.I
  have hr : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) μ := by
    have hm : Measurable (fun t : ℝ => ((t : ℂ) - z)⁻¹) :=
      (Complex.continuous_ofReal.measurable.sub measurable_const).inv
    refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := η⁻¹) ?_⟩
    filter_upwards [] with t
    have hd : η ≤ ‖(t : ℂ) - z‖ := by
      simpa [z, abs_of_pos hη] using Complex.abs_im_le_norm ((t : ℂ) - z)
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hη hd
  unfold AndersonAC.Blueprint.borelTransform
  change (∫ t, ((t : ℂ) - z)⁻¹ ∂μ).im = _
  change RCLike.im (∫ t, ((t : ℂ) - z)⁻¹ ∂μ) = _
  rw [← integral_im hr]
  apply integral_congr_ae
  filter_upwards [] with t
  simp [z, finitePoissonKernel, Complex.inv_im, Complex.normSq_apply]
  ring

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma finiteCountingMeasure_lintegral_poisson (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η : ℝ) (hη : 0 < η) :
    (∫⁻ t, ENNReal.ofReal (finitePoissonKernel E η t) ∂finiteCountingMeasure H hH) =
      ENNReal.ofReal (∑ i, scalarQ H E η i) := by
  rw [sum_scalarQ_eq_eigenvalues H hH E η hη]
  simp only [finiteCountingMeasure, lintegral_finsetSum_measure, lintegral_dirac]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  rfl

universe u v

lemma averagedCountingMeasure_poisson (hRank : WindowRankMeasurableStatement.{u,v})
    {n : Type u} [Fintype n] [DecidableEq n]
    {Ξ : Type v} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsFiniteMeasure μ]
    (H : Ξ → Matrix n n ℂ) (hH : ∀ ξ, (H ξ).IsHermitian) (hM : Measurable H)
    (E η : ℝ) (hη : 0 < η) :
    (AndersonAC.Blueprint.borelTransform (averagedCountingMeasure μ H hH)
      ((E : ℂ) + η * Complex.I)).im = ∫ ξ, (∑ i, scalarQ (H ξ) E η i) ∂μ := by
  letI := averagedCountingMeasure_finite hRank μ H hH hM
  have hm := finiteCountingMeasure_measurable hRank H hH hM
  have hp := finitePoissonKernel_measurable E η
  have hsum : Measurable (fun ξ => ∑ i, scalarQ (H ξ) E η i) :=
    Finset.measurable_sum Finset.univ (fun i _ => scalarQ_measurable H hM E η i)
  have hnon : ∀ ξ, 0 ≤ ∑ i, scalarQ (H ξ) E η i := by
    intro ξ
    exact Finset.sum_nonneg fun i _ => scalarQ_nonneg (H ξ) (hH ξ) E η hη i
  rw [borelTransform_im_eq_finitePoisson _ E η hη,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun t => finitePoissonKernel_nonneg E η t hη)) hp.aestronglyMeasurable]
  rw [averagedCountingMeasure, Measure.lintegral_bind (m := μ)
    (μ := fun ξ => finiteCountingMeasure (H ξ) (hH ξ))
    (f := fun t : ℝ => ENNReal.ofReal (finitePoissonKernel E η t)) hm.aemeasurable
    (ENNReal.measurable_ofReal.comp hp).aemeasurable]
  simp only [finiteCountingMeasure_lintegral_poisson _ _ E η hη]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hnon)
    hsum.aestronglyMeasurable).symm

end AndersonAC.SolS9
