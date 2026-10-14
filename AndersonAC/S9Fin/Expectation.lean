import AndersonAC.S9Fin.Torus
import AndersonAC.S9Fin.PrincipalProof
import AndersonAC.S9Fin.ProbabilityStatements

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9

namespace AndersonAC.SolS9

lemma truncatedReadout_nonneg (b : CertificateBounds) (ε q : ℝ) (hq : 0 ≤ q) :
    0 ≤ truncatedReadout b ε q := by
  exact le_min (mul_nonneg (by unfold cutMultiplier; positivity) hq)
    (columnConstant_pos_proof b).le

lemma windowRank_integrable {n Ξ : Type*} [Fintype n] [DecidableEq n]
    [MeasurableSpace Ξ] (μ : Measure Ξ) [IsFiniteMeasure μ]
    (H : Ξ → Matrix n n ℂ) (hH : ∀ ξ, (H ξ).IsHermitian) (E δ : ℝ)
    (hm : Measurable (fun ξ => (windowRank (H ξ) (hH ξ) E δ : ℝ))) :
    Integrable (fun ξ => (windowRank (H ξ) (hH ξ) E δ : ℝ)) μ := by
  refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded
    (C := (Fintype.card n : ℝ)) ?_⟩
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Matrix.rank_le_card_width (windowProjection (H ξ) (hH ξ) E δ)

lemma torusReadout_integrable (d m : ℕ) (coupling E η ε : ℝ) (b : CertificateBounds) :
    Integrable (fun ω => (∑ i, truncatedReadout b ε
      (scalarQ (periodicHamiltonian coupling ω) E η i)) / Fintype.card (Torus d m))
      (torusLaw d m) := by
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    truncatedReadout_torus_integrable d m coupling E η ε b i)).div_const _

lemma torusReadout_nonneg (d m : ℕ) (coupling E η ε : ℝ) (hη : 0 < η)
    (b : CertificateBounds) (ω : TorusConfiguration d m) :
    0 ≤ (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
      Fintype.card (Torus d m) := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun i _ => truncatedReadout_nonneg b ε _
    (scalarQ_nonneg _ (periodicHamiltonian_isHermitian_proof d m coupling ω) E η hη i)

set_option maxHeartbeats 800000 in
/-- The estimate assumes the deterministic comparison and cutoff-rank measurability.
It integrates the event under the true unconditioned law. -/
theorem finite_truncated_average_of_inputs (hRank : WindowRankMeasurableStatement.{0,0})
    (d m : ℕ) (coupling E η ε : ℝ)
    (hcoupling : 0 < coupling) (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (b : CertificateBounds)
    (hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian)
    (hCompare : ∀ ω : TorusConfiguration d m,
      allPrincipalInvertible (periodicHamiltonian coupling ω) E →
      matrixCertificate (periodicHamiltonian coupling ω) E η b →
      columnConstant b / 2 - 8 * (windowRank (periodicHamiltonian coupling ω)
        (hH ω) E (ε * η) : ℝ) / (η * Fintype.card (Torus d m)) ≤
      (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
        Fintype.card (Torus d m)) :
    columnConstant b / 2 * (torusLaw d m (trueCertificateEvent d m coupling E η b)).toReal -
      8 * (∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E (ε * η) : ℝ)
        ∂torusLaw d m) / (η * Fintype.card (Torus d m)) ≤
      ∫ ω, (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
        Fintype.card (Torus d m) ∂torusLaw d m := by
  let μ := torusLaw d m
  let S := trueCertificateEvent d m coupling E η b
  let N : ℝ := Fintype.card (Torus d m)
  let r (ω : TorusConfiguration d m) : ℝ :=
    windowRank (periodicHamiltonian coupling ω) (hH ω) E (ε * η)
  let f (ω : TorusConfiguration d m) :=
    (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) / N
  have hN : 0 < N := by
    change 0 < (Fintype.card (Torus d m) : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Torus d m))
  have hs : MeasurableSet S := trueCertificateEvent_measurable_proof d m coupling E η b
  have hr : Integrable r μ := windowRank_integrable μ _ hH E (ε * η)
    (hRank (Torus d m) (TorusConfiguration d m) _ hH
      (continuous_periodicHamiltonian d m coupling).measurable E (ε * η))
  have hf : Integrable f μ := torusReadout_integrable d m coupling E η ε b
  have hi : Integrable (S.indicator (fun _ : TorusConfiguration d m => columnConstant b / 2)) μ :=
    (integrable_const _).indicator hs
  have he : Integrable (fun ω => 8 * r ω / (η * N)) μ := (hr.const_mul 8).div_const _
  have hpoint : ∀ᵐ ω ∂μ,
      S.indicator (fun _ => columnConstant b / 2) ω - 8 * r ω / (η * N) ≤ f ω := by
    filter_upwards [true_principal_invertible_ae_proof d m coupling E hcoupling] with ω hω
    by_cases hSω : ω ∈ S
    · rw [Set.indicator_of_mem hSω]
      exact hCompare ω hω hSω
    · rw [Set.indicator_of_notMem hSω, zero_sub]
      apply le_trans _ (torusReadout_nonneg d m coupling E η ε hη b ω)
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (mul_pos hη hN).le)
  have hInt := integral_mono_ae (hi.sub he) hf hpoint
  simp only [Pi.sub_apply] at hInt
  rw [integral_sub hi he, integral_indicator_const _ hs,
    integral_div, integral_const_mul] at hInt
  rw [smul_eq_mul, mul_comm (μ.real S) (columnConstant b / 2)] at hInt
  exact hInt

end AndersonAC.SolS9
