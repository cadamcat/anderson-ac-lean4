import AndersonAC.S9Inf.ComparisonStatement
import AndersonAC.S9Inf.RootCoupling
import AndersonAC.S9Inf.BoundaryProbability
import AndersonAC.S9Inf.VolumeComparison
import AndersonAC.S9Fin.Basic
import AndersonAC.S9Fin.Scalar

/-! Transfer the finite root lower bound through the coupled law. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson AndersonAC.S9 AndersonAC.SolS9
open scoped Topology

namespace AndersonAC.SolS9Inf

theorem truncatedReadout_lipschitz (b : CertificateBounds) (ε q p : ℝ) :
    |truncatedReadout b ε q - truncatedReadout b ε p| ≤
      (2 * cutMultiplier ε) * |q - p| := by
  have hK : 0 ≤ 2 * cutMultiplier ε := by unfold cutMultiplier; positivity
  have h := abs_min_sub_min_le_max (2 * cutMultiplier ε * q) (columnConstant b)
    (2 * cutMultiplier ε * p) (columnConstant b)
  simp only [sub_self, abs_zero,
    max_eq_left (abs_nonneg (2 * cutMultiplier ε * q - 2 * cutMultiplier ε * p))] at h
  simpa only [truncatedReadout, ← mul_sub, abs_mul, abs_of_nonneg hK] using h

theorem truncatedReadout_bounds (b : CertificateBounds) (ε q : ℝ) (hq : 0 ≤ q) :
    0 ≤ truncatedReadout b ε q ∧ truncatedReadout b ε q ≤ columnConstant b := by
  have hK : 0 ≤ 2 * cutMultiplier ε := by unfold cutMultiplier; positivity
  exact ⟨le_min (mul_nonneg hK hq) (columnConstant_pos_proof b).le, min_le_right _ _⟩

theorem infinite_readout_measurable {d : ℕ} (coupling E η ε : ℝ) (hη : 0 < η)
    (b : CertificateBounds) : Measurable (fun ω : Configuration d =>
      truncatedReadout b ε (diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)).im) := by
  have hq := measurable_scalarGreen_of_potential potentialStrongContinuity_proof
    (d := d) coupling 0 0 ((E : ℂ) + η * Complex.I) (by simpa using hη)
  have h := ((Complex.measurable_im.comp hq).const_mul (2 * cutMultiplier ε)).min
    (measurable_const (a := columnConstant b))
  simpa only [Function.comp_apply, truncatedReadout, diagonalGreen, AndersonAC.Blueprint.diagonalGreen,
    AndersonAC.Blueprint.greenOperator, AndersonAC.Blueprint.delta, scalarGreen, green, basis] using h

theorem infinite_readout_bounds {d : ℕ} (coupling E η ε : ℝ) (hη : 0 < η)
    (b : CertificateBounds) (ω : Configuration d) :
    0 ≤ truncatedReadout b ε (diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)).im ∧
      truncatedReadout b ε (diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)).im ≤
        columnConstant b := by
  apply truncatedReadout_bounds
  have h := green_quadratic_im_nonneg _ (hamiltonian_isSelfAdjoint coupling ω)
    ((E : ℂ) + η * Complex.I) (by simpa using hη) (basis 0)
  simpa only [diagonalGreen, AndersonAC.Blueprint.diagonalGreen,
    AndersonAC.Blueprint.greenOperator, AndersonAC.Blueprint.delta, green, basis] using h

theorem infinite_readout_integrable {d : ℕ} (coupling E η ε : ℝ) (hη : 0 < η)
    (b : CertificateBounds) : Integrable (fun ω : Configuration d =>
      truncatedReadout b ε (diagonalGreen coupling ω 0 ((E : ℂ) + η * Complex.I)).im)
        (disorderLaw d) := by
  refine ⟨(infinite_readout_measurable coupling E η ε hη b).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := columnConstant b) ?_⟩
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (infinite_readout_bounds coupling E η ε hη b ω).1]
  exact (infinite_readout_bounds coupling E η ε hη b ω).2

theorem infinite_root_readout_of_comparison (hcomparison : FiniteInfiniteComparisonStatement)
    (d : ℕ) (hd : 3 ≤ d) (coupling E ε : ℝ)
    (b : CertificateBounds) (η : ℕ → ℝ) (hη : comparableHeights η)
    (hε : 0 < ε)
    (hfinite : ∀ᶠ m in atTop, columnConstant b / 8 ≤
      ∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E (η m) 0)
        ∂torusLaw d m) :
    columnConstant b / 8 ≤ liminf (fun m => ∫ ω,
      truncatedReadout b ε (diagonalGreen coupling ω 0
        ((E : ℂ) + η m * Complex.I)).im ∂disorderLaw d) atTop := by
  let g (m : ℕ) (ω : Configuration d) :=
    truncatedReadout b ε (diagonalGreen coupling ω 0 ((E : ℂ) + η m * Complex.I)).im
  let J (m : ℕ) := ∫ ω, g m ω ∂disorderLaw d
  let K := 2 * cutMultiplier ε
  have hK : 0 ≤ K := by dsimp [K, cutMultiplier]; positivity
  have hgm (m : ℕ) : Measurable (g m) := infinite_readout_measurable coupling E _ ε (hη.1 m) b
  have hgi (m : ℕ) : Integrable (g m) (disorderLaw d) :=
    infinite_readout_integrable coupling E _ ε (hη.1 m) b
  have hJlower : atTop.IsBoundedUnder (· ≥ ·) J := by
    refine isBoundedUnder_of ⟨0, ?_⟩
    intro m
    exact integral_nonneg (fun ω => (infinite_readout_bounds coupling E _ ε (hη.1 m) b ω).1)
  have hJupper : atTop.IsBoundedUnder (· ≤ ·) J := by
    refine isBoundedUnder_of ⟨columnConstant b, ?_⟩
    intro m
    have h := integral_mono (hgi m) (integrable_const (columnConstant b))
      (fun ω => (infinite_readout_bounds coupling E _ ε (hη.1 m) b ω).2)
    simpa [J] using h
  obtain ⟨C, c, hC, hc, hcomp⟩ := hcomparison d hd coupling
  let err (m : ℕ) := C * (sideLength m : ℝ) ^ (d - 1) * (η m)⁻¹ ^ 2 *
    Real.exp (-c * η m * sideLength m)
  have herr : Tendsto (fun m => K * err m) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := K)).mul
      (volume_comparison_error_tendsto_proof d η hη C c hc)
  have hηevent : ∀ᶠ m in atTop, η m ∈ Set.Ioc (0 : ℝ) 1 := by
    have hlim := tendsto_nhds_of_tendsto_nhdsWithin (comparable_heights_tendsto η hη)
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m hm
    exact ⟨hη.1 m, hm.le⟩
  have hdiff : ∀ᶠ m in atTop,
      |(∫ ω, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E (η m) 0)
        ∂torusLaw d m) - J m| ≤ K * err m := by
    filter_upwards [hcomp, hηevent] with m hm hηm
    obtain ⟨Q⟩ := rootCoupling_exists_proof d m
    letI : IsProbabilityMeasure Q.law := Q.probability
    let F (ωm : TorusConfiguration d m) :=
      truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ωm) E (η m) 0)
    have hFm : Measurable F :=
      ((scalarQ_measurable _ (continuous_periodicHamiltonian d m coupling).measurable
        E (η m) 0).const_mul K).min measurable_const
    have hFi : Integrable F (torusLaw d m) := truncatedReadout_torus_integrable d m coupling E _ ε b 0
    have hmpF : MeasurePreserving Prod.fst Q.law (torusLaw d m) := ⟨measurable_fst, Q.finite_marginal⟩
    have hmpG : MeasurePreserving Prod.snd Q.law (disorderLaw d) := ⟨measurable_snd, Q.infinite_marginal⟩
    have hFint : Integrable (fun p : TorusConfiguration d m × Configuration d => F p.1) Q.law :=
      hmpF.integrable_comp_of_integrable hFi
    have hGint : Integrable (fun p : TorusConfiguration d m × Configuration d => g m p.2) Q.law :=
      hmpG.integrable_comp_of_integrable (hgi m)
    have hFmap : (∫ ω, F ω ∂torusLaw d m) = ∫ p, F p.1 ∂Q.law := by
      rw [← Q.finite_marginal]
      exact integral_map_of_stronglyMeasurable measurable_fst hFm.stronglyMeasurable
    have hGmap : J m = ∫ p, g m p.2 ∂Q.law := by
      dsimp [J]
      rw [← Q.infinite_marginal]
      exact integral_map_of_stronglyMeasurable measurable_snd (hgm m).stronglyMeasurable
    have hbound : ∀ᵐ p ∂Q.law, ‖F p.1 - g m p.2‖ ≤ K * err m := by
      filter_upwards [Q.matched] with p hp
      rw [Real.norm_eq_abs]
      apply (truncatedReadout_lipschitz b ε _ _).trans
      apply (mul_le_mul_of_nonneg_left ?_ hK).trans
        (mul_le_mul_of_nonneg_left (hm E (η m) hηm p.1 p.2 hp) hK)
      simpa only [scalarQ, Complex.sub_im, matrixResolvent, diagonalGreen] using Complex.abs_im_le_norm
        (matrixResolvent (periodicHamiltonian coupling p.1) E (η m) 0 0 -
          diagonalGreen coupling p.2 0 ((E : ℂ) + η m * Complex.I))
    have h := norm_integral_le_of_norm_le_const hbound
    rw [integral_sub hFint hGint, ← hFmap, ← hGmap] at h
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  apply (le_liminf_iff' hJupper.isCoboundedUnder_ge hJlower).mpr
  intro q hq
  filter_upwards [hfinite, hdiff, herr.eventually (gt_mem_nhds (sub_pos.mpr hq))] with m hf hm he
  have hfg := (abs_le.mp hm).2
  linarith

end AndersonAC.SolS9Inf
