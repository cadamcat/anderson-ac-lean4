/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.MetricSpace.Polish

/-!
# Ported Herglotz and Nevanlinna representation from TauCeti (Apache-2.0)

This file ports the minimal self-contained closure for
`TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add` from the Apache-2.0 licensed TauCeti
library (`refs/external/TauCeti-Nevanlinna.lean` and its upstream dependencies `Prokhorov.lean`,
`Circle.lean`, `Herglotz.lean`, `Cayley.lean`, and `Pick/Basic.lean`) to Lean 4.34.1.
-/

noncomputable section

open Complex MeasureTheory Metric Real Set Filter Topology Bornology
open scoped NNReal ENNReal ComplexConjugate Topology

namespace TauCeti

/-! ### From `TauCeti.MeasureTheory.Measure.Prokhorov` -/

section Prokhorov

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [T2Space α] [BorelSpace α]

omit [T2Space α] [BorelSpace α] in
private lemma exists_monotone_isCompact_measure_compl_le
    {σ : ℕ → Measure α} (hTight : IsTightMeasureSet (Set.range σ))
    {u : ℕ → ℝ≥0} (hu_pos : ∀ j, 0 < u j) :
    ∃ K : ℕ → Set α, Monotone K ∧ (∀ j, IsCompact (K j)) ∧
      ∀ j n, (σ n) (K j)ᶜ ≤ (u j : ENNReal) := by
  have hchoose : ∀ j, ∃ K : Set α, IsCompact K ∧ ∀ n, (σ n) Kᶜ ≤ (u j : ENNReal) := by
    intro j
    obtain ⟨K, hK, htail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight
        (u j : ENNReal) (by exact_mod_cast hu_pos j)
    exact ⟨K, hK, fun n => htail (σ n) (Set.mem_range_self n)⟩
  choose K hK_comp hK_tail using hchoose
  refine ⟨Set.accumulate K, Set.monotone_accumulate,
    fun j => isCompact_accumulate hK_comp j, fun j n => ?_⟩
  exact (measure_mono (compl_subset_compl.mpr (Set.subset_accumulate (s := K) (x := j)))).trans
    (hK_tail j n)

lemma finite_measure_cluster_limit (σ : ℕ → Measure α) (C : ℝ≥0)
    (hmass : ∀ n, (σ n) univ ≤ (C : ENNReal)) (hTight : IsTightMeasureSet (Set.range σ)) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop ∧ IsFiniteMeasure μ₀ ∧
      μ₀ univ ≤ (C : ENNReal) ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun n => ∫ x, g x ∂(σ n)) (U : Filter ℕ)
          (nhds (∫ x, g x ∂μ₀)) := by
  have hfin : ∀ n, IsFiniteMeasure (σ n) := fun n =>
    ⟨(hmass n).trans_lt ENNReal.coe_lt_top⟩
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  obtain ⟨u, -, hu_pos, hu_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  obtain ⟨K, hKmono, hK_comp, hK_tail⟩ :=
    exists_monotone_isCompact_measure_compl_le hTight hu_pos
  let S : Set (FiniteMeasure α) := {μ | μ.mass ≤ C ∧ ∀ j, μ (K j)ᶜ ≤ u j}
  have hcompact : IsCompact S := by
    simpa [S] using
      isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
        (E := α) (C := C) (u := u) (K := K) hu_lim hK_comp (Or.inr hKmono)
  have hσ_mem : ∀ n, σf n ∈ S := by
    refine fun n => ⟨?_, fun j => ?_⟩
    · dsimp [σf, S, FiniteMeasure.mass]
      exact ENNReal.coe_le_coe.mp (by simpa using hmass n)
    · exact ENNReal.coe_le_coe.mp (by simpa [σf] using hK_tail j n)
  have hmap_le : map σf atTop ≤ 𝓟 S :=
    tendsto_principal.mpr (Eventually.of_forall hσ_mem)
  obtain ⟨μf, hμfS, hcluster⟩ := hcompact hmap_le
  have hmapcluster : MapClusterPt μf atTop σf := hcluster
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hmapcluster
  refine ⟨(μf : Measure α), U, hUle, inferInstance, ?_, ?_⟩
  · have hle : (μf.mass : ENNReal) ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr hμfS.1
    rw [← FiniteMeasure.ennreal_mass]
    simpa using hle
  · intro g
    have hweak :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend) g
    simpa [σf] using hweak

end Prokhorov

/-! ### From `TauCeti.MeasureTheory.Group.Circle` -/

def circleDensityMeasure (φ : ℂ → ℝ) : Measure Circle :=
  ((volume.restrict (Ioc 0 (2 * π))).withDensity
    fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ))).map Circle.exp

private lemma continuous_comp_circleMap {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) :
    Continuous fun θ ↦ φ (circleMap 0 1 θ) :=
  hφ.comp_continuous (continuous_circleMap 0 1) fun θ ↦ circleMap_mem_sphere 0 zero_le_one θ

theorem isFiniteMeasure_circleDensityMeasure {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (sphere 0 1)) : IsFiniteMeasure (circleDensityMeasure φ) := by
  have hint : IntegrableOn (fun θ ↦ (2 * π)⁻¹ * φ (circleMap 0 1 θ)) (Ioc 0 (2 * π)) :=
    ((continuous_const.mul (continuous_comp_circleMap hφ)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have := isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  unfold circleDensityMeasure
  infer_instance

theorem integral_circleDensityMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1))
    (hφ₀ : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ φ z) {g : ℂ → E} (hg : ContinuousOn g (sphere 0 1)) :
    ∫ z : Circle, g z ∂circleDensityMeasure φ = circleAverage (fun ζ ↦ φ ζ • g ζ) 0 1 := by
  have hgc : Continuous fun z : Circle ↦ g z :=
    hg.comp_continuous continuous_subtype_val fun z ↦ by simp
  have hexp : ∀ θ : ℝ, (Circle.exp θ : ℂ) = circleMap 0 1 θ := fun θ ↦ by
    simp [Circle.coe_exp, circleMap]
  have hmeas : Measurable fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ)) :=
    (continuous_const.mul (continuous_comp_circleMap hφ)).measurable.ennreal_ofReal
  rw [circleDensityMeasure, integral_map Circle.exp.continuous.aemeasurable
    hgc.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hmeas
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top), circleAverage_def,
    intervalIntegral.integral_of_le (by positivity), ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun θ ↦ ?_)
  have h₀ : 0 ≤ (2 * π)⁻¹ * φ (circleMap 0 1 θ) :=
    mul_nonneg (by positivity) (hφ₀ _ (circleMap_mem_sphere 0 zero_le_one θ))
  simp only [hexp, ENNReal.toReal_ofReal h₀, smul_smul]

/-! ### From `TauCeti.Analysis.Complex.Herglotz` -/

section Herglotz

variable {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}

private lemma circleAverage_herglotzRieszKernel_smul_re_add_of_center_zero
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hw : w ∈ ball 0 R) :
    circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • ((f ζ).re : ℂ)) 0 R + (f 0).im * I =
      f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hcont : ContinuousOn f (sphere 0 |R|) := by
    refine hf.2.mono ?_
    rw [abs_of_pos hR, closure_ball 0 hR.ne']
    exact sphere_subset_closedBall
  have hre : CircleIntegrable (fun ζ ↦ (f ζ).re) 0 R :=
    (continuous_re.comp_continuousOn hcont).circleIntegrable'
  have hreC : CircleIntegrable (fun ζ ↦ ((f ζ).re : ℂ)) 0 R :=
    (continuous_ofReal.comp_continuousOn (continuous_re.comp_continuousOn hcont)).circleIntegrable'
  have hball : ball (0 : ℂ) R ⊆ (sphere 0 |R|)ᶜ := by
    intro z hz hzs
    rw [abs_of_pos hR, mem_sphere_zero_iff_norm] at hzs
    exact (mem_ball_zero_iff.1 hz).ne hzs
  set G : ℂ → ℂ := fun z ↦
    circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • ((f ζ).re : ℂ)) 0 R with hG_def
  have hG : AnalyticOnNhd ℂ G (ball 0 R) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hreC).mono hball
  have hF : AnalyticOnNhd ℂ f (ball 0 R) := hf.1.analyticOnNhd isOpen_ball
  have hreeq : ∀ z ∈ ball (0 : ℂ) R, ((G - f) z).re = 0 := by
    intro z hz
    have hint : CircleIntegrable ((re ∘ herglotzRieszKernel 0 z) • f) 0 R :=
      ((continuous_re.comp_continuousOn
        (continuousOn_herglotzRieszKernel_sphere (hball hz))).smul hcont).circleIntegrable'
    have h₁ := re_circleAverage_herglotzRieszKernel_smul hre (hball hz)
    have h₂ := reCLM.circleAverage_comp_comm hint
    rw [hf.circleAverage_re_herglotzRieszKernel_smul hz, reCLM_apply] at h₂
    rw [Pi.sub_apply, sub_re, hG_def, h₁, ← h₂, sub_eq_zero]
    congr 1
    ext ζ
    simp
  obtain ⟨k, hk⟩ := (hG.sub hF).eq_const_of_re_eq_const hreeq isOpen_ball (isConnected_ball hR)
  have hG₀ : G 0 = ((f 0).re : ℂ) := by
    have hsphere : EqOn (fun ζ ↦ herglotzRieszKernel 0 0 ζ • ((f ζ).re : ℂ))
        ((ofRealCLM.comp reCLM) ∘ f) (sphere 0 |R|) := by
      intro ζ hζ
      have hζ₀ : ζ ≠ 0 := ne_of_mem_sphere hζ (abs_pos.2 hR.ne').ne'
      simp [herglotzRieszKernel_def, hζ₀]
    have hf' : DiffContOnCl ℂ f (ball 0 |R|) := by rwa [abs_of_pos hR]
    rw [hG_def]
    dsimp only
    rw [circleAverage_congr_sphere hsphere,
      (ofRealCLM.comp reCLM).circleAverage_comp_comm hcont.circleIntegrable', hf'.circleAverage]
    simp
  have e₁ := hk w hw
  have e₀ := hk 0 (mem_ball_self hR)
  simp only [Pi.sub_apply] at e₁ e₀
  linear_combination e₁ - e₀ + hG₀ + re_add_im (f 0)

theorem _root_.DiffContOnCl.circleAverage_herglotzRieszKernel_smul_re_add
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • ((f ζ).re : ℂ)) c R + (f c).im * I =
      f w := by
  have hg : DiffContOnCl ℂ (fun z ↦ f (z + c)) (ball 0 R) :=
    hf.comp (DifferentiableOn.diffContOnCl <| by fun_prop) (by intro; aesop)
  have hw' : w - c ∈ ball 0 R := by simpa using mem_ball_iff_norm.1 hw
  have h := circleAverage_herglotzRieszKernel_smul_re_add_of_center_zero hg hw'
  simp only [zero_add, sub_add_cancel] at h
  rw [← circleAverage_map_add_const]
  simpa [herglotzRieszKernel_add_const] using h

noncomputable def _root_.MeasureTheory.Measure.herglotzTransform (μ : Measure Circle) (w : ℂ) : ℂ :=
  ∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂μ

theorem _root_.MeasureTheory.Measure.herglotzTransform_def (μ : Measure Circle) (w : ℂ) :
    μ.herglotzTransform w = ∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂μ := by
  rw [Measure.herglotzTransform]

private lemma coe_sub_ne_zero (hw : w ∈ ball (0 : ℂ) 1) (z : Circle) : (z : ℂ) - w ≠ 0 := by
  rw [sub_ne_zero]
  rintro rfl
  simp at hw

private lemma continuous_add_div_sub (hw : w ∈ ball (0 : ℂ) 1) :
    Continuous fun z : Circle ↦ ((z : ℂ) + w) / ((z : ℂ) - w) :=
  (continuous_subtype_val.add continuous_const).div (continuous_subtype_val.sub continuous_const)
    (coe_sub_ne_zero hw)

private lemma exists_isFiniteMeasure_comp_mul_eq_integral_add_div_sub
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (F w).re) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    ∃ ν : Measure Circle, IsFiniteMeasure ν ∧ ∀ w ∈ ball (0 : ℂ) 1,
      F (r * w) = ν.herglotzTransform w + (F 0).im * I := by
  have hmaps : MapsTo (fun z : ℂ ↦ (r : ℂ) * z) (closedBall 0 1) (ball 0 1) := fun z hz ↦ by
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_of_nonneg hr₀]
    nlinarith [norm_nonneg z]
  have hdiff : DifferentiableOn ℂ (fun z ↦ F (r * z)) (closedBall 0 1) :=
    hF.comp (by fun_prop) hmaps
  have hφc : ContinuousOn (fun ζ ↦ (F (r * ζ)).re) (sphere 0 1) :=
    continuous_re.comp_continuousOn (hdiff.continuousOn.mono sphere_subset_closedBall)
  have hφ₀ : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ (F (r * z)).re := fun z hz ↦
    hre _ (hmaps (sphere_subset_closedBall hz))
  refine ⟨circleDensityMeasure fun ζ ↦ (F (r * ζ)).re,
    isFiniteMeasure_circleDensityMeasure hφc, fun w hw ↦ ?_⟩
  have hK : ContinuousOn (fun ζ : ℂ ↦ (ζ + w) / (ζ - w)) (sphere 0 1) := by
    have hw' : w ∉ sphere (0 : ℂ) |1| := by
      rw [abs_one, mem_sphere_zero_iff_norm]
      exact (mem_ball_zero_iff.1 hw).ne
    simpa [herglotzRieszKernel_fun_def] using continuousOn_herglotzRieszKernel_sphere hw'
  have hcl : DiffContOnCl ℂ (fun z ↦ F (r * z)) (ball 0 1) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball 0 one_ne_zero])
  have h := hcl.circleAverage_herglotzRieszKernel_smul_re_add hw
  rw [mul_zero] at h
  rw [Measure.herglotzTransform_def, ← h, integral_circleDensityMeasure hφc hφ₀ hK]
  congr 2
  ext ζ
  simp [herglotzRieszKernel_def, Complex.real_smul, mul_comm]

theorem exists_isFiniteMeasure_eq_herglotzTransform_add
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (F w).re) :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧ ∀ w ∈ ball (0 : ℂ) 1,
      F w = μ.herglotzTransform w + (F 0).im * I := by
  set r : ℕ → ℝ := fun n ↦ 1 - 1 / ((n : ℝ) + 1) with hr_def
  have hr_lim : Tendsto r atTop (𝓝 1) := by
    simpa [hr_def] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hdil : ∀ n, ∃ ν : Measure Circle, IsFiniteMeasure ν ∧ ∀ w ∈ ball (0 : ℂ) 1,
      F (r n * w) = ν.herglotzTransform w + (F 0).im * I := fun n ↦
    exists_isFiniteMeasure_comp_mul_eq_integral_add_div_sub hF hre
      (by simp only [hr_def, sub_nonneg]
          exact div_le_one_of_le₀ (by linarith [n.cast_nonneg (α := ℝ)]) (by positivity))
      (by simp only [hr_def]; linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)])
  choose μs hμs hrep using hdil
  have hre₀ : 0 ≤ (F 0).re := hre 0 (mem_ball_self one_pos)
  let C : ℝ≥0 := ⟨(F 0).re, hre₀⟩
  have hmass : ∀ n, μs n univ ≤ C := fun n ↦ by
    have h := congrArg re (hrep n 0 (mem_ball_self one_pos))
    simp only [mul_zero, Measure.herglotzTransform_def, add_zero, sub_zero, ne_eq,
      Circle.coe_ne_zero, not_false_eq_true, div_self, integral_const, real_smul, mul_one, add_re,
      ofReal_re, mul_re, I_re, ofReal_im, I_im, sub_self] at h
    rw [← ofReal_measureReal (measure_ne_top _ _), ← h, ENNReal.ofReal_eq_coe_nnreal hre₀]
    exact le_rfl
  obtain ⟨μ, U, hU, hμ, -, hlim⟩ :=
    finite_measure_cluster_limit μs _ hmass IsTightMeasureSet.of_compactSpace
  refine ⟨μ, hμ, fun w hw ↦ ?_⟩
  let μf : ℕ → FiniteMeasure Circle := fun n ↦ ⟨μs n, hμs n⟩
  let μf₀ : FiniteMeasure Circle := ⟨μ, hμ⟩
  have hweak : Tendsto μf U (𝓝 μf₀) := FiniteMeasure.tendsto_iff_forall_integral_tendsto.2 hlim
  have hconv := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hweak
    (.mkOfCompact ⟨_, continuous_add_div_sub hw⟩)
  have hFlim : Tendsto (fun n ↦ F (r n * w)) U (𝓝 (F w)) := by
    have h : Tendsto (fun n ↦ (r n : ℂ) * w) atTop (𝓝 w) := by
      simpa using ((continuous_ofReal.tendsto 1).comp hr_lim).mul_const w
    exact ((hF.continuousOn.continuousAt (isOpen_ball.mem_nhds hw)).tendsto.comp h).mono_left hU
  exact tendsto_nhds_unique hFlim ((hconv.add_const _).congr fun n ↦ by
    rw [hrep n w hw, Measure.herglotzTransform_def]
    simp only [FiniteMeasure.toMeasure_mk, BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk, μf])

end Herglotz

/-! ### From `TauCeti.Analysis.Complex.UnitDisc.Basic` and `UpperHalfPlane.Cayley` -/

theorem ne_of_mem_ball_of_norm_eq_one {ζ w : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1)
    (hw : ‖w‖ = 1) : ζ ≠ w := by
  intro h
  have hnorm := congrArg norm h
  rw [hw] at hnorm
  exact (mem_ball_zero_iff.mp hζ).ne hnorm

theorem add_I_ne_zero_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := fun h => by
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

private theorem norm_add_I_sq (z : ℂ) : ‖z + I‖ ^ 2 = ‖z - I‖ ^ 2 + 4 * z.im := by
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
  ring

theorem norm_sub_I_div_add_I_lt_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖(z - I) / (z + I)‖ < 1 ↔ 0 < z.im := by
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hz), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_add_I_sq]
  constructor <;> intro h <;> linarith

theorem injOn_sub_I_div_add_I :
    InjOn (fun z : ℂ => (z - I) / (z + I)) {z | z + I ≠ 0} := by
  intro z hz w hw h
  simp only [mem_ofPred_eq] at hz hw
  rw [div_eq_div_iff hz hw] at h
  have h2 : (2 * I) * (z - w) = 0 := by linear_combination h
  simpa [sub_eq_zero, I_ne_zero] using h2

private theorem sub_I_div_add_I_inverse {w : ℂ} (hw : w ≠ 1) :
    I * (1 + w) / (1 - w) + I ≠ 0 ∧
      (I * (1 + w) / (1 - w) - I) / (I * (1 + w) / (1 - w) + I) = w := by
  have h1 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hden : I * (1 + w) / (1 - w) + I = 2 * I / (1 - w) := by
    field_simp
    ring
  have hnum : I * (1 + w) / (1 - w) - I = 2 * I * w / (1 - w) := by
    field_simp
    ring
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  refine ⟨hden ▸ div_ne_zero h2I h1, ?_⟩
  rw [hden, hnum]
  field_simp

theorem I_mul_one_add_sub_I_div_add_I_div_one_sub {z : ℂ} (hz : z + I ≠ 0) :
    I * (1 + (z - I) / (z + I)) / (1 - (z - I) / (z + I)) = z := by
  field_simp
  ring

theorem bijOn_sub_I_div_add_I_upperHalfPlaneSet :
    BijOn (fun z : ℂ => (z - I) / (z + I)) UpperHalfPlane.upperHalfPlaneSet
      (ball 0 1) := by
  refine ⟨fun z hz => ?_, injOn_sub_I_div_add_I.mono fun z hz => ?_, fun w hw => ?_⟩
  · exact mem_ball_zero_iff.mpr
      ((norm_sub_I_div_add_I_lt_one_iff (add_I_ne_zero_of_im_nonneg (le_of_lt hz))).mpr hz)
  · exact add_I_ne_zero_of_im_nonneg (le_of_lt hz)
  · have hw1 : w ≠ 1 := by
      rintro rfl
      simp at hw
    obtain ⟨hne, heq⟩ := sub_I_div_add_I_inverse hw1
    refine ⟨_, ?_, heq⟩
    rw [UpperHalfPlane.upperHalfPlaneSet, mem_ofPred_eq, ← norm_sub_I_div_add_I_lt_one_iff hne, heq]
    exact mem_ball_zero_iff.mp hw

theorem bijOn_I_mul_one_add_div_one_sub_ball :
    BijOn (fun w : ℂ => I * (1 + w) / (1 - w)) (ball 0 1)
      UpperHalfPlane.upperHalfPlaneSet := by
  refine bijOn_sub_I_div_add_I_upperHalfPlaneSet.symm ⟨fun w hw => ?_, fun z hz => ?_⟩
  · refine (sub_I_div_add_I_inverse ?_).2
    rintro rfl
    simp at hw
  · have hz' := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
    exact I_mul_one_add_sub_I_div_add_I_div_one_sub hz'

theorem hasDerivAt_I_mul_one_add_div_one_sub {w : ℂ} (hw : w ≠ 1) :
    HasDerivAt (fun u : ℂ => I * (1 + u) / (1 - u)) (2 * I / (1 - w) ^ 2) w := by
  have h1 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  refine ((((hasDerivAt_id w).const_add 1).const_mul I).div
    ((hasDerivAt_id w).const_sub 1) h1).congr_deriv ?_
  simp only [id]
  field_simp
  ring

noncomputable def boundaryCayley (x : ℝ) : Circle :=
  ⟨((x : ℂ) - I) / ((x : ℂ) + I), by
    refine mem_sphere_zero_iff_norm.2 ?_
    rw [norm_div]
    have hnorm : ‖(x : ℂ) - I‖ = ‖(x : ℂ) + I‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
        ← normSq_eq_norm_sq]
      simp [normSq_apply]
    rw [hnorm]
    apply div_self
    rw [norm_ne_zero_iff]
    intro h
    have := congrArg im h
    norm_num at this⟩

@[simp]
theorem coe_boundaryCayley (x : ℝ) :
    (boundaryCayley x : ℂ) = ((x : ℂ) - I) / ((x : ℂ) + I) :=
  by rw [boundaryCayley]

@[simp]
theorem boundaryCayley_ne_one (x : ℝ) : boundaryCayley x ≠ 1 := by
  intro h
  have h' := congrArg ((↑) : Circle → ℂ) h
  simp only [coe_boundaryCayley, Circle.coe_one] at h'
  have hden : (x : ℂ) + I ≠ 0 := by
    intro hzero
    have := congrArg im hzero
    simp at this
  rw [div_eq_one_iff_eq hden] at h'
  have := congrArg im h'
  norm_num at this

/-! ### From `TauCeti.Analysis.Complex.Pick.Basic` -/

private lemma add_I_ne_zero_of_mem_upperHalfPlane {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    z + I ≠ 0 :=
  add_I_ne_zero_of_im_nonneg (le_of_lt hz)

private lemma cayley_mem_ball {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (z - I) / (z + I) ∈ ball (0 : ℂ) 1 :=
  bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo hz

theorem exists_isFiniteMeasure_eq_I_mul_herglotzTransform_cayley_add {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧ ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = I * μ.herglotzTransform ((z - I) / (z + I)) + (F I).re := by
  let G : ℂ → ℂ := fun w => -I * F (I * (1 + w) / (1 - w))
  have hG : DifferentiableOn ℂ G (ball 0 1) := by
    intro w hw
    have hmem := bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hw
    have hinner : DifferentiableAt ℂ (fun u : ℂ => I * (1 + u) / (1 - u)) w :=
      (hasDerivAt_I_mul_one_add_div_one_sub
        (ne_of_mem_ball_of_norm_eq_one hw norm_one)).differentiableAt
    have hF' : DifferentiableAt ℂ F (I * (1 + w) / (1 - w)) :=
      (hF _ hmem).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hmem)
    exact ((differentiableAt_const (-I)).mul (hF'.comp w hinner)).differentiableWithinAt
  have hGre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (G w).re := by
    intro w hw
    simpa [G, mul_re] using him _ (bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hw)
  obtain ⟨μ, hμ, hrep⟩ := exists_isFiniteMeasure_eq_herglotzTransform_add hG hGre
  refine ⟨μ, hμ, fun z hz => ?_⟩
  have hcz := cayley_mem_ball hz
  have h := hrep ((z - I) / (z + I)) hcz
  dsimp only [G] at h
  rw [I_mul_one_add_sub_I_div_add_I_div_one_sub (add_I_ne_zero_of_mem_upperHalfPlane hz)] at h
  have hc : (G 0).im = -(F I).re := by
    simp [G]
  rw [hc] at h
  calc
    F z = I * (-I * F z) := by
      rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
    _ = I * (μ.herglotzTransform ((z - I) / (z + I)) + ((-(F I).re : ℝ) : ℂ) * I) :=
      congrArg (I * ·) h
    _ = I * μ.herglotzTransform ((z - I) / (z + I)) + (F I).re := by
      rw [mul_add]
      congr 1
      rw [← mul_assoc, mul_comm I ((-(F I).re : ℝ) : ℂ), mul_assoc, I_mul_I]
      simp

/-! ### From `TauCeti.Analysis.Complex.Pick.Nevanlinna` -/

def circleCayleyInv (z : Circle) : ℝ :=
  -(z : ℂ).im / (1 - (z : ℂ).re)

@[simp]
theorem circleCayleyInv_boundaryCayley (x : ℝ) :
    circleCayleyInv (boundaryCayley x) = x := by
  simp only [circleCayleyInv, coe_boundaryCayley, div_re, div_im, sub_re, sub_im,
    ofReal_re, ofReal_im, I_re, I_im, add_re, add_im, normSq_apply]
  field_simp
  ring

@[simp]
theorem boundaryCayley_re (x : ℝ) :
    (((x : ℂ) - I) / ((x : ℂ) + I)).re = (x ^ 2 - 1) / (x ^ 2 + 1) := by
  rw [div_re]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    normSq_apply]
  ring

@[simp]
theorem boundaryCayley_im (x : ℝ) :
    (((x : ℂ) - I) / ((x : ℂ) + I)).im = -(2 * x) / (x ^ 2 + 1) := by
  rw [div_im]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    normSq_apply]
  ring

private theorem one_sub_re_ne_zero_of_ne_one {z : Circle} (hz : z ≠ 1) :
    1 - (z : ℂ).re ≠ 0 := by
  intro h
  have hre : (z : ℂ).re = 1 := by linarith
  have him : (z : ℂ).im = 0 := by
    have hs := Circle.normSq_coe z
    rw [normSq_apply, hre] at hs
    nlinarith [sq_nonneg (z : ℂ).im]
  apply hz
  apply Circle.ext
  apply Complex.ext <;> simp [hre, him]

theorem boundaryCayley_circleCayleyInv {z : Circle} (hz : z ≠ 1) :
    boundaryCayley (circleCayleyInv z) = z := by
  apply Circle.ext
  have hden := one_sub_re_ne_zero_of_ne_one hz
  have hcircle := Circle.normSq_coe z
  rw [normSq_apply] at hcircle
  have hquad : (z : ℂ).im ^ 2 + (1 - (z : ℂ).re) ^ 2 =
      2 * (1 - (z : ℂ).re) := by
    nlinarith [hcircle]
  have hquadpos : 0 < (z : ℂ).im ^ 2 + (1 - (z : ℂ).re) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hden)
  apply Complex.ext
  · rw [coe_boundaryCayley, boundaryCayley_re]
    simp only [circleCayleyInv]
    have hdenom : 0 < (-(z : ℂ).im / (1 - (z : ℂ).re)) ^ 2 + 1 := by positivity
    rw [div_eq_iff hdenom.ne']
    field_simp [hden, hquadpos.ne']
    nlinarith [hquad]
  · rw [coe_boundaryCayley, boundaryCayley_im]
    simp only [circleCayleyInv]
    have hdenom : 0 < (-(z : ℂ).im / (1 - (z : ℂ).re)) ^ 2 + 1 := by positivity
    rw [div_eq_iff hdenom.ne']
    field_simp [hden, hquadpos.ne']
    rw [hquad]
    ring

@[fun_prop]
theorem continuous_boundaryCayley : Continuous boundaryCayley := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : ℝ => (boundaryCayley x : ℂ))
  simp_rw [coe_boundaryCayley]
  exact Continuous.div (by fun_prop) (by fun_prop) fun x h ↦ by
    have := congrArg im h
    norm_num at this

@[fun_prop]
theorem measurable_circleCayleyInv : Measurable circleCayleyInv := by
  unfold circleCayleyInv
  fun_prop

def _root_.MeasureTheory.Measure.cayleyPushforward (mu : Measure Circle) : Measure ℝ :=
  (mu.restrict ({1}ᶜ : Set Circle)).map circleCayleyInv

instance _root_.MeasureTheory.Measure.isFiniteMeasure_cayleyPushforward
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    IsFiniteMeasure mu.cayleyPushforward := by
  unfold Measure.cayleyPushforward
  infer_instance

theorem integral_circle_eq_atom_add_integral_cayleyPushforward {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (mu : Measure Circle)
    [IsFiniteMeasure mu] (f : Circle → E) (hf : Continuous f) :
    ∫ z, f z ∂mu = mu.real {1} • f 1 + ∫ x, f (boundaryCayley x) ∂mu.cayleyPushforward := by
  have hfi : Integrable f mu :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hsingle : Integrable f (mu.restrict ({1} : Set Circle)) := hfi.restrict
  have hcompl : Integrable f (mu.restrict ({1}ᶜ : Set Circle)) := hfi.restrict
  calc
    ∫ z, f z ∂mu = ∫ z, f z ∂(mu.restrict {1} + mu.restrict ({1}ᶜ : Set Circle)) := by
      rw [Measure.restrict_add_restrict_compl (measurableSet_singleton 1)]
    _ = ∫ z, f z ∂mu.restrict {1} + ∫ z, f z ∂mu.restrict ({1}ᶜ : Set Circle) :=
      integral_add_measure hsingle hcompl
    _ = mu.real {1} • f 1 + ∫ z, f z ∂mu.restrict ({1}ᶜ : Set Circle) := by
      rw [integral_singleton]
    _ = mu.real {1} • f 1 + ∫ x, f (boundaryCayley x) ∂mu.cayleyPushforward := by
      congr 1
      unfold Measure.cayleyPushforward
      change ∫ z, f z ∂mu.restrict ({1}ᶜ : Set Circle) =
        ∫ x, (f ∘ boundaryCayley) x ∂Measure.map circleCayleyInv
          (mu.restrict ({1}ᶜ : Set Circle))
      rw [integral_map measurable_circleCayleyInv.aemeasurable
        (hf.comp continuous_boundaryCayley).aestronglyMeasurable]
      refine integral_congr_ae ((ae_restrict_mem (measurableSet_singleton 1).compl).mono ?_)
      intro z hz
      exact congrArg f (boundaryCayley_circleCayleyInv (by simpa using hz)).symm

def nevanlinnaKernel (z : ℂ) (x : ℝ) : ℂ :=
  (1 + (x : ℂ) * z) / ((x : ℂ) - z)

@[fun_prop]
theorem measurable_nevanlinnaKernel (z : ℂ) : Measurable (nevanlinnaKernel z) := by
  unfold nevanlinnaKernel
  exact (measurable_const.add (Complex.measurable_ofReal.mul_const z)).div
    (Complex.measurable_ofReal.sub measurable_const)

theorem I_mul_herglotzKernel_cayley (z : ℂ) (x : ℝ)
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    I * (((boundaryCayley x : ℂ) + (z - I) / (z + I)) /
      ((boundaryCayley x : ℂ) - (z - I) / (z + I))) = nevanlinnaKernel z x := by
  have hxi : (x : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg im h
    simp at this
  have hzi : z + I ≠ 0 := by
    have hzpos : 0 < z.im := hz
    intro h
    have := congrArg im h
    simp only [add_im, I_im, zero_im] at this
    linarith
  have hxz : (x : ℂ) - z ≠ 0 := by
    have hzpos : 0 < z.im := hz
    intro h
    have := congrArg im h
    simp only [sub_im, ofReal_im, zero_sub, zero_im] at this
    linarith
  have hdiff : ((x : ℂ) - I) / ((x : ℂ) + I) - (z - I) / (z + I) ≠ 0 := by
    rw [div_sub_div _ _ hxi hzi]
    apply div_ne_zero
    · have heq : ((x : ℂ) - I) * (z + I) - ((x : ℂ) + I) * (z - I) =
          2 * I * ((x : ℂ) - z) := by ring
      rw [heq]
      exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hxz
    · exact mul_ne_zero hxi hzi
  simp only [coe_boundaryCayley, nevanlinnaKernel]
  field_simp [hxi, hzi, hxz, hdiff]
  have hsum : ((x : ℂ) - I) * (z + I) + ((x : ℂ) + I) * (z - I) =
      2 * ((x : ℂ) * z + 1) := by
    calc
      _ = 2 * (x : ℂ) * z - 2 * (I * I) := by ring
      _ = _ := by rw [I_mul_I]; ring
  have hsub : ((x : ℂ) - I) * (z + I) - ((x : ℂ) + I) * (z - I) =
      2 * I * ((x : ℂ) - z) := by ring
  rw [hsum, hsub]
  field_simp [hxz, I_ne_zero]
  ring

@[simp]
theorem nevanlinnaKernel_im (z : ℂ) (x : ℝ) :
    (nevanlinnaKernel z x).im = z.im * (1 + x ^ 2) / normSq ((x : ℂ) - z) := by
  simp only [nevanlinnaKernel, div_im, normSq_apply, add_re, add_im, one_re, one_im, mul_re,
    mul_im, ofReal_re, ofReal_im, sub_re, sub_im]
  ring

theorem norm_nevanlinnaKernel_le {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) (x : ℝ) :
    ‖nevanlinnaKernel z x‖ ≤ (‖z + I‖ + ‖z - I‖) / (‖z + I‖ - ‖z - I‖) := by
  have hzim : 0 < z.im := hz
  have hlt : ‖z - I‖ < ‖z + I‖ := by
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp only [normSq_apply, sub_re, sub_im, add_re, add_im, I_re, I_im]
    nlinarith
  have hDpos : (0 : ℝ) < ‖z + I‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have hEnonneg : (0 : ℝ) ≤ ‖z - I‖ := norm_nonneg _
  set D := ‖z + I‖ with hD
  set E := ‖z - I‖ with hE
  set W := ‖(z - I) / (z + I)‖ with hW
  have hWeq : D * W = E := by
    rw [hW, norm_div, ← hD, ← hE]
    field_simp
  have hWlt : W < 1 := by nlinarith
  have hzeta : ‖(boundaryCayley x : ℂ)‖ = 1 := Circle.norm_coe _
  have hnum : ‖(boundaryCayley x : ℂ) + (z - I) / (z + I)‖ ≤ 1 + W := by
    calc ‖(boundaryCayley x : ℂ) + (z - I) / (z + I)‖
        ≤ ‖(boundaryCayley x : ℂ)‖ + W := norm_add_le _ _
      _ = 1 + W := by rw [hzeta]
  have hden : 1 - W ≤ ‖(boundaryCayley x : ℂ) - (z - I) / (z + I)‖ := by
    have := norm_sub_norm_le ((boundaryCayley x : ℂ)) ((z - I) / (z + I))
    rwa [hzeta] at this
  have hdenpos : (0 : ℝ) < ‖(boundaryCayley x : ℂ) - (z - I) / (z + I)‖ :=
    lt_of_lt_of_le (by linarith) hden
  rw [← I_mul_herglotzKernel_cayley z x hz, norm_mul, norm_I, one_mul, norm_div,
    div_le_div_iff₀ hdenpos (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_right hnum (by nlinarith : (0 : ℝ) ≤ D - E),
    mul_le_mul_of_nonneg_left hden (by nlinarith : (0 : ℝ) ≤ D + E)]

@[fun_prop]
theorem continuous_nevanlinnaKernel {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (nevanlinnaKernel z) := by
  unfold nevanlinnaKernel
  refine Continuous.div (by fun_prop) (by fun_prop) fun x h ↦ ?_
  have := congrArg im h
  simp only [sub_im, ofReal_im, zero_sub, zero_im, neg_eq_zero] at this
  exact hz this

theorem integrable_nevanlinnaKernel {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet)
    (mu : Measure ℝ) [IsFiniteMeasure mu] : Integrable (nevanlinnaKernel z) mu :=
  .of_bound (continuous_nevanlinnaKernel (ne_of_gt hz)).aestronglyMeasurable _
    (.of_forall (norm_nevanlinnaKernel_le hz))

private theorem I_mul_one_add_cayley_div_one_sub (z : ℂ)
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    I * ((1 + (z - I) / (z + I)) / (1 - (z - I) / (z + I))) = z := by
  have hzpos : 0 < z.im := hz
  have hzi : z + I ≠ 0 := by
    intro h
    have := congrArg im h
    simp only [add_im, I_im, zero_im] at this
    linarith
  field_simp [hzi, I_mul_I]
  ring

theorem I_mul_herglotzTransform_cayley_eq (mu : Measure Circle) [IsFiniteMeasure mu]
    {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    I * mu.herglotzTransform ((z - I) / (z + I)) =
      (mu.real {1} : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu.cayleyPushforward := by
  let w := (z - I) / (z + I)
  have hw : w ∈ ball (0 : ℂ) 1 := cayley_mem_ball hz
  have hcont : Continuous fun u : Circle ↦ I * (((u : ℂ) + w) / ((u : ℂ) - w)) :=
    continuous_const.mul <| (continuous_subtype_val.add continuous_const).div
      (continuous_subtype_val.sub continuous_const) fun u hu ↦ by
        have hnorm := Circle.norm_coe u
        rw [sub_eq_zero] at hu
        rw [hu] at hnorm
        exact (mem_ball_zero_iff.1 hw).ne hnorm
  rw [Measure.herglotzTransform_def, ← integral_const_mul,
    integral_circle_eq_atom_add_integral_cayleyPushforward mu _ hcont]
  simp only [w, Circle.coe_one, I_mul_herglotzKernel_cayley z _ hz]
  rw [I_mul_one_add_cayley_div_one_sub z hz]
  simp only [real_smul]

theorem exists_isFiniteMeasure_eq_nevanlinnaKernel_add {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∃ (rho : Measure ℝ) (b : ℝ), IsFiniteMeasure rho ∧ 0 ≤ b ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂rho + (F I).re := by
  obtain ⟨mu, hmu, hrep⟩ :=
    exists_isFiniteMeasure_eq_I_mul_herglotzTransform_cayley_add hF him
  let _ := hmu
  refine ⟨mu.cayleyPushforward, mu.real {1}, inferInstance, measureReal_nonneg, fun z hz ↦ ?_⟩
  rw [hrep z hz, I_mul_herglotzTransform_cayley_eq mu hz]

end TauCeti
