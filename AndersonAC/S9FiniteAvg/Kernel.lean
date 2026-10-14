import AndersonAC.S9Fin.Scalar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9

lemma cauchy_interval_integral_bound (c a γ : ℝ) (hc : 0 < c) (_hγ : 0 < γ) :
    (∫ x in (-1 : ℝ)..1, γ / ((c * x + a) ^ 2 + γ ^ 2)) ≤ Real.pi / c := by
  rw [intervalIntegral.integral_comp_mul_add
    (f := fun y : ℝ => γ / (y ^ 2 + γ ^ 2)) hc.ne' a]
  have hden : (fun y : ℝ => γ / (y ^ 2 + γ ^ 2)) =
      fun y => γ / (γ ^ 2 + y ^ 2) := by
    funext y
    congr 1
    ring
  rw [hden, integral_div_sq_add_sq]
  have hlow : -(Real.pi / 2) < Real.arctan ((c * -1 + a) / γ) :=
    Real.neg_pi_div_two_lt_arctan _
  have hupp : Real.arctan ((c * 1 + a) / γ) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hdiff : Real.arctan ((c * 1 + a) / γ) -
      Real.arctan ((c * -1 + a) / γ) ≤ Real.pi := by
    linarith
  have hcpos : 0 ≤ c⁻¹ := (inv_pos.mpr hc).le
  rw [smul_eq_mul]
  calc
    c⁻¹ * (Real.arctan ((c * 1 + a) / γ) -
        Real.arctan ((c * -1 + a) / γ)) ≤ c⁻¹ * Real.pi :=
      mul_le_mul_of_nonneg_left hdiff hcpos
    _ = Real.pi / c := by rw [div_eq_mul_inv]; ring

lemma uniformSite_cauchy_integral_bound (c a γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    (∫ s : SingleSite, γ / ((c * (s : ℝ) + a) ^ 2 + γ ^ 2) ∂uniformSite) ≤
      Real.pi / (2 * c) := by
  let f : ℝ → ℝ := fun x => γ / ((c * x + a) ^ 2 + γ ^ 2)
  have hfcont : Continuous f := by
    dsimp [f]
    have hd : ∀ x : ℝ, (c * x + a) ^ 2 + γ ^ 2 ≠ 0 := by
      intro x
      positivity
    exact continuous_const.div (by fun_prop) hd
  have hfmap : AEStronglyMeasurable f
      (uniformSite.map (fun s : SingleSite => (s : ℝ))) :=
    hfcont.aestronglyMeasurable
  have hrestrict : volume.restrict (Set.Icc (-1 : ℝ) 1) =
      volume.restrict (Set.Ioc (-1 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  calc
    (∫ s : SingleSite, f s ∂uniformSite) =
        ∫ x : ℝ, f x ∂uniformSite.map (fun s : SingleSite => (s : ℝ)) := by
      symm
      exact MeasureTheory.integral_map measurable_subtype_coe.aemeasurable hfmap
    _ = ((2 : ENNReal)⁻¹).toReal * (∫ x : ℝ, f x ∂volume.restrict (Set.Icc (-1 : ℝ) 1)) := by
      rw [uniformSite_map_val, MeasureTheory.integral_smul_measure, smul_eq_mul]
    _ = (1 / 2) * (∫ x in (-1 : ℝ)..1, f x) := by
      rw [show ((2 : ENNReal)⁻¹).toReal = (1 / 2 : ℝ) by norm_num,
        show volume.restrict (Set.Icc (-1 : ℝ) 1) =
          volume.restrict (Set.Ioc (-1 : ℝ) 1) from hrestrict,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    _ ≤ (1 / 2) * (Real.pi / c) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact cauchy_interval_integral_bound c a γ hc hγ
    _ = Real.pi / (2 * c) := by field_simp

end AndersonAC.SolS9
