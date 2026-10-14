import AndersonAC.Spectral.Resolution
import AndersonAC.Blueprint.SpectralInputs

open MeasureTheory OAI.Anderson
open scoped InnerProductSpace ENNReal lp

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace AndersonAC.LunaPvm

/-- The continuous scalar symbol for the resolvent in the upper half-plane. -/
noncomputable def resolventSymbol {d : ℕ}
    (T : AndersonAC.Blueprint.Operator d) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) : C(spectrum ℂ T, ℂ) :=
  ⟨fun w => ((w : ℂ) - z)⁻¹,
    (continuous_subtype_val.sub continuous_const).inv₀ (by
      intro w hzero
      have hwz : (w : ℂ) = z := sub_eq_zero.mp hzero
      have hzreal : z = ((w : ℂ).re : ℂ) :=
        hwz.symm.trans (hT.mem_spectrum_eq_re w.property)
      have him : z.im = 0 := by rw [hzreal]; simp
      exact (ne_of_gt hz) him)⟩

/-- The continuous functional calculus of the scalar resolvent symbol is the
operator inverse used by the spectral interface. -/
theorem cfc_resolvent_eq_greenOperator {d : ℕ}
    (T : AndersonAC.Blueprint.Operator d) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : 0 < z.im) :
    cfcHom hT.isStarNormal (resolventSymbol T hT z hz) =
      AndersonAC.Blueprint.greenOperator T z := by
  let coord : C(spectrum ℂ T, ℂ) :=
    (ContinuousMap.id ℂ).restrict (spectrum ℂ T)
  let q : C(spectrum ℂ T, ℂ) := coord - z • (1 : C(spectrum ℂ T, ℂ))
  let f : C(spectrum ℂ T, ℂ) := resolventSymbol T hT z hz
  have hq_ne (w : spectrum ℂ T) : q w ≠ 0 := by
    intro hzero
    have hwz : (w : ℂ) = z := sub_eq_zero.mp (by simpa [q, coord] using hzero)
    have hzreal : z = ((w : ℂ).re : ℂ) :=
      hwz.symm.trans (hT.mem_spectrum_eq_re w.property)
    have him : z.im = 0 := by rw [hzreal]; simp
    exact (ne_of_gt hz) him
  have hqval (w : spectrum ℂ T) : q w = (w : ℂ) - z := by
    simp [q, coord]
  have hfval (w : spectrum ℂ T) : f w = ((w : ℂ) - z)⁻¹ := rfl
  have hqf : q * f = 1 := by
    ext w
    change q w * f w = 1
    have hne : (w : ℂ) - z ≠ 0 := by
      intro hzero
      apply hq_ne w
      rw [hqval]
      exact hzero
    rw [hqval, hfval]
    exact mul_inv_cancel₀ hne
  have hfq : f * q = 1 := by
    ext w
    change f w * q w = 1
    have hne : (w : ℂ) - z ≠ 0 := by
      intro hzero
      apply hq_ne w
      rw [hqval]
      exact hzero
    rw [hfval, hqval]
    exact inv_mul_cancel₀ hne
  have hcfc_q : cfcHom hT.isStarNormal q =
      T - z • (1 : AndersonAC.Blueprint.Operator d) := by
    change cfcHom hT.isStarNormal
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ T) -
          z • (1 : C(spectrum ℂ T, ℂ))) = _
    rw [map_sub, map_smul, map_one, cfcHom_id]
  have hqf_op : cfcHom hT.isStarNormal q * cfcHom hT.isStarNormal f = 1 := by
    calc
      cfcHom hT.isStarNormal q * cfcHom hT.isStarNormal f =
          cfcHom hT.isStarNormal (q * f) := (map_mul _ _ _).symm
      _ = cfcHom hT.isStarNormal 1 := by rw [hqf]
      _ = 1 := map_one _
  have hfq_op : cfcHom hT.isStarNormal f * cfcHom hT.isStarNormal q = 1 := by
    calc
      cfcHom hT.isStarNormal f * cfcHom hT.isStarNormal q =
          cfcHom hT.isStarNormal (f * q) := (map_mul _ _ _).symm
      _ = cfcHom hT.isStarNormal 1 := by rw [hfq]
      _ = 1 := map_one _
  let u : (AndersonAC.Blueprint.Operator d)ˣ :=
    ⟨cfcHom hT.isStarNormal q, cfcHom hT.isStarNormal f, hqf_op, hfq_op⟩
  have hinv : Ring.inverse (cfcHom hT.isStarNormal q) =
      cfcHom hT.isStarNormal f := by
    calc
      Ring.inverse (cfcHom hT.isStarNormal q) =
          Ring.inverse (u : AndersonAC.Blueprint.Operator d) := rfl
      _ = ((u⁻¹ : (AndersonAC.Blueprint.Operator d)ˣ) : AndersonAC.Blueprint.Operator d) :=
        Ring.inverse_unit u
      _ = cfcHom hT.isStarNormal f := rfl
  change cfcHom hT.isStarNormal f =
    Ring.inverse (T - z • (1 : AndersonAC.Blueprint.Operator d))
  calc
    cfcHom hT.isStarNormal f = Ring.inverse (cfcHom hT.isStarNormal q) := hinv.symm
    _ = Ring.inverse (T - z • (1 : AndersonAC.Blueprint.Operator d)) := by rw [hcfc_q]

/-- The scalar resolvent transform of the constructed spectral measure agrees
with the diagonal matrix element of `(T-z)⁻¹` in the upper half-plane. -/
theorem spectralResolution_resolvent_eq {d : ℕ}
    (T : AndersonAC.Blueprint.Operator d) (hT : IsSelfAdjoint T)
    (v : StateSpace d) (z : ℂ) (hz : 0 < z.im) :
    inner ℂ v (AndersonAC.Blueprint.greenOperator T z v) =
      AndersonAC.Blueprint.borelTransform
        ((AndersonAC.Spectral.spectralResolution T hT).vectorMeasure v) z := by
  change inner ℂ v (AndersonAC.Blueprint.greenOperator T z v) =
    ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂AndersonAC.Spectral.spectralVectorMeasure hT v
  rw [AndersonAC.Spectral.spectralVectorMeasure_eq_map hT v]
  let μ := TauCeti.BorelCalculus.diagMeasure hT.isStarNormal v
  have hdenom (t : ℝ) : (t : ℂ) - z ≠ 0 := by
    intro ht
    have hzreal : z = (t : ℂ) := (sub_eq_zero.mp ht).symm
    have him : z.im = 0 := by rw [hzreal]; simp
    exact (ne_of_gt hz) him
  have hkernel : Continuous (fun t : ℝ => ((t : ℂ) - z)⁻¹) :=
    (Complex.continuous_ofReal.sub continuous_const).inv₀ hdenom
  have hmap_integral :
      ∫ t : ℝ, ((t : ℂ) - z)⁻¹
        ∂Measure.map (TauCeti.BorelCalculus.reCoord (T := T)) μ =
      ∫ w, (((TauCeti.BorelCalculus.reCoord (T := T) w : ℝ) : ℂ) - z)⁻¹ ∂μ :=
    MeasureTheory.integral_map TauCeti.BorelCalculus.measurable_reCoord.aemeasurable
      hkernel.aestronglyMeasurable
  let f : C(spectrum ℂ T, ℂ) := resolventSymbol T hT z hz
  have hgreen : cfcHom hT.isStarNormal f =
      AndersonAC.Blueprint.greenOperator T z :=
    cfc_resolvent_eq_greenOperator T hT z hz
  have hreal (w : spectrum ℂ T) :
      ((TauCeti.BorelCalculus.reCoord (T := T) w : ℝ) : ℂ) = (w : ℂ) := by
    simpa only [TauCeti.BorelCalculus.reCoord_apply] using
      (hT.mem_spectrum_eq_re w.property).symm
  have hpoint (w : spectrum ℂ T) :
      f w = (((TauCeti.BorelCalculus.reCoord (T := T) w : ℝ) : ℂ) - z)⁻¹ := by
    calc
      f w = ((w : ℂ) - z)⁻¹ := by rfl
      _ = (((TauCeti.BorelCalculus.reCoord (T := T) w : ℝ) : ℂ) - z)⁻¹ :=
        congrArg (fun x : ℂ => (x - z)⁻¹) (hreal w).symm
  have hdiag_integral :
      ∫ w, f w ∂μ =
        ∫ w, (((TauCeti.BorelCalculus.reCoord (T := T) w : ℝ) : ℂ) - z)⁻¹ ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with w
    exact hpoint w
  calc
    inner ℂ v (AndersonAC.Blueprint.greenOperator T z v) = ∫ w, f w ∂μ := by
      rw [← hgreen]
      exact (TauCeti.BorelCalculus.integral_diagMeasure hT.isStarNormal v f).symm
    _ = ∫ w, (((TauCeti.BorelCalculus.reCoord (T := T) w : ℝ) : ℂ) - z)⁻¹ ∂μ :=
      hdiag_integral
    _ = ∫ t : ℝ, ((t : ℂ) - z)⁻¹
        ∂Measure.map (TauCeti.BorelCalculus.reCoord (T := T)) μ := hmap_integral.symm

end AndersonAC.LunaPvm

namespace AndersonAC.Blueprint.Packages

/-- The spectral package: every bounded self-adjoint operator has a constructed OAI resolution
whose scalar resolvent transform has the standard sign convention. -/
theorem spectral : AndersonAC.Blueprint.SpectralInput := by
  intro d T hT
  refine ⟨{ spectral := AndersonAC.Spectral.spectralResolution T hT, resolvent_eq := ?_ }⟩
  intro v z hz
  exact AndersonAC.LunaPvm.spectralResolution_resolvent_eq T hT v z hz

end AndersonAC.Blueprint.Packages
