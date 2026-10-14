import AndersonAC.S9.PoissonInterval
import AndersonAC.S9.Operators
import AndersonAC.S9.Resolution
import AndersonAC.Boundary.PoissonBoundary
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

namespace AndersonAC.SolS9

theorem no_positive_boundary_off_spectrum {d : ℕ}
    (T : StateSpace d →L[ℂ] StateSpace d) (hT : IsSelfAdjoint T)
    (v : StateSpace d) (E : ℝ) (hE : (E : ℂ) ∉ spectrum ℂ T) :
    ¬ positiveBoundary (fun z => inner ℂ v (operatorResolvent T z v)) E := by
  have hu : IsUnit (T - (E : ℂ) • (1 : StateSpace d →L[ℂ] StateSpace d)) := by
    simpa only [neg_sub, Algebra.algebraMap_eq_smul_one] using (spectrum.notMem_iff.mp hE).neg
  have hshift : (T - (E : ℂ) • (1 : StateSpace d →L[ℂ] StateSpace d)).toLinearMap.IsSymmetric := by
    have ht := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
    intro u w
    have htw : inner ℂ (T u) w = inner ℂ u (T w) := ht u w
    change inner ℂ (T u - (E : ℂ) • u) w = inner ℂ u (T w - (E : ℂ) • w)
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    rw [htw]
    simp
  have hcancel (q : StateSpace d) :
      (T - (E : ℂ) • (1 : StateSpace d →L[ℂ] StateSpace d)) (operatorResolvent T E q) = q := by
    simpa only [operatorResolvent, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
      using congrArg (fun f : StateSpace d →L[ℂ] StateSpace d => f q)
        (Ring.mul_inverse_cancel _ hu)
  have hsym : (operatorResolvent T E).toLinearMap.IsSymmetric := by
    intro u w
    have h := hshift (operatorResolvent T E u) (operatorResolvent T E w)
    change inner ℂ ((T - (E : ℂ) • 1) (operatorResolvent T E u)) (operatorResolvent T E w) =
      inner ℂ (operatorResolvent T E u) ((T - (E : ℂ) • 1) (operatorResolvent T E w)) at h
    rw [hcancel u, hcancel w] at h
    exact h.symm
  have him : (inner ℂ v (operatorResolvent T E v)).im = 0 := by
    exact hsym.im_inner_self_apply v
  have hc : ContinuousAt (fun η : ℝ => operatorResolvent T ((E : ℂ) + η * Complex.I)) 0 := by
    have hinv := NormedRing.inverse_continuousAt hu.unit
    rw [hu.unit_spec] at hinv
    have hfun : Continuous (fun η : ℝ => T - ((E : ℂ) + η * Complex.I) •
        (1 : StateSpace d →L[ℂ] StateSpace d)) := by fun_prop
    have hi : ContinuousAt Ring.inverse ((fun η : ℝ => T - ((E : ℂ) + η * Complex.I) •
        (1 : StateSpace d →L[ℂ] StateSpace d)) 0) := by simpa using hinv
    have hh := ContinuousAt.comp
      (f := fun η : ℝ => T - ((E : ℂ) + η * Complex.I) •
        (1 : StateSpace d →L[ℂ] StateSpace d))
      (g := Ring.inverse) (x := (0 : ℝ)) hi hfun.continuousAt
    simpa only [operatorResolvent, Function.comp_def] using hh
  have hscalar : ContinuousAt (fun η : ℝ => inner ℂ v
      (operatorResolvent T ((E : ℂ) + η * Complex.I) v)) 0 :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => v) 0).inner
      (hc.clm_apply (continuousAt_const : ContinuousAt (fun _ : ℝ => v) 0))
  have hl := hscalar.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  intro hp
  obtain ⟨w, hw, hwpos⟩ := hp
  have heq : w = inner ℂ v (operatorResolvent T E v) := by
    apply tendsto_nhds_unique hw
    simpa using hl
  rw [heq, him] at hwpos
  exact lt_irrefl _ hwpos

theorem positive_boundary_spectrum {d : ℕ}
    (T : StateSpace d →L[ℂ] StateSpace d) (hT : IsSelfAdjoint T) (v : StateSpace d)
    (I : Set ℝ) (hI : IsOpen I)
    (hp : ∀ᵐ E ∂volume.restrict I,
      positiveBoundary (fun z => inner ℂ v (operatorResolvent T z v)) E) :
    I ⊆ AndersonAC.Blueprint.realSpectrum T := by
  let U := I \ AndersonAC.Blueprint.realSpectrum T
  have hclosed : IsClosed (AndersonAC.Blueprint.realSpectrum T) :=
    (spectrum.isClosed T).preimage Complex.continuous_ofReal
  have hU : IsOpen U := hI.inter hclosed.isOpen_compl
  have hnull : volume U = 0 := by
    have hall : ∀ᵐ E ∂volume, E ∉ U := by
      filter_upwards [ae_imp_of_ae_restrict hp] with E hE
      intro hEU
      exact no_positive_boundary_off_spectrum T hT v E hEU.2 (hE hEU.1)
    simpa [ae_iff] using hall
  intro E hE
  by_contra hn
  have hpos := hU.measure_pos (μ := (volume : Measure ℝ)) ⟨E, hE, hn⟩
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

theorem positive_boundary_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (I : Set ℝ) (hI : IsOpen I) (hne : I.Nonempty)
    (hp : ∀ᵐ E ∂volume.restrict I, positiveBoundary (borelTransform μ) E) :
    0 < μ I := by
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  have hr : μ.restrict I = 0 := Measure.restrict_eq_zero.mpr hzero
  have hrn : ∀ᵐ E ∂volume.restrict I, μ.rnDeriv volume E = 0 := by
    filter_upwards [ae_restrict_of_ae (Measure.rnDeriv_restrict μ volume hI.measurableSet),
      ae_restrict_of_ae (Measure.rnDeriv_zero volume), ae_restrict_mem hI.measurableSet]
      with E hE h0 hEI
    rw [hr] at hE
    simpa [hEI, h0] using hE.symm
  have hlimit := ae_restrict_of_ae (s := I)
    (AndersonAC.Boundary.im_resolventTransform_tendsto_ae μ)
  have hfalse : ∀ᵐ E ∂volume.restrict I, False := by
    filter_upwards [hp, hrn, hlimit] with E hE hRN hlim
    obtain ⟨w, hw, hwpos⟩ := hE
    have himlim := Complex.continuous_im.continuousAt.tendsto.comp hw
    have heq : w.im = 0 := by
      apply tendsto_nhds_unique himlim
      simpa only [← borelTransform_eq_resolventTransform, hRN,
        ENNReal.toReal_zero, mul_zero, Function.comp_def] using hlim
    rw [heq] at hwpos
    exact lt_irrefl _ hwpos
  have hnull : volume I = 0 := by
    simpa [ae_iff] using hfalse
  have hpos := hI.measure_pos (μ := (volume : Measure ℝ)) hne
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

end AndersonAC.SolS9
