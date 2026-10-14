import OAI.MathematicalPhysics.Anderson.Certificates
import AndersonAC.Spectral.Projections
import AndersonAC.Spectral.CountableAdditivity

open MeasureTheory
open scoped InnerProductSpace ENNReal

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace AndersonAC.Spectral

private theorem spectralProjection_eq_proj
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (B : Set ℝ) (hB : MeasurableSet B) :
    spectralProjection T hT B = (TauCeti.BorelCalculus.boundedPVM hT).proj B hB := by
  classical
  simp [spectralProjection, hB]

private theorem stateSpace_nontrivial (d : ℕ) : Nontrivial (OAI.Anderson.StateSpace d) := by
  let x : OAI.Anderson.Site d := fun _ => 0
  let v : OAI.Anderson.StateSpace d :=
    lp.single (E := fun _ : OAI.Anderson.Site d => ℂ) 2 x 1
  have hv : v ≠ 0 := by
    intro h
    have hval := congrArg (fun f : OAI.Anderson.StateSpace d => f x) h
    have : (1 : ℂ) = 0 := by simpa [v, x] using hval
    exact one_ne_zero this
  exact ⟨⟨v, 0, hv⟩⟩

private theorem reCoord_mem_Icc_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} [NormOneClass (H →L[ℂ] H)] (w : spectrum ℂ T) :
    TauCeti.BorelCalculus.reCoord w ∈ Set.Icc (-‖T‖) ‖T‖ := by
  rw [TauCeti.BorelCalculus.reCoord_apply]
  have hnorm : ‖(w : ℂ)‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem w.property
  have habs : |(w : ℂ).re| ≤ ‖T‖ :=
    (Complex.abs_re_le_norm _).trans hnorm
  exact abs_le.mp habs

private theorem reCoord_preimage_Icc_compl_empty
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} [NormOneClass (H →L[ℂ] H)] :
    TauCeti.BorelCalculus.reCoord (T := T) ⁻¹' (Set.Icc (-‖T‖) ‖T‖)ᶜ = ∅ := by
  ext w
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false,
    iff_false]
  exact not_not_intro (reCoord_mem_Icc_norm w)

/-- The scalar spectral measure associated with a bounded self-adjoint operator. -/
noncomputable def spectralVectorMeasure
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (v : H) : Measure ℝ :=
  (TauCeti.BorelCalculus.boundedPVM hT).diag v

/-- The scalar spectral measure is the pushforward of the diagonal measure on the operator spectrum. -/
theorem spectralVectorMeasure_eq_map
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (v : H) :
    spectralVectorMeasure hT v = Measure.map (TauCeti.BorelCalculus.reCoord (T := T))
      (TauCeti.BorelCalculus.diagMeasure hT.isStarNormal v) :=
  TauCeti.BorelCalculus.boundedPVM_diag hT v

/-- The OAI spectral-resolution package for the bounded self-adjoint operator `T`.

Its vector measures are the diagonal measures of the LeanPool PVM, pushed forward
from the operator spectrum by the real-part coordinate. -/
noncomputable def spectralResolution {d : ℕ}
    (T : OAI.Anderson.StateSpace d →L[ℂ] OAI.Anderson.StateSpace d)
    (hT : IsSelfAdjoint T) : OAI.Anderson.SpectralResolution T where
  projection := spectralProjection T hT
  projection_empty := by
    rw [spectralProjection_eq_proj T hT ∅ MeasurableSet.empty]
    exact (TauCeti.BorelCalculus.boundedPVM hT).proj_empty
  projection_univ := by
    rw [spectralProjection_eq_proj T hT Set.univ MeasurableSet.univ]
    exact (TauCeti.BorelCalculus.boundedPVM hT).proj_univ
  projection_selfAdjoint := by
    intro B hB
    rw [spectralProjection_eq_proj T hT B hB]
    exact (TauCeti.BorelCalculus.boundedPVM hT).isSelfAdjoint_proj B hB
  projection_inter := by
    intro B C hB hC
    rw [spectralProjection_eq_proj T hT (B ∩ C) (hB.inter hC),
      spectralProjection_eq_proj T hT B hB, spectralProjection_eq_proj T hT C hC]
    exact ((TauCeti.BorelCalculus.boundedPVM hT).proj_inter B C hB hC).symm
  projection_iUnion := by
    intro B hB hdisj v
    have hterm (n : ℕ) : spectralProjection T hT (B n) =
        (TauCeti.BorelCalculus.boundedPVM hT).proj (B n) (hB n) :=
      spectralProjection_eq_proj T hT (B n) (hB n)
    have hunion : spectralProjection T hT (⋃ n, B n) =
        (TauCeti.BorelCalculus.boundedPVM hT).proj (⋃ n, B n) (MeasurableSet.iUnion hB) :=
      spectralProjection_eq_proj T hT (⋃ n, B n) (MeasurableSet.iUnion hB)
    simpa only [hterm, hunion] using
      proj_iUnion_hasSum (TauCeti.BorelCalculus.boundedPVM hT) B hB hdisj v
  vectorMeasure := spectralVectorMeasure hT
  finite_vectorMeasure := by
    intro v
    exact (TauCeti.BorelCalculus.boundedPVM hT).diag_finite v
  vectorMeasure_apply := by
    intro v B hB
    rw [spectralVectorMeasure, spectralProjection_eq_proj T hT B hB]
    calc
      ((TauCeti.BorelCalculus.boundedPVM hT).diag v) B =
          ENNReal.ofReal (((TauCeti.BorelCalculus.boundedPVM hT).diag v B).toReal) := by
        exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal (‖(TauCeti.BorelCalculus.boundedPVM hT).proj B hB v‖ ^ 2) := by
        rw [(TauCeti.BorelCalculus.boundedPVM hT).norm_sq_proj_apply B hB v]
  vectorMeasure_supported := by
    letI : Nontrivial (OAI.Anderson.StateSpace d) := stateSpace_nontrivial d
    intro v
    change ((TauCeti.BorelCalculus.boundedPVM hT).diag v)
      (Set.Icc (-‖T‖) ‖T‖)ᶜ = 0
    rw [TauCeti.BorelCalculus.boundedPVM_diag]
    rw [Measure.map_apply TauCeti.BorelCalculus.measurable_reCoord
      measurableSet_Icc.compl]
    rw [reCoord_preimage_Icc_compl_empty (T := T), measure_empty]
  vectorMeasure_moments := by
    intro v n
    rw [spectralVectorMeasure_eq_map hT]
    let r : C(spectrum ℂ T, ℝ) :=
      ⟨fun w => (w : ℂ).re, Complex.continuous_re.comp continuous_subtype_val⟩
    let g : C(spectrum ℂ T, ℝ) := r ^ n
    have hsymbol : TauCeti.BorelCalculus.ofRealLM g =
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ T)) ^ n := by
      ext w
      change (((w : ℂ).re ^ n : ℝ) : ℂ) = (w : ℂ) ^ n
      push_cast
      rw [← hT.mem_spectrum_eq_re w.property]
    have hcfc : cfcHom hT.isStarNormal (TauCeti.BorelCalculus.ofRealLM g) = T ^ n := by
      calc
        cfcHom hT.isStarNormal (TauCeti.BorelCalculus.ofRealLM g) =
            cfcHom hT.isStarNormal (((ContinuousMap.id ℂ).restrict (spectrum ℂ T)) ^ n) := by
          rw [hsymbol]
        _ = (cfcHom hT.isStarNormal ((ContinuousMap.id ℂ).restrict (spectrum ℂ T))) ^ n :=
          map_pow _ _ _
        _ = T ^ n := by rw [cfcHom_id]
    calc
      ∫ t : ℝ, t ^ n ∂Measure.map (TauCeti.BorelCalculus.reCoord (T := T))
          (TauCeti.BorelCalculus.diagMeasure hT.isStarNormal v) =
          ∫ w, TauCeti.BorelCalculus.reCoord w ^ n
            ∂TauCeti.BorelCalculus.diagMeasure hT.isStarNormal v :=
        MeasureTheory.integral_map TauCeti.BorelCalculus.measurable_reCoord.aemeasurable
          (f := fun t : ℝ => t ^ n)
          ((continuous_id.pow n).aestronglyMeasurable)
      _ = ∫ w, g w ∂TauCeti.BorelCalculus.diagMeasure hT.isStarNormal v := by
            rfl
      _ = (⟪v, cfcHom hT.isStarNormal (TauCeti.BorelCalculus.ofRealLM g) v⟫_ℂ).re :=
        TauCeti.BorelCalculus.integral_diagMeasure_ofReal hT.isStarNormal v g
      _ = (⟪v, (T ^ n) v⟫_ℂ).re := by rw [hcfc]

/-- The absolutely continuous spectral subspace of `T`, bundled as the OAI
spectral-resolution submodule. -/
noncomputable def absolutelyContinuousSubspace {d : ℕ}
    (T : OAI.Anderson.StateSpace d →L[ℂ] OAI.Anderson.StateSpace d)
    (hT : IsSelfAdjoint T) : Submodule ℂ (OAI.Anderson.StateSpace d) :=
  (spectralResolution T hT).acSubspace

end AndersonAC.Spectral
