import AndersonAC.S9Fin.Wegner
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Thickening

-- Poisson domination for finite-volume spectral measures.
noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace AndersonAC.SolS9Pois

def poissonKernel (η E t : ℝ) : ℝ := η / ((t - E) ^ 2 + η ^ 2)

lemma poissonKernel_swap (η E t : ℝ) : poissonKernel η E t = poissonKernel η t E := by
  unfold poissonKernel
  congr 1
  ring

lemma poissonKernel_norm_le_inv (η E t : ℝ) (hη : 0 < η) :
    ‖poissonKernel η E t‖ ≤ η⁻¹ := by
  unfold poissonKernel
  have hden : 0 < (t - E) ^ 2 + η ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hη.le hden.le)]
  apply (div_le_iff₀ hden).2
  rw [inv_mul_eq_div, le_div_iff₀ hη]
  nlinarith [sq_nonneg (t - E)]

lemma integrable_poissonKernel (ν : Measure ℝ) [IsFiniteMeasure ν]
    (η E : ℝ) (hη : 0 < η) : Integrable (fun t => poissonKernel η E t) ν := by
  have hcont : Continuous (fun t : ℝ => poissonKernel η E t) := by
    have hden : Continuous (fun t : ℝ => (t - E) ^ 2 + η ^ 2) := by fun_prop
    have hden_ne : ∀ t : ℝ, (t - E) ^ 2 + η ^ 2 ≠ 0 := by
      intro t
      positivity
    change Continuous (fun t : ℝ => η * (((t - E) ^ 2 + η ^ 2)⁻¹))
    exact continuous_const.mul (hden.inv₀ hden_ne)
  refine (integrable_const (η⁻¹ : ℝ)).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [] with t
  exact poissonKernel_norm_le_inv η E t hη

lemma borelTransform_im_eq_poissonKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E η : ℝ) (hη : 0 < η) :
    (AndersonAC.Blueprint.borelTransform μ ((E : ℂ) + η * Complex.I)).im =
      ∫ t : ℝ, poissonKernel η E t ∂μ := by
  let z : ℂ := (E : ℂ) + η * Complex.I
  have hz_im (t : ℝ) : ((t : ℂ) - z).im = -η := by
    simp [z]
  have hz_ne (t : ℝ) : (t : ℂ) - z ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    rw [hz_im] at h'
    have hz0 : -η = 0 := by simpa using h'
    linarith
  have hcont : Continuous (fun t : ℝ => ((t : ℂ) - z)⁻¹) :=
    (RCLike.continuous_ofReal.sub continuous_const).inv₀ hz_ne
  have hnorm (t : ℝ) : η ≤ ‖(t : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((t : ℂ) - z)
    rw [hz_im, abs_neg, abs_of_pos hη] at h
    exact h
  have hbound (t : ℝ) : ‖((t : ℂ) - z)⁻¹‖ ≤ η⁻¹ := by
    simpa only [norm_inv, one_div] using one_div_le_one_div_of_le hη (hnorm t)
  have hInt : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) μ := by
    refine (integrable_const (η⁻¹ : ℝ)).mono' hcont.aestronglyMeasurable ?_
    filter_upwards [] with t
    exact hbound t
  rw [AndersonAC.Blueprint.borelTransform]
  change Complex.imCLM (∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ) = _
  rw [← Complex.imCLM.integral_comp_comm hInt]
  apply integral_congr_ae
  filter_upwards [] with t
  change (((t : ℂ) - z)⁻¹).im = _
  have hnormsq : Complex.normSq ((t : ℂ) - z) = (t - E) ^ 2 + η ^ 2 := by
    have hz : (t : ℂ) - z = ((t - E : ℝ) : ℂ) + (-η : ℝ) * Complex.I := by
      simp [z]
      push_cast
      ring
    rw [hz, Complex.normSq_add_mul_I]
    ring
  rw [Complex.inv_im, hz_im, hnormsq]
  simp [poissonKernel, div_eq_mul_inv]
  <;> ring

lemma integral_poissonKernel_interval (t η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∫ x : ℝ in t - δ..t + δ, poissonKernel η t x =
      2 * Real.arctan (δ / η) := by
  unfold poissonKernel
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => η / (x ^ 2 + η ^ 2)) t]
  simp only [sub_sub_cancel_left, add_sub_cancel_left]
  have hi := integral_div_sq_add_sq (a := -δ) (b := δ) (c := η)
  calc
    _ = Real.arctan (δ / η) - Real.arctan ((-δ) / η) := by simpa [add_comm] using hi
    _ = 2 * Real.arctan (δ / η) := by rw [neg_div, Real.arctan_neg]; ring

lemma compact_poisson_height_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C η δ : ℝ) (hC : 0 ≤ C) (hη : 0 < η) (hδ : 0 < δ)
    (hbound : ∀ E : ℝ, ∫ t : ℝ, poissonKernel η E t ∂μ ≤ Real.pi * C)
    (K U : Set ℝ) (hK : IsCompact K)
    (hthick : Metric.cthickening δ K ⊆ U) (hUfin : volume U < ∞) :
    (2 * Real.arctan (δ / η)) * μ.real K ≤
      Real.pi * C * volume.real U := by
  haveI : Fact (volume U < ∞) := ⟨hUfin⟩
  let f : ℝ × ℝ → ℝ := fun p => poissonKernel η p.2 p.1
  have hfcont : Continuous f := by
    have hden : Continuous (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2 + η ^ 2) := by fun_prop
    have hden_ne : ∀ p : ℝ × ℝ, (p.1 - p.2) ^ 2 + η ^ 2 ≠ 0 := by
      intro p
      positivity
    change Continuous (fun p : ℝ × ℝ => η * (((p.1 - p.2) ^ 2 + η ^ 2)⁻¹))
    exact continuous_const.mul (hden.inv₀ hden_ne)
  have hfint : Integrable f ((volume.restrict U).prod μ) := by
    refine (integrable_const (η⁻¹ : ℝ)).mono' hfcont.aestronglyMeasurable ?_
    filter_upwards [] with p
    exact poissonKernel_norm_le_inv η p.2 p.1 hη
  have houterInt : Integrable (fun E => ∫ t, f (E, t) ∂μ) (volume.restrict U) :=
    hfint.integral_prod_left
  have hinnerInt : Integrable (fun t => ∫ E, f (E, t) ∂volume.restrict U) μ :=
    hfint.integral_prod_right
  have hupper :
      ∫ E, (∫ t, f (E, t) ∂μ) ∂volume.restrict U ≤
        Real.pi * C * volume.real U := by
    calc
      ∫ E, (∫ t, f (E, t) ∂μ) ∂volume.restrict U ≤
          ∫ E, (Real.pi * C) ∂volume.restrict U := by
        apply integral_mono_ae houterInt (integrable_const _)
        filter_upwards [] with E
        change (∫ t, poissonKernel η t E ∂μ) ≤ Real.pi * C
        calc
          ∫ t, poissonKernel η t E ∂μ = ∫ t, poissonKernel η E t ∂μ := by
            apply integral_congr_ae
            exact Eventually.of_forall fun t => (poissonKernel_swap η t E)
          _ ≤ Real.pi * C := hbound E
      _ = Real.pi * C * volume.real U := by
        simp [integral_const, smul_eq_mul, Measure.restrict_apply, mul_comm]
  have hswap :
      ∫ E, (∫ t, f (E, t) ∂μ) ∂volume.restrict U =
        ∫ t, (∫ E, f (E, t) ∂volume.restrict U) ∂μ :=
    integral_integral_swap hfint
  have hlocal : ∀ t ∈ K,
      2 * Real.arctan (δ / η) ≤ ∫ E, f (E, t) ∂volume.restrict U := by
    intro t ht
    have hinterval : Set.Ioc (t - δ) (t + δ) ⊆ U := by
      intro x hx
      apply hthick (Metric.mem_cthickening_of_dist_le x t δ K ht ?_)
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2]
    have hsubsetAE : Set.Ioc (t - δ) (t + δ) ≤ᵐ[volume] U :=
      Eventually.of_forall fun x hx => hinterval hx
    have hnonneg : 0 ≤ᵐ[volume.restrict U] (fun x : ℝ => poissonKernel η t x) :=
      Eventually.of_forall fun x => div_nonneg hη.le (by positivity)
    have hmono :
        (∫ x in Set.Ioc (t - δ) (t + δ), poissonKernel η t x ∂volume) ≤
          ∫ x in U, poissonKernel η t x ∂volume := by
      apply setIntegral_mono_set (integrable_poissonKernel (volume.restrict U) η t hη)
      · exact hnonneg
      · exact hsubsetAE
    have hformula :
        (∫ x in Set.Ioc (t - δ) (t + δ), poissonKernel η t x ∂volume) =
          2 * Real.arctan (δ / η) := by
      have h := integral_poissonKernel_interval t η δ hη hδ
      rw [intervalIntegral.integral_of_le (by linarith)] at h
      exact h
    calc
      2 * Real.arctan (δ / η) =
          ∫ x in Set.Ioc (t - δ) (t + δ), poissonKernel η t x ∂volume := hformula.symm
      _ ≤ ∫ x in U, poissonKernel η t x ∂volume := hmono
      _ = ∫ E, f (E, t) ∂volume.restrict U := rfl
  have hnonnegInner : 0 ≤ᵐ[μ] (fun t => ∫ E, f (E, t) ∂volume.restrict U) := by
    filter_upwards [] with t
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun E => div_nonneg hη.le (by positivity)
  haveI : Fact (μ K < ∞) := ⟨measure_lt_top μ K⟩
  have hlocalAE :
      (fun _ : ℝ => 2 * Real.arctan (δ / η)) ≤ᵐ[μ.restrict K]
        (fun t => ∫ E, f (E, t) ∂volume.restrict U) := by
    apply (ae_restrict_iff' hK.measurableSet).2
    filter_upwards [] with t ht
    exact hlocal t ht
  have htotal :
      (2 * Real.arctan (δ / η)) * μ.real K ≤
        ∫ t, (∫ E, f (E, t) ∂volume.restrict U) ∂μ := by
    calc
      (2 * Real.arctan (δ / η)) * μ.real K =
          ∫ t, (2 * Real.arctan (δ / η)) ∂μ.restrict K := by
        simp [integral_const, smul_eq_mul, Measure.restrict_apply, mul_comm]
      _ ≤ ∫ t, (∫ E, f (E, t) ∂volume.restrict U) ∂μ.restrict K :=
        integral_mono_ae (integrable_const _) (hinnerInt.mono_measure Measure.restrict_le_self)
          hlocalAE
      _ ≤ ∫ t, (∫ E, f (E, t) ∂volume.restrict U) ∂μ :=
        integral_mono_measure Measure.restrict_le_self hnonnegInner hinnerInt
  calc
    (2 * Real.arctan (δ / η)) * μ.real K ≤
        ∫ t, (∫ E, f (E, t) ∂volume.restrict U) ∂μ := htotal
    _ = ∫ E, (∫ t, f (E, t) ∂μ) ∂volume.restrict U := hswap.symm
    _ ≤ Real.pi * C * volume.real U := hupper

lemma compact_poisson_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hpoisson : ∀ E η : ℝ, 0 < η →
      (AndersonAC.Blueprint.borelTransform μ ((E : ℂ) + η * Complex.I)).im ≤ Real.pi * C)
    (K U : Set ℝ) (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U)
    (hUfin : volume U < ∞) : μ.real K ≤ C * volume.real U := by
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have harctan :
      Tendsto (fun n : ℕ => Real.arctan ((n : ℝ) + 1)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hn
  have hlim :
      Tendsto (fun n : ℕ => (2 * Real.arctan ((n : ℝ) + 1)) * μ.real K) atTop
        (𝓝 (Real.pi * μ.real K)) := by
    have hmul :
        Tendsto (fun n : ℕ => (2 * Real.arctan ((n : ℝ) + 1)) * μ.real K) atTop
          (𝓝 ((2 * (Real.pi / 2)) * μ.real K)) :=
      (tendsto_const_nhds.mul harctan).mul tendsto_const_nhds
    convert hmul using 1 <;> ring
  have hseq : ∀ n : ℕ,
      (2 * Real.arctan ((n : ℝ) + 1)) * μ.real K ≤ Real.pi * C * volume.real U := by
    intro n
    let η : ℝ := δ / ((n : ℝ) + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    have hheight :
        (2 * Real.arctan (δ / η)) * μ.real K ≤ Real.pi * C * volume.real U := by
      apply compact_poisson_height_bound μ C η δ hC hη hδ
      · intro E
        rw [← borelTransform_im_eq_poissonKernel μ E η hη]
        exact hpoisson E η hη
      · exact hK
      · exact hthick
      · exact hUfin
    have hratio : δ / η = (n : ℝ) + 1 := by
      dsimp [η]
      field_simp
    simpa [hratio] using hheight
  have hpi : Real.pi * μ.real K ≤ Real.pi * (C * volume.real U) := by
    apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    exact Eventually.of_forall fun n => by simpa [mul_assoc] using hseq n
  exact (mul_le_mul_iff_of_pos_left Real.pi_pos).1 (by simpa [mul_assoc] using hpi)

lemma compact_measure_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hpoisson : ∀ E η : ℝ, 0 < η →
      (AndersonAC.Blueprint.borelTransform μ ((E : ℂ) + η * Complex.I)).im ≤ Real.pi * C)
    (K : Set ℝ) (hK : IsCompact K) : μ K ≤ ENNReal.ofReal C * volume K := by
  have hKvolfin : volume K < ∞ := IsCompact.measure_lt_top (μ := volume) hK
  have hbasefin : ENNReal.ofReal C * volume K < ∞ := by finiteness
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let e : ℝ := (ε : ℝ) / (C + 1)
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hKlt : volume K < volume K + ENNReal.ofReal e :=
    ENNReal.lt_add_right hKvolfin.ne (ENNReal.ofReal_pos.mpr he).ne'
  obtain ⟨U, hKU, hUopen, hUmeasure⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := volume) K (volume K + ENNReal.ofReal e) hKlt
  have hUfin : volume U < ∞ := by
    calc
      volume U < volume K + ENNReal.ofReal e := hUmeasure
      _ < ∞ := ENNReal.add_lt_top.mpr
        ⟨hKvolfin, lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top⟩
  have hreal : μ.real K ≤ C * volume.real U :=
    compact_poisson_bound μ C hC hpoisson K U hK hKU hUopen hUfin
  have hKle : μ K ≤ ENNReal.ofReal C * volume U := by
    have hCfin : ENNReal.ofReal C < ∞ := lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
    have htargetne : ENNReal.ofReal C * volume U ≠ ∞ :=
      (ENNReal.mul_lt_top hCfin hUfin).ne
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ K) htargetne).1
    rw [ENNReal.toReal_ofReal_mul C (volume U) hC]
    simpa only [measureReal_def] using hreal
  have hCplus : 0 < C + 1 := by linarith
  have hCe : C * e ≤ (ε : ℝ) := by
    dsimp [e]
    field_simp [ne_of_gt hCplus]
    nlinarith [hC, hε]
  have hprod :
      ENNReal.ofReal C * volume U ≤ ENNReal.ofReal C * volume K + (ε : ℝ≥0∞) := by
    calc
      ENNReal.ofReal C * volume U ≤
          ENNReal.ofReal C * (volume K + ENNReal.ofReal e) :=
        by gcongr
      _ = ENNReal.ofReal C * volume K + ENNReal.ofReal (C * e) := by
        rw [mul_add, ← ENNReal.ofReal_mul hC]
      _ ≤ ENNReal.ofReal C * volume K + (ε : ℝ≥0∞) := by
        exact add_le_add_right (by simpa using ENNReal.ofReal_le_ofReal hCe) _
  exact hKle.trans hprod

end AndersonAC.SolS9Pois

namespace AndersonAC.SolS9

theorem finitePoissonDomination_proof : FinitePoissonDominationInput := by
  intro μ hμ C hC hpoisson
  letI : IsFiniteMeasure μ := hμ
  apply Measure.le_iff.2
  intro s hs
  rw [hs.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top μ s)]
  apply iSup_le fun K => iSup_le fun hKs => iSup_le fun hK => ?_
  calc
    μ K ≤ ENNReal.ofReal C * volume K :=
      AndersonAC.SolS9Pois.compact_measure_bound μ C hC hpoisson K hK
    _ ≤ (ENNReal.ofReal C • volume) s := by
      rw [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (measure_mono hKs) (by positivity)

end AndersonAC.SolS9
