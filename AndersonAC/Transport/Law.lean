import AndersonAC.Blueprint.Transport

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal

namespace AndersonAC.LunaTransport

/-- Per-site affine map from normalized coordinates to `[a,b]`. -/
def siteAffine (a b : ℝ) (v : SingleSite) : ℝ :=
  Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * (v : ℝ)

lemma coupling_pos {a b : ℝ} (hab : a < b) :
    0 < Blueprint.intervalCoupling a b := by
  unfold Blueprint.intervalCoupling
  linarith

lemma center_sub_coupling {a b : ℝ} :
    Blueprint.intervalCenter a b - Blueprint.intervalCoupling a b = a := by
  unfold Blueprint.intervalCenter Blueprint.intervalCoupling
  ring

lemma center_add_coupling {a b : ℝ} :
    Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b = b := by
  unfold Blueprint.intervalCenter Blueprint.intervalCoupling
  ring

lemma siteAffine_mem_Icc {a b : ℝ} (hab : a < b) (v : SingleSite) :
    siteAffine a b v ∈ Set.Icc a b := by
  have hK := coupling_pos hab
  have ht := (v : SingleSite).property
  simp only [Set.mem_Icc] at ht ⊢
  constructor
  · have h1 : Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * (-1)
        = a := by
      have := center_sub_coupling (a := a) (b := b)
      linarith
    calc a = Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * (-1) :=
          h1.symm
      _ ≤ siteAffine a b v := by
          unfold siteAffine
          have := mul_le_mul_of_nonneg_left ht.1 hK.le
          linarith
  · have h2 : Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * 1
        = b := by
      have := center_add_coupling (a := a) (b := b)
      linarith
    calc siteAffine a b v
        ≤ Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * 1 := by
          unfold siteAffine
          have := mul_le_mul_of_nonneg_left ht.2 hK.le
          linarith
      _ = b := h2

lemma measurable_siteAffine (a b : ℝ) : Measurable (siteAffine a b) := by
  unfold siteAffine
  fun_prop

/-- Affine homeomorphism of ℝ used to transport Lebesgue measure. -/
def affineEquiv (center coupling : ℝ) (hc : coupling ≠ 0) : ℝ ≃ᵐ ℝ where
  toEquiv :=
    { toFun := fun t => center + coupling * t
      invFun := fun y => (y - center) / coupling
      left_inv := fun t => by field_simp; ring
      right_inv := fun y => by field_simp; ring }
  measurable_toFun := by
    show Measurable (fun t : ℝ => center + coupling * t)
    fun_prop
  measurable_invFun := by
    show Measurable (fun y : ℝ => (y - center) / coupling)
    fun_prop

lemma affineEquiv_image_Icc {a b : ℝ} (hab : a < b)
    (e : ℝ ≃ᵐ ℝ)
    (he : ∀ t : ℝ, e t = Blueprint.intervalCenter a b
      + Blueprint.intervalCoupling a b * t) :
    e '' Set.Icc (-1 : ℝ) 1 = Set.Icc a b := by
  have hK := coupling_pos hab
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    rw [he]
    have h1 : Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * (-1)
        = a := by
      have h := center_sub_coupling (a := a) (b := b)
      linarith
    have h2 : Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b * 1
        = b := by
      have h := center_add_coupling (a := a) (b := b)
      linarith
    have hlo := mul_le_mul_of_nonneg_left ht1 hK.le
    have hhi := mul_le_mul_of_nonneg_left ht2 hK.le
    constructor <;> linarith
  · intro ⟨hy1, hy2⟩
    refine ⟨(y - Blueprint.intervalCenter a b)
      / Blueprint.intervalCoupling a b, ?_, by rw [he]; field_simp; ring⟩
    have ha : Blueprint.intervalCenter a b - Blueprint.intervalCoupling a b = a :=
      center_sub_coupling
    have hb : Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b = b :=
      center_add_coupling
    constructor
    · rw [le_div_iff₀ hK]
      linarith
    · rw [div_le_iff₀ hK]
      linarith

/-- Real-valued left inverse of the per-site map (0 outside `[a,b]`). -/
def unAffineReal (a b : ℝ) (y : ℝ) : ℝ :=
  if y ∈ Set.Icc a b then
    (y - Blueprint.intervalCenter a b) / Blueprint.intervalCoupling a b
  else 0

lemma measurable_unAffineReal (a b : ℝ) : Measurable (unAffineReal a b) := by
  unfold unAffineReal
  exact Measurable.piecewise measurableSet_Icc (by fun_prop) measurable_const

/-- Subtype-valued left inverse of the per-site map. -/
def siteUnAffine (a b : ℝ) (hab : a < b) (y : ℝ) : SingleSite :=
  ⟨unAffineReal a b y, by
    unfold unAffineReal
    split_ifs with h
    · have hK := coupling_pos hab
      have ha : Blueprint.intervalCenter a b - Blueprint.intervalCoupling a b = a :=
        center_sub_coupling
      have hb : Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b = b :=
        center_add_coupling
      simp only [Set.mem_Icc] at h ⊢
      constructor
      · rw [le_div_iff₀ hK]
        linarith
      · rw [div_le_iff₀ hK]
        linarith
    · norm_num⟩

lemma measurable_siteUnAffine (a b : ℝ) (hab : a < b) :
    Measurable (siteUnAffine a b hab) := by
  have hcoe : Measurable (fun y : ℝ => ((siteUnAffine a b hab y : SingleSite) : ℝ)) := by
    have : (fun y : ℝ => ((siteUnAffine a b hab y : SingleSite) : ℝ))
        = unAffineReal a b := rfl
    rw [this]
    exact measurable_unAffineReal a b
  exact Measurable.subtype_mk hcoe

lemma siteUnAffine_siteAffine {a b : ℝ} (hab : a < b) (v : SingleSite) :
    siteUnAffine a b hab (siteAffine a b v) = v := by
  have hmem := siteAffine_mem_Icc hab v
  have hK := coupling_pos hab
  have hKne : Blueprint.intervalCoupling a b ≠ 0 := ne_of_gt hK
  apply Subtype.ext
  show unAffineReal a b (siteAffine a b v) = (v : ℝ)
  unfold unAffineReal
  simp only [hmem, ite_true]
  show (siteAffine a b v - Blueprint.intervalCenter a b)
    / Blueprint.intervalCoupling a b = (v : ℝ)
  unfold siteAffine
  field_simp
  ring

lemma siteAffine_siteUnAffine {a b : ℝ} (hab : a < b) {y : ℝ}
    (hy : y ∈ Set.Icc a b) :
    siteAffine a b (siteUnAffine a b hab y) = y := by
  have hKne : Blueprint.intervalCoupling a b ≠ 0 := ne_of_gt (coupling_pos hab)
  show Blueprint.intervalCenter a b + Blueprint.intervalCoupling a b *
    ((siteUnAffine a b hab y : SingleSite) : ℝ) = y
  have hcoe : ((siteUnAffine a b hab y : SingleSite) : ℝ) = unAffineReal a b y := rfl
  rw [hcoe]
  unfold unAffineReal
  simp only [hy, ite_true]
  field_simp
  ring

lemma measurableEmbedding_siteAffine {a b : ℝ} (hab : a < b) :
    MeasurableEmbedding (siteAffine a b) := by
  apply MeasurableEmbedding.of_measurable_inverse (measurable_siteAffine a b)
  · have hrange : Set.range (siteAffine a b) = Set.Icc a b := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact siteAffine_mem_Icc hab v
      · intro hy
        exact ⟨siteUnAffine a b hab y, siteAffine_siteUnAffine hab hy⟩
    rw [hrange]
    exact measurableSet_Icc
  · exact measurable_siteUnAffine a b hab
  · intro v
    exact siteUnAffine_siteAffine hab v

lemma scalar_eq {a b : ℝ} (hab : a < b) :
    (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (Blueprint.intervalCoupling a b)⁻¹
      = (ENNReal.ofReal (b - a))⁻¹ := by
  have hba : 0 < b - a := by linarith
  have hK : Blueprint.intervalCoupling a b = (b - a) / 2 := by
    unfold Blueprint.intervalCoupling
    ring
  have hKinv : (Blueprint.intervalCoupling a b)⁻¹ = 2 / (b - a) := by
    rw [hK]
    field_simp
  rw [hKinv, ENNReal.ofReal_div_of_pos hba]
  rw [ENNReal.ofReal_ofNat]
  rw [ENNReal.div_eq_inv_mul]
  calc (2 : ℝ≥0∞)⁻¹ * ((ENNReal.ofReal (b - a))⁻¹ * 2)
      = ((2 : ℝ≥0∞)⁻¹ * 2) * (ENNReal.ofReal (b - a))⁻¹ := by ring
    _ = (ENNReal.ofReal (b - a))⁻¹ := by
        rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

lemma map_affineEquiv (center coupling : ℝ) (hc : 0 < coupling) :
    (volume : Measure ℝ).map
        (affineEquiv center coupling (ne_of_gt hc))
      = ENNReal.ofReal coupling⁻¹ • volume := by
  have hcomp : ((affineEquiv center coupling (ne_of_gt hc)) : ℝ → ℝ)
      = (center + ·) ∘ (coupling * ·) := by
    funext t
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Real.map_volume_mul_left (ne_of_gt hc)]
  have habs : |coupling⁻¹| = coupling⁻¹ := abs_of_pos (inv_pos.mpr hc)
  rw [habs,
    Measure.map_smul _
      ((by fun_prop : Measurable (center + ·)).aemeasurable)]
  rw [(MeasureTheory.measurePreserving_add_left (volume : Measure ℝ) center).map_eq]

lemma siteAffine_map {a b : ℝ} (hab : a < b) :
    uniformSite.map (siteAffine a b) = Blueprint.uniformInterval a b := by
  have hK := coupling_pos hab
  have hKne : Blueprint.intervalCoupling a b ≠ 0 := ne_of_gt hK
  have hfun : siteAffine a b
      = (affineEquiv (Blueprint.intervalCenter a b)
          (Blueprint.intervalCoupling a b) hKne)
        ∘ (fun v : SingleSite => (v : ℝ)) := rfl
  have himage : (affineEquiv (Blueprint.intervalCenter a b)
      (Blueprint.intervalCoupling a b) hKne) '' Set.Icc (-1 : ℝ) 1
      = Set.Icc a b := by
    apply affineEquiv_image_Icc hab
    intro t
    rfl
  have hrest : (volume.restrict (Set.Icc (-1 : ℝ) 1)).map
        ((affineEquiv (Blueprint.intervalCenter a b)
          (Blueprint.intervalCoupling a b) hKne) : ℝ → ℝ)
      = ((volume : Measure ℝ).map
          (affineEquiv (Blueprint.intervalCenter a b)
            (Blueprint.intervalCoupling a b) hKne)).restrict (Set.Icc a b) := by
    have h := (affineEquiv (Blueprint.intervalCenter a b)
      (Blueprint.intervalCoupling a b) hKne).measurableEmbedding.restrict_map
      (volume : Measure ℝ) (Set.Icc a b)
    have hpre : ((affineEquiv (Blueprint.intervalCenter a b)
        (Blueprint.intervalCoupling a b) hKne) : ℝ → ℝ) ⁻¹' (Set.Icc a b)
        = Set.Icc (-1 : ℝ) 1 := by
      rw [← himage,
        (affineEquiv (Blueprint.intervalCenter a b)
          (Blueprint.intervalCoupling a b) hKne).injective.preimage_image _]
    rw [hpre] at h
    exact h.symm
  rw [hfun,
    ← Measure.map_map
      (affineEquiv (Blueprint.intervalCenter a b)
        (Blueprint.intervalCoupling a b) hKne).measurable
      measurable_subtype_coe,
    uniformSite_map_val,
    Measure.map_smul _
      ((affineEquiv (Blueprint.intervalCenter a b)
        (Blueprint.intervalCoupling a b) hKne).measurable.aemeasurable),
    hrest, map_affineEquiv _ _ hK, Measure.restrict_smul]
  unfold Blueprint.uniformInterval
  rw [← smul_assoc, smul_eq_mul, scalar_eq hab]

/-- The affine configuration map is the pi map of the per-site maps. -/
lemma affineConfiguration_eq_pi (d : ℕ) (a b : ℝ) :
    Blueprint.affineConfiguration (d := d) a b
      = fun ω x => siteAffine a b (ω x) := by
  funext ω x
  simp [Blueprint.affineConfiguration, siteAffine, potential]

/-- Measurable left inverse of the configuration map. -/
def configUnAffine (d : ℕ) (a b : ℝ) (hab : a < b) (V : Site d → ℝ) : Configuration d :=
  fun x => siteUnAffine a b hab (V x)

lemma measurable_configUnAffine (d : ℕ) (a b : ℝ) (hab : a < b) :
    Measurable (configUnAffine d a b hab) := by
  unfold configUnAffine
  exact measurable_pi_iff.mpr (fun x =>
    (measurable_siteUnAffine a b hab).comp (measurable_pi_apply x))

lemma measurable_affineConfiguration (d : ℕ) (a b : ℝ) :
    Measurable (Blueprint.affineConfiguration (d := d) a b) := by
  rw [affineConfiguration_eq_pi]
  exact measurable_pi_iff.mpr (fun x =>
    (measurable_siteAffine a b).comp (measurable_pi_apply x))

lemma range_affineConfiguration (d : ℕ) (a b : ℝ) (hab : a < b) :
    Set.range (Blueprint.affineConfiguration (d := d) a b)
      = Set.univ.pi (fun _ => Set.Icc a b) := by
  ext V
  constructor
  · rintro ⟨ω, rfl⟩
    intro x _
    exact siteAffine_mem_Icc hab (ω x)
  · intro hV
    refine ⟨configUnAffine d a b hab V, ?_⟩
    funext x
    show siteAffine a b (siteUnAffine a b hab (V x)) = V x
    exact siteAffine_siteUnAffine hab (hV x (Set.mem_univ x))

lemma measurableEmbedding_affineConfiguration (d : ℕ) (a b : ℝ) (hab : a < b) :
    MeasurableEmbedding (Blueprint.affineConfiguration (d := d) a b) := by
  apply MeasurableEmbedding.of_measurable_inverse
      (measurable_affineConfiguration d a b)
  · rw [range_affineConfiguration d a b hab]
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  · exact measurable_configUnAffine d a b hab
  · intro ω
    funext x
    exact siteUnAffine_siteAffine hab (ω x)

theorem lawTransportCore : Blueprint.LawTransportInput := by
  intro d a b hab
  refine ⟨measurableEmbedding_affineConfiguration d a b hab, ?_⟩
  have hsite := siteAffine_map hab
  rw [affineConfiguration_eq_pi]
  unfold disorderLaw Blueprint.intervalLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_siteAffine a b)]
  simp only [hsite]

end AndersonAC.LunaTransport

namespace AndersonAC.Blueprint.Packages

theorem lawTransport : AndersonAC.Blueprint.LawTransportInput :=
  AndersonAC.LunaTransport.lawTransportCore


end AndersonAC.Blueprint.Packages
