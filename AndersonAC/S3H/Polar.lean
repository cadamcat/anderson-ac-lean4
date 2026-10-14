import AndersonAC.S3.HelperStatements
import AndersonAC.S3.PolarIntegration

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Set
open scoped BigOperators NNReal ENNReal

namespace AndersonAC.S3H

variable {d : ℕ}

/-- finrank of EuclideanSpace Fin d is d. -/
theorem finrank_euc (d : ℕ) : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
  rw [finrank_euclideanSpace]
  simp

/-- Sphere area positivity. -/
theorem sphereArea_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < Measure.real (Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))) Set.univ := by
  have _hNe : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hsphere : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    refine ⟨⟨EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ), ?_⟩⟩
    rw [Metric.mem_sphere, dist_zero_right]
    have h : ‖EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ)‖ = 1 := by
      simp [EuclideanSpace.single, PiLp.norm_single]
    exact h
  have htop : Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d))) Set.univ ≠ 0 := by
    apply IsOpen.measure_ne_zero
    · exact isOpen_univ
    · exact Set.univ_nonempty
  have hfin2 : Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d))) Set.univ ≠ ⊤ := by
    exact (measure_lt_top _ _).ne
  exact ENNReal.toReal_pos htop hfin2

/-- Bochner polar formula for general Haar measure, general codomain. -/
theorem bochner_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → G)
    (hF : Integrable F μ) :
    ∫ x, F x ∂μ =
      ∫ u : Metric.sphere (0 : E) 1,
        (∫ r : Set.Ioi (0 : ℝ), F ((r : ℝ) • (u : E)) ∂(volumeIoiPow (Module.finrank ℝ E - 1)))
        ∂(μ.toSphere) := by
  have hrestr : μ.restrict ({0}ᶜ : Set E) = μ := restrict_compl_singleton 0
  have hsub : ∫ x, F x ∂μ = ∫ x : ({0}ᶜ : Set E), F (x : E) ∂ (μ.comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton 0).compl F, hrestr]
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd (E := E)
  have hHdef : ∀ x : ({0}ᶜ : Set E), F (x : E) =
        (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
          ((homeomorphUnitSphereProd E) x) := by
    intro x
    simp only
    have hx : ((homeomorphUnitSphereProd E x).2 : ℝ) • ((((homeomorphUnitSphereProd E x).1 : Metric.sphere (0 : E) 1) : E)) = (x : E) := by
      rw [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
      have hne : ‖(x : E)‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr x.2)
      rw [← mul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [hx]
  have htrans : (∫ x : ({0}ᶜ : Set E), F (x : E) ∂ (μ.comap Subtype.val)) =
      ∫ p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
        F ((p.2 : ℝ) • (p.1 : E)) ∂(μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1))) := by
    calc (∫ x : ({0}ᶜ : Set E), F (x : E) ∂ (μ.comap Subtype.val))
        = ∫ x : ({0}ᶜ : Set E),
            (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
              ((homeomorphUnitSphereProd E) x) ∂ (μ.comap Subtype.val) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hHdef x
      _ = _ := hmp.integral_comp (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E))
          (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
  have hFsub : Integrable (fun x : ({0}ᶜ : Set E) => F (x : E)) (μ.comap Subtype.val) := by
    have hOn : IntegrableOn F ({0}ᶜ : Set E) μ := by
      rw [IntegrableOn, hrestr]
      exact hF
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton 0).compl).mp hOn
  have hH : Integrable (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
      F ((p.2 : ℝ) • (p.1 : E))) (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1))) := by
    have h_eq : (fun x : ({0}ᶜ : Set E) => F (x : E)) =
        (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E))) ∘
          (homeomorphUnitSphereProd E) := by
      funext x
      exact hHdef x
    rw [h_eq] at hFsub
    exact (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)).mp hFsub
  have hprod : (∫ p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
        F ((p.2 : ℝ) • (p.1 : E)) ∂(μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1)))) =
      ∫ u : Metric.sphere (0 : E) 1,
        (∫ r : Set.Ioi (0 : ℝ), F ((r : ℝ) • (u : E)) ∂(volumeIoiPow (Module.finrank ℝ E - 1)))
        ∂(μ.toSphere) := by
    exact integral_prod _ hH
  rw [hsub, htrans, hprod]

/-- Inner volumeIoiPow integral equals weighted ray integral (real smul form). -/
theorem inner_eq_ray_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) (Gf : E → G) (u : Metric.sphere (0 : E) 1) :
    (∫ r : Set.Ioi (0 : ℝ), Gf ((r : ℝ) • (u : E)) ∂(volumeIoiPow n)) =
      ∫ r in Set.Ioi (0 : ℝ), ((r ^ n : ℝ)) • Gf (r • (u : E)) := by
  have hmeas : Measurable (fun r : Set.Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ n)) := by
    fun_prop
  have hfin : ∀ᵐ r : Set.Ioi (0 : ℝ) ∂(volume.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)),
      ENNReal.ofReal ((r : ℝ) ^ n) < ⊤ := by
    filter_upwards with r
    exact ENNReal.ofReal_lt_top
  have hvol : volumeIoiPow n =
      (volume.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)).withDensity
        (fun r : Set.Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ n)) := by
    rfl
  rw [hvol, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
  have htoReal : ∀ r : Set.Ioi (0 : ℝ), (ENNReal.ofReal ((r : ℝ) ^ n)).toReal = (r : ℝ) ^ n := by
    intro r
    apply ENNReal.toReal_ofReal
    apply pow_nonneg (le_of_lt r.2)
  simp_rw [htoReal]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => ((r ^ n : ℝ)) • Gf (r • (u : E)))]

/-- Strongly convex functions on univ are continuous. -/
theorem strongConvex_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hsc : StrongConvexOn Set.univ c g) : Continuous g := by
  have hunif : UniformConvexOn Set.univ (fun r => c / 2 * r ^ 2) g := hsc
  have hconv : ConvexOn ℝ Set.univ g := by
    apply hunif.convexOn
    intro r
    simp only [Pi.zero_apply]
    positivity
  have hcont : ContinuousOn g Set.univ := hconv.continuousOn isOpen_univ
  rwa [continuousOn_univ] at hcont

/-- Ray monotonicity from minimizer (uses only convexity). -/
theorem ray_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (y₀ : E) (u : E) (c : ℝ) (_hc : 0 < c)
    (hsc : StrongConvexOn Set.univ c g) (hmin : ∀ y, g y₀ ≤ g y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    g (y₀ + a • u) ≤ g (y₀ + b • u) := by
  have hunif : UniformConvexOn Set.univ (fun r => c / 2 * r ^ 2) g := hsc
  have hconv : ConvexOn ℝ Set.univ g := by
    apply hunif.convexOn
    intro r
    simp only [Pi.zero_apply]
    positivity
  by_cases hb0 : b = 0
  · have ha0 : a = 0 := by linarith
    rw [ha0, hb0]
  · have hbpos : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb0)
    have ht0 : 0 ≤ a / b := div_nonneg ha hbpos.le
    have ht1 : a / b ≤ 1 := by
      rw [div_le_one hbpos]
      exact hab
    have h1t : 0 ≤ 1 - a / b := sub_nonneg.mpr ht1
    have htb : (a / b) * b = a := div_mul_cancel₀ a hb0
    have hpt : (1 - a / b) • y₀ + (a / b) • (y₀ + b • u) = y₀ + a • u := by
      rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul, ← mul_smul, htb]
    have hmem1 : y₀ ∈ (Set.univ : Set E) := Set.mem_univ _
    have hmem2 : y₀ + b • u ∈ (Set.univ : Set E) := Set.mem_univ _
    have hconv_ineq := hconv.2 hmem1 hmem2 h1t ht0 (by ring : (1 - a / b) + a / b = 1)
    rw [hpt] at hconv_ineq
    simp only [smul_eq_mul] at hconv_ineq
    by_cases ht0' : a / b = 0
    · have ha0 : a = 0 := by
        rcases div_eq_zero_iff.mp ht0' with h | h
        · exact h
        · exact absurd h hb0
      rw [ha0]
      simp
      exact hmin _
    · have hpos : 0 < a / b := lt_of_le_of_ne ht0 (Ne.symm ht0')
      have hm : g y₀ ≤ g (y₀ + a • u) := hmin _
      have h1 : g (y₀ + a • u) ≤ (1 - a / b) * g (y₀ + a • u) + (a / b) * g (y₀ + b • u) := by
        calc g (y₀ + a • u) ≤ (1 - a / b) * g y₀ + (a / b) * g (y₀ + b • u) := hconv_ineq
          _ ≤ (1 - a / b) * g (y₀ + a • u) + (a / b) * g (y₀ + b • u) := by
            gcongr
      have h2 : (a / b) * g (y₀ + a • u) ≤ (a / b) * g (y₀ + b • u) := by
        linarith
      exact le_of_mul_le_mul_left h2 hpos

/-- Quadratic growth from minimizer. -/
theorem ray_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (y₀ : E) (u : E) (c : ℝ)
    (hsc : StrongConvexOn Set.univ c g) (hmin : ∀ y, g y₀ ≤ g y)
    (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    (c / 4) * r ^ 2 ≤ g (y₀ + r • u) - g y₀ := by
  have hunif : UniformConvexOn Set.univ (fun r => c / 2 * r ^ 2) g := hsc
  have hmem1 : y₀ ∈ (Set.univ : Set E) := Set.mem_univ _
  have hmem2 : y₀ + r • u ∈ (Set.univ : Set E) := Set.mem_univ _
  have hstrong := hunif.2 hmem1 hmem2 (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have hmid : (1/2 : ℝ) • y₀ + (1/2 : ℝ) • (y₀ + r • u) = y₀ + (r/2) • u := by
    module
  rw [hmid] at hstrong
  simp only [smul_eq_mul] at hstrong
  have hnorm : ‖y₀ - (y₀ + r • u)‖ = r := by
    have h1 : y₀ - (y₀ + r • u) = -(r • u) := by module
    rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu, mul_one]
  rw [hnorm] at hstrong
  have hmin2 : g y₀ ≤ g (y₀ + (r/2) • u) := hmin _
  nlinarith

/-- Key shell difference bound. -/
theorem ray_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (y₀ : E) (u : E) (c : ℝ) (hc : 0 < c)
    (hsc : StrongConvexOn Set.univ c g) (hmin : ∀ y, g y₀ ≤ g y)
    (hu : ‖u‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (c / 8) * (b ^ 2 - a ^ 2) ≤ g (y₀ + b • u) - g (y₀ + a • u) := by
  have hunif : UniformConvexOn Set.univ (fun r => c / 2 * r ^ 2) g := hsc
  by_cases hb0 : b = 0
  · have ha0 : a = 0 := by linarith
    simp [ha0, hb0]
  · have hbpos : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb0)
    set t := a / b with htdef
    have ht0 : 0 ≤ t := div_nonneg ha hbpos.le
    have ht1 : t ≤ 1 := by
      rw [htdef, div_le_one hbpos]
      exact hab
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have htb : t * b = a := div_mul_cancel₀ a hb0
    have hgrowth_b : (c / 4) * b ^ 2 ≤ g (y₀ + b • u) - g y₀ :=
      ray_growth g y₀ u c hsc hmin hu hbpos.le
    have hmem1 : y₀ ∈ (Set.univ : Set E) := Set.mem_univ _
    have hmem2 : y₀ + b • u ∈ (Set.univ : Set E) := Set.mem_univ _
    have hstrong := hunif.2 hmem1 hmem2 h1t ht0 (by ring : (1 - t) + t = 1)
    have hpt : (1 - t) • y₀ + t • (y₀ + b • u) = y₀ + a • u := by
      rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul, ← mul_smul, htb]
    rw [hpt] at hstrong
    simp only [smul_eq_mul] at hstrong
    have hnorm : ‖y₀ - (y₀ + b • u)‖ = b := by
      have h1 : y₀ - (y₀ + b • u) = -(b • u) := by module
      rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hbpos.le, hu, mul_one]
    rw [hnorm] at hstrong
    have ha_eq : a = t * b := htb.symm
    rw [ha_eq] at hstrong ⊢
    have hmono : (1 - t) * ((c / 4) * b ^ 2) ≤ (1 - t) * (g (y₀ + b • u) - g y₀) :=
      mul_le_mul_of_nonneg_left hgrowth_b h1t
    have hdiff1 : (1 - t) * (g (y₀ + b • u) - g y₀) + t * (1 - t) * (c / 2 * b ^ 2)
        ≤ g (y₀ + b • u) - g (y₀ + (t * b) • u) := by
      linarith [hstrong]
    have hcomb : (1 - t) * ((c / 4) * b ^ 2) + t * (1 - t) * (c / 2 * b ^ 2)
        ≤ g (y₀ + b • u) - g (y₀ + (t * b) • u) := by
      linarith [hdiff1, hmono]
    have hfinal : (c / 8) * (b ^ 2 - (t * b) ^ 2)
        ≤ (1 - t) * ((c / 4) * b ^ 2) + t * (1 - t) * (c / 2 * b ^ 2) := by
      have heq : ((1 - t) * ((c / 4) * b ^ 2) + t * (1 - t) * (c / 2 * b ^ 2))
          - (c / 8) * (b ^ 2 - (t * b) ^ 2)
          = (1 - t) * b ^ 2 * c * (1 + 3 * t) / 8 := by
        ring
      have hnn : 0 ≤ (1 - t) * b ^ 2 * c * (1 + 3 * t) / 8 := by
        have h1 : 0 ≤ 1 - t := h1t
        have h2 : 0 ≤ b ^ 2 := sq_nonneg b
        have h3 : 0 ≤ c := le_of_lt hc
        have h4 : 0 ≤ 1 + 3 * t := by linarith [ht0]
        positivity
      linarith [hnn, heq]
    linarith [hcomb, hfinal]

/-- Translation preserves strong convexity. -/
theorem strongConvex_translation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (y₀ : E) (c : ℝ) (hsc : StrongConvexOn Set.univ c g) :
    StrongConvexOn Set.univ c (fun z => g (y₀ + z)) := by
  obtain ⟨hset, hineq⟩ := hsc
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    have hmem1 : y₀ + x ∈ (Set.univ : Set E) := Set.mem_univ _
    have hmem2 : y₀ + y ∈ (Set.univ : Set E) := Set.mem_univ _
    have h := hineq hmem1 hmem2 ha hb hab
    have hpt : y₀ + (a • x + b • y) = a • (y₀ + x) + b • (y₀ + y) := by
      have hab1 : (a + b) • y₀ = y₀ := by
        rw [hab, one_smul]
      calc y₀ + (a • x + b • y)
          = (a + b) • y₀ + (a • x + b • y) := by rw [hab1]
        _ = a • y₀ + b • y₀ + (a • x + b • y) := by rw [add_smul]
        _ = a • (y₀ + x) + b • (y₀ + y) := by
            rw [smul_add, smul_add]
            module
    have hnorm : ‖(y₀ + x) - (y₀ + y)‖ = ‖x - y‖ := by
      congr 1
      rw [add_sub_add_left_eq_sub]
    simp only
    rw [hpt]
    calc g (a • (y₀ + x) + b • (y₀ + y))
        ≤ a • g (y₀ + x) + b • g (y₀ + y) - a * b * ((fun r => c / 2 * r ^ 2) ‖(y₀ + x) - (y₀ + y)‖) :=
          h
      _ = a • (fun z => g (y₀ + z)) x + b • (fun z => g (y₀ + z)) y
          - a * b * ((fun r => c / 2 * r ^ 2) ‖x - y‖) := by
          rw [hnorm]

/-- One-dimensional shell bound along a ray (inner volumeIoiPow estimate).
  `φ` is continuous, nondecreasing on `[0,∞)`, with
  `φ(b)-φ(a) ≥ (c/8)*(b^2-a^2)` for `0≤a≤b`.
  Then the `volumeIoiPow (q-1)`-measure of `{r>0 | r≤R ∧ |φ(r)-β|≤s}`
  is at most `8*R^(q-2)*s/c`. -/
theorem inner_shell_bound (q : ℕ) (hq : 2 ≤ q) (c R s β : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hs : 0 < s)
    (φ : ℝ → ℝ) (hcont : Continuous φ)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → φ a ≤ φ b)
    (hdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b → (c / 8) * (b ^ 2 - a ^ 2) ≤ φ b - φ a) :
    (volumeIoiPow (q - 1)) {r : Set.Ioi (0 : ℝ) | r.1 ≤ R ∧ |φ r.1 - β| ≤ s}
      ≤ ENNReal.ofReal (8 * R ^ (q - 2) * s / c) := by
  set S : Set (Set.Ioi (0 : ℝ)) := {r | r.1 ≤ R ∧ |φ r.1 - β| ≤ s} with hSdef
  set T : Set ℝ := {r | 0 < r ∧ r ≤ R ∧ |φ r - β| ≤ s} with hTdef
  -- RHS nonneg for empty case
  have hRHS_nn : 0 ≤ 8 * R ^ (q - 2) * s / c := by
    positivity
  by_cases hSe : S.Nonempty
  · -- T nonempty, bounded, inf/sup
    have hTne : T.Nonempty := by
      obtain ⟨r0, hr0⟩ := hSe
      exact ⟨r0.1, r0.2, hr0.1, hr0.2⟩
    have hTbdd_below : BddBelow T := by
      exact ⟨0, fun x hx => le_of_lt hx.1⟩
    have hTbdd_above : BddAbove T := by
      exact ⟨R, fun x hx => hx.2.1⟩
    set a : ℝ := sInf T with ha_def
    set b : ℝ := sSup T with hb_def
    have ha0 : 0 ≤ a := by
      apply le_csInf hTne
      intro x hx
      exact le_of_lt hx.1
    have hab : a ≤ b := by
      exact csInf_le_csSup hTne hTbdd_below hTbdd_above
    have hbR : b ≤ R := by
      apply csSup_le hTne
      intro x hx
      exact hx.2.1
    have hb2a2 : b ^ 2 - a ^ 2 ≤ 16 * s / c := by
      -- Pairwise bound first
      have hpair : ∀ r1 r2 : ℝ, r1 ∈ T → r2 ∈ T → r1 ≤ r2 → r2 ^ 2 - r1 ^ 2 ≤ 16 * s / c := by
        intro r1 r2 hr1 hr2 hle
        have hr10 : 0 ≤ r1 := le_of_lt hr1.1
        have hlow : (c / 8) * (r2 ^ 2 - r1 ^ 2) ≤ φ r2 - φ r1 :=
          hdiff r1 r2 hr10 hle
        have hup : φ r2 - φ r1 ≤ 2 * s := by
          have h1 : φ r2 - β ≤ s := (abs_le.mp hr2.2.2).2
          have h2 : β - φ r1 ≤ s := by
            have habs := abs_le.mp hr1.2.2
            linarith [habs.1, habs.2]
          linarith
        have hc8 : 0 < c / 8 := by positivity
        have hle2 : (c / 8) * (r2 ^ 2 - r1 ^ 2) ≤ 2 * s := le_trans hlow hup
        have hle2' : (r2 ^ 2 - r1 ^ 2) * (c / 8) ≤ 2 * s := by
          rw [mul_comm]
          exact hle2
        have hdiv : r2 ^ 2 - r1 ^ 2 ≤ 2 * s / (c / 8) :=
          (le_div_iff₀ hc8).mpr hle2'
        have heq : 2 * s / (c / 8) = 16 * s / c := by
          field_simp
          ring
        rw [heq] at hdiv
        exact hdiv
      by_cases hab_eq : a = b
      · simp [hab_eq]
        positivity
      · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
        apply le_of_forall_pos_le_add
        intro ε hε
        have hbpos : 0 < b := lt_of_le_of_lt ha0 hab_lt
        have hba : 0 < b - a := sub_pos.mpr hab_lt
        set δ : ℝ := min ((b - a) / 4) (ε / (8 * R)) with hδdef
        have hδpos : 0 < δ := by
          apply lt_min
          · linarith [hba]
          · positivity
        have hδle1 : δ ≤ (b - a) / 4 := min_le_left _ _
        have hδle2 : δ ≤ ε / (8 * R) := min_le_right _ _
        have ha_lt : sInf T < a + δ := by
          rw [ha_def]
          linarith [hδpos]
        obtain ⟨r1, hr1mem, hr1lt⟩ := exists_lt_of_csInf_lt hTne ha_lt
        have hb_lt : b - δ < sSup T := by
          rw [hb_def]
          linarith [hδpos]
        obtain ⟨r2, hr2mem, hr2gt⟩ := exists_lt_of_lt_csSup hTne hb_lt
        have hr1ge : a ≤ r1 := csInf_le hTbdd_below hr1mem
        have hr2le : r2 ≤ b := le_csSup hTbdd_above hr2mem
        have hr1_le_r2 : r1 ≤ r2 := by
          have h1 : r1 < a + δ := hr1lt
          have h2 : b - δ < r2 := hr2gt
          have h3 : a + δ ≤ b - δ := by linarith [hδle1]
          linarith
        have hpair_le := hpair r1 r2 hr1mem hr2mem hr1_le_r2
        -- Bounds for error terms
        have hr1R : r1 ≤ R := hr1mem.2.1
        have hr2R : r2 ≤ R := hr2mem.2.1
        have hr10 : 0 < r1 := hr1mem.1
        have hr20 : 0 < r2 := hr2mem.1
        have hb0' : 0 ≤ b := le_trans ha0 hab
        have haR : a ≤ R := le_trans hab hbR
        have hbr2 : 0 ≤ b - r2 := sub_nonneg.mpr hr2le
        have hbr2lt : b - r2 < δ := by linarith [hr2gt]
        have hr1a : 0 ≤ r1 - a := sub_nonneg.mpr hr1ge
        have hr1alt : r1 - a < δ := by linarith [hr1lt]
        have hbr2_nn : 0 ≤ b + r2 := by positivity
        have hbr2_le : b + r2 ≤ 2 * R := by linarith [hbR, hr2R]
        have hr1a_nn : 0 ≤ r1 + a := by positivity
        have hr1a_le : r1 + a ≤ 2 * R := by linarith [hr1R, haR]
        have herr1 : b ^ 2 - r2 ^ 2 ≤ δ * (2 * R) := by
          have heq1 : b ^ 2 - r2 ^ 2 = (b - r2) * (b + r2) := by ring
          rw [heq1]
          have h1 : b - r2 ≤ δ := le_of_lt hbr2lt
          have hδnn : 0 ≤ δ := le_of_lt hδpos
          exact mul_le_mul h1 hbr2_le hbr2_nn hδnn
        have herr2 : r1 ^ 2 - a ^ 2 ≤ δ * (2 * R) := by
          have heq2 : r1 ^ 2 - a ^ 2 = (r1 - a) * (r1 + a) := by ring
          rw [heq2]
          have h1 : r1 - a ≤ δ := le_of_lt hr1alt
          have hδnn : 0 ≤ δ := le_of_lt hδpos
          exact mul_le_mul h1 hr1a_le hr1a_nn hδnn
        have h4Rδ : 4 * R * δ ≤ ε := by
          have hRpos : 0 < R := hR
          have h1 : δ ≤ ε / (8 * R) := hδle2
          have h2 : 0 < 8 * R := by positivity
          have h3 : 4 * R * δ ≤ 4 * R * (ε / (8 * R)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 4 * R)
          have heq : 4 * R * (ε / (8 * R)) = ε / 2 := by
            field_simp
            ring
          rw [heq] at h3
          linarith [h3, hε]
        have hfinal_le : b ^ 2 - a ^ 2 ≤ 16 * s / c + ε := by
          have heq3 : b ^ 2 - a ^ 2 = (r2 ^ 2 - r1 ^ 2) + (b ^ 2 - r2 ^ 2) + (r1 ^ 2 - a ^ 2) := by
            ring
          linarith [hpair_le, herr1, herr2, h4Rδ]
        linarith [hfinal_le]
    -- Measure conversion and bound
    have hT_meas : MeasurableSet T := by
      have hpre3 : {r : ℝ | |φ r - β| ≤ s} = φ ⁻¹' (Set.Icc (β - s) (β + s)) := by
        ext r
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
        constructor
        · intro h
          have h2 := abs_le.mp h
          constructor
          · linarith [h2.1, h2.2]
          · linarith [h2.1, h2.2]
        · intro h
          rw [abs_le]
          constructor
          · linarith [h.1, h.2]
          · linarith [h.1, h.2]
      have hT_eq : T = Set.Ioi (0 : ℝ) ∩ (Set.Iic R ∩ {r : ℝ | |φ r - β| ≤ s}) := rfl
      have hIoi : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
      have hIic : MeasurableSet (Set.Iic R) := measurableSet_Iic
      have hS3 : MeasurableSet {r : ℝ | |φ r - β| ≤ s} := by
        rw [hpre3]
        exact hcont.measurable measurableSet_Icc
      rw [hT_eq]
      exact hIoi.inter (hIic.inter hS3)
    have hST_eq : S = Subtype.val ⁻¹' T := by
      ext r
      simp only [hSdef, hTdef, Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro h
        exact ⟨r.2, h.1, h.2⟩
      · intro h
        exact ⟨h.2.1, h.2.2⟩
    have hS_meas : MeasurableSet S := by
      rw [hST_eq]
      exact measurable_subtype_coe hT_meas
    have hvol_eq2 : volumeIoiPow (q - 1) S = ∫⁻ r in T, ENNReal.ofReal (r ^ (q - 1)) ∂volume := by
      have himage : Subtype.val '' S = T := by
        ext r
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.2, hx⟩
        · intro hr
          exact ⟨⟨r, hr.1⟩, hr.2, rfl⟩
      rw [volumeIoiPow, withDensity_apply _ hS_meas,
        setLIntegral_subtype measurableSet_Ioi S (fun r : ℝ => ENNReal.ofReal (r ^ (q - 1))),
        himage]
    have hbound1 : ∀ r : ℝ, r ∈ T → ENNReal.ofReal (r ^ (q - 1)) ≤ ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r := by
      intro r hr
      have hr0 : 0 < r := hr.1
      have hrR : r ≤ R := hr.2.1
      have hr0' : 0 ≤ r := le_of_lt hr0
      have hR0 : 0 ≤ R := le_of_lt hR
      have hq1 : q - 1 = (q - 2) + 1 := by omega
      have hpow_eq : r ^ (q - 1) = r ^ (q - 2) * r := by
        rw [hq1, pow_add, pow_one]
      have hpow_le : r ^ (q - 2) ≤ R ^ (q - 2) :=
        pow_le_pow_left₀ hr0' hrR _
      have hreal_le : r ^ (q - 1) ≤ R ^ (q - 2) * r := by
        rw [hpow_eq]
        exact mul_le_mul_of_nonneg_right hpow_le hr0'
      have hofReal_le : ENNReal.ofReal (r ^ (q - 1)) ≤ ENNReal.ofReal (R ^ (q - 2) * r) :=
        ENNReal.ofReal_le_ofReal hreal_le
      have hRnn : 0 ≤ R ^ (q - 2) := pow_nonneg hR0 _
      rw [ENNReal.ofReal_mul hRnn] at hofReal_le
      exact hofReal_le
    have hbound2 : (∫⁻ r in T, ENNReal.ofReal (r ^ (q - 1)) ∂volume)
        ≤ ENNReal.ofReal (R ^ (q - 2)) * ∫⁻ r in T, ENNReal.ofReal r ∂volume := by
      have hmeas_g : Measurable (fun r : ℝ => ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r) := by
        fun_prop
      have hle_point : ∀ r : ℝ, r ∈ T → ENNReal.ofReal (r ^ (q - 1))
          ≤ ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r :=
        fun r hr => hbound1 r hr
      have hmono : (∫⁻ r in T, ENNReal.ofReal (r ^ (q - 1)) ∂volume)
          ≤ ∫⁻ r in T, ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r ∂volume :=
        setLIntegral_mono hmeas_g (fun r hr => hbound1 r hr)
      have hconst_eq : (∫⁻ r in T, ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r ∂volume)
          = ENNReal.ofReal (R ^ (q - 2)) * ∫⁻ r in T, ENNReal.ofReal r ∂volume := by
        have heq_fun : (fun r : ℝ => T.indicator (fun r => ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r) r)
            = (fun r : ℝ => ENNReal.ofReal (R ^ (q - 2)) * T.indicator (fun r => ENNReal.ofReal r) r) := by
          funext r
          by_cases hrT : r ∈ T
          · simp [hrT]
          · simp [hrT]
        have h1 : (∫⁻ r in T, ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r ∂volume)
            = ∫⁻ r : ℝ, T.indicator (fun r => ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal r) r ∂volume :=
          (lintegral_indicator hT_meas _).symm
        have h2 : ENNReal.ofReal (R ^ (q - 2)) * ∫⁻ r in T, ENNReal.ofReal r ∂volume
            = ∫⁻ r : ℝ, ENNReal.ofReal (R ^ (q - 2)) * T.indicator (fun r => ENNReal.ofReal r) r ∂volume := by
          have hmeas_ind : Measurable (T.indicator (fun r : ℝ => ENNReal.ofReal r)) := by
            exact (by fun_prop : Measurable (fun r : ℝ => ENNReal.ofReal r)).indicator hT_meas
          rw [lintegral_const_mul _ hmeas_ind]
          rw [← lintegral_indicator hT_meas _]
        rw [h1, heq_fun, ← h2]
      rw [hconst_eq] at hmono
      exact hmono
    have hbound3 : (∫⁻ r in T, ENNReal.ofReal r ∂volume)
        ≤ ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) := by
      have hTsub : T ⊆ Set.Icc a b := by
        intro r hr
        exact ⟨csInf_le hTbdd_below hr, le_csSup hTbdd_above hr⟩
      have hIcc_meas : MeasurableSet (Set.Icc a b) := measurableSet_Icc
      have hmeas_id : Measurable (fun r : ℝ => ENNReal.ofReal r) := by fun_prop
      have hmono : (∫⁻ r in T, ENNReal.ofReal r ∂volume)
          ≤ ∫⁻ r in Set.Icc a b, ENNReal.ofReal r ∂volume := by
        exact lintegral_mono_set hTsub
      have hint : IntegrableOn (fun r : ℝ => r) (Set.Icc a b) :=
        continuous_id.continuousOn.integrableOn_Icc
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc a b)] (fun r : ℝ => r) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact ha0.trans hr.1
      have heq : (∫⁻ r in Set.Icc a b, ENNReal.ofReal r ∂volume)
          = ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          integral_id]
      exact hmono.trans_eq heq
    have hfinal : ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2)
        ≤ ENNReal.ofReal (8 * R ^ (q - 2) * s / c) := by
      have hRnn : 0 ≤ R ^ (q - 2) := pow_nonneg hR.le _
      have hba_nn : 0 ≤ (b ^ 2 - a ^ 2) / 2 := by
        have h0 : 0 ≤ b ^ 2 - a ^ 2 := by
          have ha0' : 0 ≤ a := ha0
          have hab' : a ≤ b := hab
          nlinarith [sq_nonneg a, sq_nonneg b, pow_le_pow_left₀ ha0' hab' 2]
        positivity
      have hreal : R ^ (q - 2) * ((b ^ 2 - a ^ 2) / 2) ≤ 8 * R ^ (q - 2) * s / c := by
        have h1 : (b ^ 2 - a ^ 2) / 2 ≤ 16 * s / c / 2 := by
          apply div_le_div_of_nonneg_right hb2a2 (by norm_num : 0 ≤ (2 : ℝ))
        have heq : (16 : ℝ) * s / c / 2 = 8 * s / c := by
          field_simp
          ring
        rw [heq] at h1
        have h2 : R ^ (q - 2) * ((b ^ 2 - a ^ 2) / 2) ≤ R ^ (q - 2) * (8 * s / c) :=
          mul_le_mul_of_nonneg_left h1 hRnn
        have heq2 : R ^ (q - 2) * (8 * s / c) = 8 * R ^ (q - 2) * s / c := by
          ring
        rw [heq2] at h2
        exact h2
      calc ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2)
          = ENNReal.ofReal (R ^ (q - 2) * ((b ^ 2 - a ^ 2) / 2)) := by
            rw [ENNReal.ofReal_mul hRnn]
        _ ≤ ENNReal.ofReal (8 * R ^ (q - 2) * s / c) :=
            ENNReal.ofReal_le_ofReal hreal
    calc volumeIoiPow (q - 1) S
        = ∫⁻ r in T, ENNReal.ofReal (r ^ (q - 1)) ∂volume := hvol_eq2
      _ ≤ ENNReal.ofReal (R ^ (q - 2)) * ∫⁻ r in T, ENNReal.ofReal r ∂volume := hbound2
      _ ≤ ENNReal.ofReal (R ^ (q - 2)) * ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hbound3 zero_le
      _ ≤ ENNReal.ofReal (8 * R ^ (q - 2) * s / c) := hfinal
  · -- Empty case
    rw [Set.not_nonempty_iff_eq_empty.mp hSe]
    rw [measure_empty]
    exact zero_le

end AndersonAC.S3H

namespace AndersonAC.S3

theorem polarRayBound_proof : PolarRayBoundStatement := by
  intro d hd
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  -- Euclidean space and sphere area
  let E := EuclideanSpace ℝ (Fin d)
  have hfin : Module.finrank ℝ E = d := S3H.finrank_euc d
  have hσpos : 0 < Measure.real (Measure.toSphere (volume : Measure E)) Set.univ :=
    S3H.sphereArea_pos d hd
  refine ⟨Measure.real (Measure.toSphere (volume : Measure E)) Set.univ, hσpos, ?_, ?_⟩
  · -- Complex upper bound
    intro f M hF hray
    -- Transfer to Euclidean
    let F : E → ℂ := fun x => f (WithLp.ofLp x)
    have hFint : Integrable F (volume : Measure E) := by
      have hpres : MeasurePreserving (WithLp.ofLp : E → (Fin d → ℝ)) volume volume :=
        PiLp.volume_preserving_ofLp (Fin d)
      have hemb : MeasurableEmbedding (WithLp.ofLp : E → (Fin d → ℝ)) :=
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
      exact (hpres.integrable_comp_emb hemb).mpr hF
    have hFray : ∀ u : Metric.sphere (0 : E) 1,
        ‖∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * F (r • (u : E))‖ ≤ M := by
      intro u
      let ω : Fin d → ℝ := WithLp.ofLp (u : E)
      have hu : ‖(u : E)‖ = 1 := by
        have hmem := u.2
        rw [Metric.mem_sphere, dist_zero_right] at hmem
        exact hmem
      have hω : ∑ j, ω j ^ 2 = 1 := by
        have hsq : ‖(u : E)‖ ^ 2 = ∑ i, (ω i) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          apply Finset.sum_congr rfl
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
        rw [hu, one_pow] at hsq
        exact hsq.symm
      have heq : (∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * F (r • (u : E))) =
          ∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * f (r • ω) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hsm : WithLp.ofLp (r • (u : E)) = r • ω :=
          map_smul (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) r _
        show ((r ^ (d - 1) : ℝ) : ℂ) * f (WithLp.ofLp (r • (u : E))) = _
        rw [hsm]
      rw [heq]
      exact hray ω hω
    -- Polar decomposition
    have hpol := S3H.bochner_polar (volume : Measure E) F hFint
    rw [hfin] at hpol
    have hinner : ∀ u : Metric.sphere (0 : E) 1,
        (∫ r : Set.Ioi (0 : ℝ), F ((r : ℝ) • (u : E)) ∂(volumeIoiPow (d - 1))) =
          ∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * F (r • (u : E)) := by
      intro u
      have hsmul := S3H.inner_eq_ray_smul (d - 1) F u
      rw [hsmul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      show ((r ^ (d - 1) : ℝ)) • F (r • (u : E)) = ((r ^ (d - 1) : ℝ) : ℂ) * F (r • (u : E))
      exact Complex.real_smul
    -- Full integral transfer Fin <-> Euclidean
    have hfull : (∫ k : (Fin d → ℝ), f k ∂(volume : Measure (Fin d → ℝ))) =
        ∫ x : E, F x ∂(volume : Measure E) := by
      have hpres_symm : MeasurePreserving
          ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
          (volume : Measure E) (volume : Measure (Fin d → ℝ)) :=
        EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
      have heq : F = f ∘ ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm) := rfl
      rw [heq]
      exact (hpres_symm.integral_comp'
        (f := ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)) f).symm
    -- Combine to bound full integral
    have hEq : (∫ x : E, F x ∂(volume : Measure E)) =
        ∫ u : Metric.sphere (0 : E) 1,
          (∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * F (r • (u : E)))
          ∂(Measure.toSphere (volume : Measure E)) := by
      rw [hpol]
      apply integral_congr_ae
      filter_upwards with u
      exact hinner u
    have hbound : ‖∫ u : Metric.sphere (0 : E) 1,
          (∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * F (r • (u : E)))
          ∂(Measure.toSphere (volume : Measure E))‖ ≤
        M * Measure.real (Measure.toSphere (volume : Measure E)) Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with u
      exact hFray u
    have hEqFin : (∫ k : (Fin d → ℝ), f k ∂(volume : Measure (Fin d → ℝ))) =
        ∫ u : Metric.sphere (0 : E) 1,
          (∫ r in Set.Ioi (0 : ℝ), ((r ^ (d - 1) : ℝ) : ℂ) * F (r • (u : E)))
          ∂(Measure.toSphere (volume : Measure E)) := by
      rw [hfull, hEq]
    rw [hEqFin]
    rw [mul_comm M _] at hbound
    exact hbound
  · -- Real lower bound
    intro f M hF hnn hray
    let F : E → ℝ := fun x => f (WithLp.ofLp x)
    have hFint : Integrable F (volume : Measure E) := by
      have hpres : MeasurePreserving (WithLp.ofLp : E → (Fin d → ℝ)) volume volume :=
        PiLp.volume_preserving_ofLp (Fin d)
      have hemb : MeasurableEmbedding (WithLp.ofLp : E → (Fin d → ℝ)) :=
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
      exact (hpres.integrable_comp_emb hemb).mpr hF
    have hFray : ∀ u : Metric.sphere (0 : E) 1,
        M ≤ ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * F (r • (u : E)) := by
      intro u
      let ω : Fin d → ℝ := WithLp.ofLp (u : E)
      have hu : ‖(u : E)‖ = 1 := by
        have hmem := u.2
        rw [Metric.mem_sphere, dist_zero_right] at hmem
        exact hmem
      have hω : ∑ j, ω j ^ 2 = 1 := by
        have hsq : ‖(u : E)‖ ^ 2 = ∑ i, (ω i) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          apply Finset.sum_congr rfl
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
        rw [hu, one_pow] at hsq
        exact hsq.symm
      have heq : (∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * F (r • (u : E))) =
          ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * f (r • ω) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hsm : WithLp.ofLp (r • (u : E)) = r • ω :=
          map_smul (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) r _
        show r ^ (d - 1) * f (WithLp.ofLp (r • (u : E))) = _
        rw [hsm]
      rw [heq]
      exact hray ω hω
    have hpol := S3H.bochner_polar (volume : Measure E) F hFint
    rw [hfin] at hpol
    have hinner : ∀ u : Metric.sphere (0 : E) 1,
        (∫ r : Set.Ioi (0 : ℝ), F ((r : ℝ) • (u : E)) ∂(volumeIoiPow (d - 1))) =
          ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * F (r • (u : E)) := by
      intro u
      have hsmul := S3H.inner_eq_ray_smul (d - 1) F u
      rw [hsmul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      show ((r ^ (d - 1) : ℝ)) • F (r • (u : E)) = r ^ (d - 1) * F (r • (u : E))
      exact smul_eq_mul _ _
    have hfull : (∫ k : (Fin d → ℝ), f k ∂(volume : Measure (Fin d → ℝ))) =
        ∫ x : E, F x ∂(volume : Measure E) := by
      have hpres_symm : MeasurePreserving
          ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
          (volume : Measure E) (volume : Measure (Fin d → ℝ)) :=
        EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
      have heq : F = f ∘ ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm) := rfl
      rw [heq]
      exact (hpres_symm.integral_comp'
        (f := ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)) f).symm
    have hEq : (∫ x : E, F x ∂(volume : Measure E)) =
        ∫ u : Metric.sphere (0 : E) 1,
          (∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * F (r • (u : E)))
          ∂(Measure.toSphere (volume : Measure E)) := by
      rw [hpol]
      apply integral_congr_ae
      filter_upwards with u
      exact hinner u
    -- Integrability of ray for integral_mono
    have hH : Integrable (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
        F ((p.2 : ℝ) • (p.1 : E)))
        ((Measure.toSphere (volume : Measure E)).prod (volumeIoiPow (d - 1))) := by
      have hrestr : (volume : Measure E).restrict ({0}ᶜ : Set E) = volume :=
        restrict_compl_singleton 0
      have hFsub : Integrable (fun x : ({0}ᶜ : Set E) => F (x : E))
          ((volume : Measure E).comap Subtype.val) := by
        have hOn : IntegrableOn F ({0}ᶜ : Set E) (volume : Measure E) := by
          rw [IntegrableOn, hrestr]
          exact hFint
        exact (integrableOn_iff_comap_subtypeVal
          (measurableSet_singleton 0).compl).mp hOn
      have hmp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd (E := E)
      have hHdef2 : ∀ x : ({0}ᶜ : Set E), F (x : E) =
          (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
            ((homeomorphUnitSphereProd E) x) := by
        intro x
        simp only
        have hx : ((homeomorphUnitSphereProd E x).2 : ℝ) • ((((homeomorphUnitSphereProd E x).1 : Metric.sphere (0 : E) 1) : E)) = (x : E) := by
          rw [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
          have hne : ‖(x : E)‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr x.2)
          rw [← mul_smul, mul_inv_cancel₀ hne, one_smul]
        rw [hx]
      have h_eq : (fun x : ({0}ᶜ : Set E) => F (x : E)) =
          (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E))) ∘
            (homeomorphUnitSphereProd E) := by
        funext x
        exact hHdef2 x
      rw [h_eq] at hFsub
      have hHfin : Integrable (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
          F ((p.2 : ℝ) • (p.1 : E)))
          ((Measure.toSphere (volume : Measure E)).prod
            (volumeIoiPow (Module.finrank ℝ E - 1))) :=
        (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)).mp hFsub
      rw [hfin] at hHfin
      exact hHfin
    have hray_int : Integrable
        (fun u : Metric.sphere (0 : E) 1 =>
          ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * F (r • (u : E)))
        (Measure.toSphere (volume : Measure E)) := by
      have hvol_int : Integrable
          (fun u : Metric.sphere (0 : E) 1 =>
            ∫ r : Set.Ioi (0 : ℝ), F ((r : ℝ) • (u : E)) ∂(volumeIoiPow (d - 1)))
          (Measure.toSphere (volume : Measure E)) :=
        hH.integral_prod_left
      exact hvol_int.congr (Filter.Eventually.of_forall (fun u => hinner u))
    have hconst_int : Integrable (fun _ : Metric.sphere (0 : E) 1 => M)
        (Measure.toSphere (volume : Measure E)) :=
      integrable_const _
    have hle : (∫ u : Metric.sphere (0 : E) 1, M
          ∂(Measure.toSphere (volume : Measure E))) ≤
        ∫ u : Metric.sphere (0 : E) 1,
          (∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * F (r • (u : E)))
          ∂(Measure.toSphere (volume : Measure E)) := by
      apply integral_mono hconst_int hray_int
      exact hFray
    have hconst_eq : (∫ _ : Metric.sphere (0 : E) 1, M
          ∂(Measure.toSphere (volume : Measure E))) =
        Measure.real (Measure.toSphere (volume : Measure E)) Set.univ * M := by
      rw [integral_const]
      rw [smul_eq_mul]
    have hEqFin : (∫ k : (Fin d → ℝ), f k ∂(volume : Measure (Fin d → ℝ))) =
        ∫ u : Metric.sphere (0 : E) 1,
          (∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * F (r • (u : E)))
          ∂(Measure.toSphere (volume : Measure E)) := by
      rw [hfull, hEq]
    rw [hconst_eq, ← hEqFin] at hle
    exact hle

theorem convexShell_proof : ConvexShellStatement := by
  intro q hq
  haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  let E := EuclideanSpace ℝ (Fin q)
  have hfin : Module.finrank ℝ E = q := S3H.finrank_euc q
  have hσpos : 0 < Measure.real (Measure.toSphere (volume : Measure E)) Set.univ :=
    S3H.sphereArea_pos q hq
  -- C = 8 * σ
  refine ⟨8 * Measure.real (Measure.toSphere (volume : Measure E)) Set.univ, by positivity, ?_⟩
  intro g y₀ c R β s hc hR hs hsc hmin
  -- Continuity of g
  have hg_cont : Continuous g :=
    S3H.strongConvex_continuous (E := E) g c hc hsc
  -- Translated g0 with minimizer at 0
  let g0 : E → ℝ := fun z => g (y₀ + z)
  have hg0_sc : StrongConvexOn Set.univ c g0 :=
    S3H.strongConvex_translation g y₀ c hsc
  have hg0_min : ∀ z : E, g0 0 ≤ g0 z := by
    intro z
    show g (y₀ + 0) ≤ g (y₀ + z)
    rw [add_zero]
    exact hmin _
  have hg0_cont : Continuous g0 := hg_cont.comp (continuous_const_add y₀)
  -- Shell sets
  let S : Set E := {y | dist y y₀ ≤ R ∧ |g y - β| ≤ s}
  let T0 : Set E := {z | dist z 0 ≤ R ∧ |g0 z - β| ≤ s}
  have hS_meas : MeasurableSet S := by
    have hclosed1 : IsClosed {y : E | dist y y₀ ≤ R} := isClosed_closedBall
    have hclosed2 : IsClosed {y : E | |g y - β| ≤ s} := by
      have hIcc : IsClosed (Set.Icc (β - s) (β + s)) := isClosed_Icc
      have hpre : {y : E | |g y - β| ≤ s} = g ⁻¹' (Set.Icc (β - s) (β + s)) := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
        constructor
        · intro h
          have h2 := abs_le.mp h
          constructor
          · linarith [h2.1, h2.2]
          · linarith [h2.1, h2.2]
        · intro h
          rw [abs_le]
          constructor
          · linarith [h.1, h.2]
          · linarith [h.1, h.2]
      rw [hpre]
      exact hIcc.preimage hg_cont
    have hclosed : IsClosed S := by
      have heq : S = {y : E | dist y y₀ ≤ R} ∩ {y : E | |g y - β| ≤ s} := rfl
      rw [heq]
      exact hclosed1.inter hclosed2
    exact hclosed.measurableSet
  have hvol_eq : volume S = volume T0 := by
    have hpre : T0 = (fun z : E => y₀ + z) ⁻¹' S := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · intro h
        obtain ⟨hdist, hshell⟩ := h
        have hdist2 : dist (y₀ + z) y₀ ≤ R := by
          have heq : dist (y₀ + z) y₀ = dist z 0 := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            rw [add_sub_cancel_left, sub_zero]
          rw [heq]
          exact hdist
        have hshell2 : |g (y₀ + z) - β| ≤ s := hshell
        exact ⟨hdist2, hshell2⟩
      · intro h
        obtain ⟨hdist, hshell⟩ := h
        have hdist2 : dist z 0 ≤ R := by
          have heq : dist (y₀ + z) y₀ = dist z 0 := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            rw [add_sub_cancel_left, sub_zero]
          rw [← heq]
          exact hdist
        exact ⟨hdist2, hshell⟩
    have hmeas_trans : Measurable (fun z : E => y₀ + z) :=
      measurable_const_add y₀
    have hmap : Measure.map (fun z : E => y₀ + z) (volume : Measure E) = volume :=
      Measure.IsAddLeftInvariant.map_add_left_eq_self y₀
    calc volume S = Measure.map (fun z : E => y₀ + z) (volume : Measure E) S := by
            rw [hmap]
      _ = volume ((fun z : E => y₀ + z) ⁻¹' S) := by
            rw [Measure.map_apply hmeas_trans hS_meas]
      _ = volume T0 := by rw [← hpre]
  -- T0 measurable (closed)
  have hT0_meas : MeasurableSet T0 := by
    have hclosed1 : IsClosed {z : E | dist z 0 ≤ R} := isClosed_closedBall
    have hclosed2 : IsClosed {z : E | |g0 z - β| ≤ s} := by
      have hIcc : IsClosed (Set.Icc (β - s) (β + s)) := isClosed_Icc
      have hpre : {z : E | |g0 z - β| ≤ s} = g0 ⁻¹' (Set.Icc (β - s) (β + s)) := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
        constructor
        · intro h
          have h2 := abs_le.mp h
          constructor
          · linarith [h2.1, h2.2]
          · linarith [h2.1, h2.2]
        · intro h
          rw [abs_le]
          constructor
          · linarith [h.1, h.2]
          · linarith [h.1, h.2]
      rw [hpre]
      exact hIcc.preimage hg0_cont
    have hclosed : IsClosed T0 := by
      have heq : T0 = {z : E | dist z 0 ≤ R} ∩ {z : E | |g0 z - β| ≤ s} := rfl
      rw [heq]
      exact hclosed1.inter hclosed2
    exact hclosed.measurableSet
  -- Polar via lintegral
  have hpol : volume T0 =
      ∫⁻ u : Metric.sphere (0 : E) 1, ∫⁻ r : Set.Ioi (0 : ℝ),
        T0.indicator 1 ((r : ℝ) • (u : E)) ∂(volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(Measure.toSphere (volume : Measure E)) := by
    have hfind : Measurable (T0.indicator 1 : E → ℝ≥0∞) :=
      measurable_const.indicator hT0_meas
    have hvol : volume T0 = ∫⁻ z : E, T0.indicator 1 z ∂(volume : Measure E) := by
      rw [lintegral_indicator_one hT0_meas]
    rw [hvol]
    exact AndersonAC.S3.polar_lintegral (volume : Measure E) _ hfind
  rw [hfin] at hpol
  -- Inner bound uniformly
  have hinner : ∀ u : Metric.sphere (0 : E) 1,
      (∫⁻ r : Set.Ioi (0 : ℝ), T0.indicator 1 ((r : ℝ) • (u : E)) ∂(volumeIoiPow (q - 1)))
        ≤ ENNReal.ofReal (8 * R ^ (q - 2) * s / c) := by
    intro u
    have hu : ‖(u : E)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.2
    let φ : ℝ → ℝ := fun r => g0 (r • (u : E))
    have hcont : Continuous φ := hg0_cont.comp (continuous_id.smul continuous_const)
    have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → φ a ≤ φ b := by
      intro a b ha hab
      simpa only [zero_add] using
        S3H.ray_mono g0 0 (u : E) c hc hg0_sc hg0_min ha hab
    have hdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
        (c / 8) * (b ^ 2 - a ^ 2) ≤ φ b - φ a := by
      intro a b ha hab
      simpa only [zero_add] using
        S3H.ray_diff g0 0 (u : E) c hc hg0_sc hg0_min hu ha hab
    let U : Set (Set.Ioi (0 : ℝ)) := {r | r.1 ≤ R ∧ |φ r.1 - β| ≤ s}
    have hUmeas : MeasurableSet U := by
      exact ((isClosed_le continuous_subtype_val continuous_const).inter
        (isClosed_le (((hcont.comp continuous_subtype_val).sub continuous_const).abs)
          continuous_const)).measurableSet
    have hind : (fun r : Set.Ioi (0 : ℝ) => T0.indicator (1 : E → ℝ≥0∞)
        ((r : ℝ) • (u : E))) = U.indicator 1 := by
      funext r
      have hdist : dist ((r : ℝ) • (u : E)) 0 = (r : ℝ) := by
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos r.2, hu, mul_one]
      have hmem : ((r : ℝ) • (u : E)) ∈ T0 ↔ r ∈ U := by
        change (dist ((r : ℝ) • (u : E)) 0 ≤ R ∧ |φ r.1 - β| ≤ s) ↔ _
        rw [hdist]
        rfl
      by_cases hr : r ∈ U
      · rw [Set.indicator_of_mem (hmem.mpr hr), Set.indicator_of_mem hr]
        rfl
      · rw [Set.indicator_of_notMem (fun h => hr (hmem.mp h)), Set.indicator_of_notMem hr]
    rw [hind, lintegral_indicator_one hUmeas]
    exact S3H.inner_shell_bound q hq c R s β hc hR hs φ hcont hmono hdiff
  -- Outer bound
  change volume S ≤ _
  rw [hvol_eq, hpol]
  calc
    _ ≤ ∫⁻ _ : Metric.sphere (0 : E) 1, ENNReal.ofReal (8 * R ^ (q - 2) * s / c)
        ∂(Measure.toSphere (volume : Measure E)) := lintegral_mono hinner
    _ = _ := by
      rw [lintegral_const, ← ofReal_measureReal,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * R ^ (q - 2) * s / c)]
      congr 1
      ring

end AndersonAC.S3
