import AndersonAC.S3.SymbolStatements
import AndersonAC.S3.Assembly

/-!
`GridBoundsStatement` from the helper statements: grid quadrature, the continuum
bottom-of-band bounds, and the two symbol statements. The scalar-map bounds are
proved here; the rest is the choice of a small `t` (via `s = t^{1/20}`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal

namespace AndersonAC.S3

variable {d : ℕ}

theorem perturbedDispersion_one_zero (κ : Frequency d) :
    perturbedDispersion (fun _ => 1) (fun _ => 0) κ = dispersion κ := by
  simp [perturbedDispersion, dispersion]

/-- The continuum resolvent at excess energy `β` and height `v`. -/
def bandRes (d : ℕ) (β v : ℝ) (κ : Frequency d) : ℂ :=
  (((dispersion κ + 2 * d - β : ℝ) : ℂ) - v * Complex.I)⁻¹

theorem gridResolvent_eq_bandRes {L : ℕ} [NeZero L] (E t : ℝ) (r : ℂ) (k : Torus d L) :
    gridResolvent E t r k = bandRes d (E + 2 * d + t * r.re) (t * r.im) (gridAngle k) := by
  unfold gridResolvent bandRes
  congr 1
  apply Complex.ext <;> simp <;> ring

theorem dispersion_continuous : Continuous (dispersion (d := d)) := by
  unfold dispersion
  fun_prop

theorem bandRes_den_ne {β v : ℝ} (hv : 0 < v) (κ : Frequency d) :
    (((dispersion κ + 2 * d - β : ℝ) : ℂ) - v * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem bandRes_continuous {β v : ℝ} (hv : 0 < v) : Continuous (bandRes d β v) := by
  unfold bandRes
  refine Continuous.inv₀ ?_ (bandRes_den_ne hv)
  have := dispersion_continuous (d := d)
  fun_prop

theorem integrableOn_cube_of_continuous {f : Frequency d → ℂ} (hf : Continuous f) :
    IntegrableOn f (torusCube d) := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (hf.continuousOn.integrableOn_compact hK).mono_set
    (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)

theorem bandRes_im {β v : ℝ} (κ : Frequency d) :
    (bandRes d β v κ).im = v / ((dispersion κ + 2 * d - β) ^ 2 + v ^ 2) := by
  unfold bandRes
  rw [Complex.inv_im, Complex.normSq_apply]
  simp
  ring

theorem bandRes_lip {β v : ℝ} (hv : 0 < v) (x y : Frequency d) :
    dist (bandRes d β v x) (bandRes d β v y) ≤ 2 * d / v ^ 2 * dist x y := by
  have hz : 0 < ((v : ℂ) * Complex.I).im := by simp [hv]
  have h := resolvent_dist_le (fun κ => dispersion κ + 2 * d - β) (2 * d)
    (fun x y => by
      rw [show dispersion x + 2 * d - β - (dispersion y + 2 * d - β) =
        dispersion x - dispersion y by ring]
      exact abs_dispersion_sub_le x y) hz x y
  simpa [bandRes] using h

theorem bandRes_sq_lip {β v : ℝ} (hv : 0 < v) (x y : Frequency d) :
    dist (bandRes d β v x ^ 2) (bandRes d β v y ^ 2) ≤ 2 * (2 * d) / v ^ 3 * dist x y := by
  have hz : 0 < ((v : ℂ) * Complex.I).im := by simp [hv]
  have h := resolvent_sq_dist_le (fun κ => dispersion κ + 2 * d - β) (2 * d)
    (fun x y => by
      rw [show dispersion x + 2 * d - β - (dispersion y + 2 * d - β) =
        dispersion x - dispersion y by ring]
      exact abs_dispersion_sub_le x y) hz x y
  simpa [bandRes] using h

/-- Grid bounds for the scalar map, its derivative and the absolute average. -/
theorem scalar_core (hQ : PeriodicGridQuadratureStatement) (hB : BottomResolventStatement)
    (hd : 3 ≤ d) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁' : β₁ ≤ 3 / 200) :
    ∃ Cq C₁ c₁ : ℝ, 0 < Cq ∧ 0 < C₁ ∧ 0 < c₁ ∧
      ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → ∀ β v : ℝ, β₁ ≤ β → β ≤ 3 / 200 →
        0 < v → v ≤ 1 →
        ((2 * Real.pi) ^ d)⁻¹ * c₁ - Cq * (2 * d / v ^ 2) / L ≤
            (gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k))).im ∧
        ‖gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k))‖ ≤
            ((2 * Real.pi) ^ d)⁻¹ * C₁ + Cq * (2 * d / v ^ 2) / L ∧
        ‖gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k) ^ 2)‖ ≤
            ((2 * Real.pi) ^ d)⁻¹ * (C₁ * Real.log (2 / v)) + Cq * (2 * (2 * d) / v ^ 3) / L ∧
        gridAvgReal (fun k : Torus d L => ‖bandRes d β v (gridAngle k)‖) ≤
            ((2 * Real.pi) ^ d)⁻¹ * (C₁ * Real.log (2 / v)) + Cq * (2 * d / v ^ 2) / L := by
  obtain ⟨ε, C₁, c₁, hε, hC₁, hc₁, hBR⟩ := hB d hd β₁ (3 / 200) hβ₁ hβ₁' (by norm_num)
  obtain ⟨Cq, hCq, hq⟩ := grid_quadrature_apply hQ d
  refine ⟨Cq, C₁, c₁, hCq, hC₁, hc₁, ?_⟩
  intro L _ hL hEv β v hβ1 hβ2 hv hv1
  obtain ⟨h1, h2, h3, h4⟩ := hBR β ⟨hβ1, hβ2⟩ v hv hv1
  set ν : ℝ := ((2 * Real.pi) ^ d)⁻¹ with hν
  have hνpos : 0 < ν := by positivity
  set f := bandRes d β v with hf
  have hfint : Integrable f (volume.restrict (torusCube d)) :=
    integrableOn_cube_of_continuous (bandRes_continuous hv)
  -- quadrature for `f`
  have hqf := hq L hL hEv f (2 * d / v ^ 2) (by positivity) (bandRes_lip hv)
  set err := Cq * (2 * d / v ^ 2) / L with herr
  have hint_im : (∫ k in torusCube d, f k).im =
      ∫ k in torusCube d, v / ((dispersion k + 2 * d - β) ^ 2 + v ^ 2) := by
    have := integral_im (𝕜 := ℂ) hfint
    simp only [RCLike.im_to_complex] at this
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun κ => bandRes_im κ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hw := Complex.abs_im_le_norm
      (gridAvg (fun k : Torus d L => f (gridAngle k)) - (ν : ℂ) * ∫ k in torusCube d, f k)
    rw [Complex.sub_im, Complex.im_ofReal_mul, hint_im] at hw
    have hc := mul_le_mul_of_nonneg_left h3 hνpos.le
    have := (abs_le.mp (hw.trans hqf)).1
    linarith
  · calc ‖gridAvg (fun k : Torus d L => f (gridAngle k))‖
        ≤ ‖(ν : ℂ) * ∫ k in torusCube d, f k‖ +
            ‖gridAvg (fun k : Torus d L => f (gridAngle k)) - (ν : ℂ) * ∫ k in torusCube d, f k‖ :=
          norm_le_insert' _ _
      _ ≤ ν * C₁ + err := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνpos]
          exact add_le_add (mul_le_mul_of_nonneg_left h2 hνpos.le) hqf
  · have hqf2 := hq L hL hEv (fun κ => f κ ^ 2) (2 * (2 * d) / v ^ 3) (by positivity)
      (bandRes_sq_lip hv)
    have h4' := h4 (fun _ => 1) (fun _ => 0) (fun _ => by simp [hε.le])
    simp_rw [perturbedDispersion_one_zero] at h4'
    calc ‖gridAvg (fun k : Torus d L => f (gridAngle k) ^ 2)‖
        ≤ ‖(ν : ℂ) * ∫ k in torusCube d, f k ^ 2‖ +
            ‖gridAvg (fun k : Torus d L => f (gridAngle k) ^ 2) -
              (ν : ℂ) * ∫ k in torusCube d, f k ^ 2‖ := norm_le_insert' _ _
      _ ≤ ν * (C₁ * Real.log (2 / v)) + Cq * (2 * (2 * d) / v ^ 3) / L := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνpos]
          exact add_le_add (mul_le_mul_of_nonneg_left h4' hνpos.le) hqf2
  · set F : Frequency d → ℂ := fun κ => ((‖f κ‖ : ℝ) : ℂ) with hF
    have hFlip : ∀ x y, dist (F x) (F y) ≤ 2 * d / v ^ 2 * dist x y := by
      intro x y
      rw [hF, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_norm_sub_norm_le _ _).trans (by rw [← dist_eq_norm]; exact bandRes_lip hv x y)
    have hqF := hq L hL hEv F (2 * d / v ^ 2) (by positivity) hFlip
    have hgrid : gridAvg (fun k : Torus d L => F (gridAngle k)) =
        ((gridAvgReal (fun k : Torus d L => ‖f (gridAngle k)‖) : ℝ) : ℂ) := by
      simp [gridAvg, gridAvgReal, hF]
    have hintF : ∫ k in torusCube d, F k = ((∫ k in torusCube d, ‖f k‖ : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [hgrid, hintF, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at hqF
    have := (abs_le.mp hqF).2
    have h1' : (∫ k in torusCube d, ‖f k‖) ≤ C₁ * Real.log (2 / v) := h1
    have hc := mul_le_mul_of_nonneg_left h1' hνpos.le
    linarith

theorem log_le_twentieth {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    Real.log (c / t) ≤ 20 * c ^ (1 / 20 : ℝ) / t ^ (1 / 20 : ℝ) := by
  have h := Real.log_le_rpow_div (x := c / t) (by positivity) (ε := 1 / 20) (by norm_num)
  rw [Real.div_rpow hc.le ht.le] at h
  have hs : 0 < t ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos ht _
  calc Real.log (c / t) ≤ c ^ (1 / 20 : ℝ) / t ^ (1 / 20 : ℝ) / (1 / 20) := h
    _ = 20 * c ^ (1 / 20 : ℝ) / t ^ (1 / 20 : ℝ) := by field_simp

theorem twentieth_pow {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (t ^ (1 / 20 : ℝ)) ^ k = t ^ ((k : ℝ) / 20) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  ring

theorem err_le {Cq c a₀ t v L : ℝ} {k : ℕ} (hk : k ≤ 7) (hCq : 0 ≤ Cq) (hc : 0 ≤ c)
    (ha₀ : 0 < a₀) (ht : 0 < t) (ht1 : t ≤ 1) (hv : a₀ * t ≤ v) (hL : t⁻¹ ^ 8 ≤ L) :
    Cq * (c / v ^ k) / L ≤ Cq * c / a₀ ^ k * t := by
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hvk : (a₀ * t) ^ k ≤ v ^ k := pow_le_pow_left₀ (by positivity) hv k
  have h1 : 1 ≤ t ^ 8 * L := by
    have e : t ^ 8 * t⁻¹ ^ 8 = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]
    have := mul_le_mul_of_nonneg_left hL (pow_pos ht 8).le
    linarith
  have htk : t ^ 8 ≤ t ^ (k + 1) := pow_le_pow_of_le_one ht.le ht1 (by omega)
  have key : a₀ ^ k ≤ t * v ^ k * L := by
    calc a₀ ^ k = a₀ ^ k * 1 := by ring
      _ ≤ a₀ ^ k * (t ^ 8 * L) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ a₀ ^ k * (t ^ (k + 1) * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htk hL0.le) (by positivity)
      _ = t * (a₀ * t) ^ k * L := by ring
      _ ≤ t * v ^ k * L := by
          apply mul_le_mul_of_nonneg_right _ hL0.le
          exact mul_le_mul_of_nonneg_left hvk ht.le
  rw [mul_div_assoc', div_div, div_le_iff₀ (by positivity)]
  calc Cq * c = Cq * c / a₀ ^ k * a₀ ^ k := by field_simp
    _ ≤ Cq * c / a₀ ^ k * (t * v ^ k * L) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = Cq * c / a₀ ^ k * t * (v ^ k * L) := by ring

set_option maxHeartbeats 2000000 in
/-- **Grid bounds from the helper statements.** -/
theorem gridBounds_of_helpers (hQ : PeriodicGridQuadratureStatement)
    (hB : BottomResolventStatement) (hS : SmallSymbolStatement) (hLS : LargeSymbolStatement) :
    GridBoundsStatement := by
  intro d hd
  obtain ⟨Cq, C₁, c₁, hCq, hC₁, hc₁, hcore⟩ := scalar_core hQ hB hd (β₁ := 1 / 800)
    (by norm_num) (by norm_num)
  set ν : ℝ := ((2 * Real.pi) ^ d)⁻¹ with hνdef
  have hν : 0 < ν := by positivity
  set a₀ : ℝ := ν * c₁ / 2 with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  set B : ℝ := ν * C₁ + 1 + a₀ with hBdef
  have hB0 : 0 < B := by positivity
  have haB : a₀ ≤ B := by
    have : 0 ≤ ν * C₁ := by positivity
    linarith
  refine ⟨a₀, B, ha₀, haB, ?_⟩
  intro δ hδ
  obtain ⟨η, Cs, ts, hη, hCs, hts, hSm⟩ := hS d hd a₀ B ha₀ haB
  obtain ⟨Cl, tl, hCl, htl, hLg⟩ := hLS d hd a₀ B ha₀ haB η hη
  set Ma : ℝ := 20 * (2 / a₀) ^ (1 / 20 : ℝ) with hMa
  set M : ℝ := 20 * (2 : ℝ) ^ (1 / 20 : ℝ) with hM
  have hMa0 : 0 < Ma := by positivity
  have hM0 : 0 < M := by positivity
  set K : ℝ := Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
    Cs * M + Cl * M ^ 2 + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
      Cs * M + Cl * M ^ 2 := by positivity
    linarith
  have hK0 : 0 < K := by linarith
  set m₀ : ℝ := min (min a₀ 1) (min (1 / 4) δ) with hm₀
  have hm₀pos : 0 < m₀ := lt_min (lt_min ha₀ one_pos) (lt_min (by norm_num) hδ)
  set s₀ : ℝ := min (1 / 2) (m₀ / K) with hs₀
  have hs₀pos : 0 < s₀ := lt_min (by norm_num) (by positivity)
  refine ⟨min (s₀ ^ 20) (min ts (min tl (1 / (800 * B)))), by positivity, ?_⟩
  intro t ht htt₀ L _ hL4 hLe hLbig E hE1 hE2 r hr
  have htts : t ≤ ts := htt₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have httl : t ≤ tl := htt₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have htB : t ≤ 1 / (800 * B) := htt₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have htB' : t * B ≤ 1 / 800 := by
    rw [le_div_iff₀ (by positivity)] at htB; linarith
  -- s = t^{1/20}
  set s : ℝ := t ^ (1 / 20 : ℝ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos ht _
  have hss₀ : s ≤ s₀ := by
    have h := Real.rpow_le_rpow ht.le (htt₀.trans (min_le_left _ _)) (by norm_num : (0 : ℝ) ≤ 1 / 20)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hs₀pos.le, show ((20 : ℕ) : ℝ) * (1 / 20) = 1 by
      norm_num, Real.rpow_one] at h
  have hs_half : s ≤ 1 / 2 := hss₀.trans (min_le_left _ _)
  have hs1 : s ≤ 1 := by linarith
  have hKs : K * s ≤ m₀ := by
    have := hss₀.trans (min_le_right _ _)
    rw [le_div_iff₀ hK0] at this; linarith
  have ht_eq : t = s ^ 20 := by
    rw [twentieth_pow ht]; norm_num
  have ht1 : t ≤ 1 := by rw [ht_eq]; exact pow_le_one₀ hs0.le hs1
  have hts_le : t ≤ s := by
    rw [ht_eq]; exact pow_le_of_le_one hs0.le hs1 (by norm_num)
  -- the parameters of the resolvent
  have hrim : 0 < r.im := rectangle_im_pos ha₀ hr
  obtain ⟨hrre, hrim1, hrim2⟩ := hr
  set β : ℝ := E + 2 * d + t * r.re with hβ
  set v : ℝ := t * r.im with hv
  have hv0 : 0 < v := mul_pos ht hrim
  have hva : a₀ * t ≤ v := by rw [hv, mul_comm]; exact mul_le_mul_of_nonneg_left hrim1 ht.le
  have hvB : v ≤ t * B := by rw [hv]; exact mul_le_mul_of_nonneg_left hrim2 ht.le
  have hv1 : v ≤ 1 := by linarith
  have hre : |t * r.re| ≤ 1 / 800 := by
    rw [abs_mul, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hrre ht.le).trans htB'
  have hβ1 : 1 / 800 ≤ β := by have := (abs_le.mp hre).1; linarith
  have hβ2 : β ≤ 3 / 200 := by have := (abs_le.mp hre).2; linarith
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcore L hL4 hLe β v hβ1 hβ2 hv0 hv1
  have hLR : ∀ k : Torus d L, gridResolvent E t r k = bandRes d β v (gridAngle k) :=
    fun k => gridResolvent_eq_bandRes E t r k
  -- error terms
  have herr1 : Cq * (2 * d / v ^ 2) / L ≤ K * s := by
    have h := err_le (k := 2) (c := 2 * (d : ℝ)) (by norm_num) hCq.le (by positivity) ha₀ ht ht1
      hva hLbig
    have : Cq * (2 * d) / a₀ ^ 2 * t ≤ Cq * (2 * d) / a₀ ^ 2 * s :=
      mul_le_mul_of_nonneg_left hts_le (by positivity)
    have hle : Cq * (2 * d) / a₀ ^ 2 ≤ K := by
      have : 0 ≤ ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 + Cs * M + Cl * M ^ 2 := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right hle hs0.le
    linarith
  have herr2 : Cq * (2 * (2 * d) / v ^ 3) / L ≤ K * s := by
    have h := err_le (k := 3) (c := 2 * (2 * (d : ℝ))) (by norm_num) hCq.le (by positivity) ha₀
      ht ht1 hva hLbig
    have : Cq * (2 * (2 * d)) / a₀ ^ 3 * t ≤ Cq * (2 * (2 * d)) / a₀ ^ 3 * s :=
      mul_le_mul_of_nonneg_left hts_le (by positivity)
    have hle : Cq * (2 * (2 * d)) / a₀ ^ 3 ≤ K := by
      have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cs * M + Cl * M ^ 2 := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right hle hs0.le
    linarith
  have hKm1 : K * s ≤ min a₀ 1 := hKs.trans (min_le_left _ _)
  have hKm2 : K * s ≤ 1 / 4 := hKs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hKm3 : K * s ≤ δ := hKs.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- logarithms
  have hlogv : Real.log (2 / v) ≤ Ma / s := by
    have h1 : Real.log (2 / v) ≤ Real.log ((2 / a₀) / t) := by
      apply Real.log_le_log (by positivity)
      rw [div_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hva
    exact h1.trans (log_le_twentieth (c := 2 / a₀) (by positivity) ht)
  have hlogt : Real.log (2 / t) ≤ M / s := by
    exact log_le_twentieth (c := 2) (by norm_num) ht
  have hlogt0 : 0 ≤ Real.log (2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hlogv0 : 0 ≤ Real.log (2 / v) := Real.log_nonneg (by rw [le_div_iff₀ hv0]; linarith)
  have hνC : ν * C₁ * Ma ≤ K := by
    have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + Cq * (2 * (2 * d)) / a₀ ^ 3 + Cs * M + Cl * M ^ 2 := by
      positivity
    linarith
  have hsMa : ν * C₁ * Ma * s ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hνC hs0.le).trans hKm2
  have hscalar : scalarMap (d := d) (L := L) E t r =
      gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k)) := by
    unfold scalarMap; congr 1; funext k; exact hLR k
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the rectangle is preserved
    rw [hscalar]
    set Φ := gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k))
    have hΦ : ‖Φ‖ ≤ B := by
      have := hc2
      have h1 : Cq * (2 * d / v ^ 2) / L ≤ 1 := herr1.trans (hKm1.trans (min_le_right _ _))
      linarith
    refine ⟨(Complex.abs_re_le_norm Φ).trans hΦ, ?_, (le_abs_self _).trans
      ((Complex.abs_im_le_norm Φ).trans hΦ)⟩
    have h1 : Cq * (2 * d / v ^ 2) / L ≤ a₀ := herr1.trans (hKm1.trans (min_le_left _ _))
    have : ν * c₁ = 2 * a₀ := by rw [ha₀def]; ring
    linarith
  · -- the contraction constant
    have hsq : gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2) =
        gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k) ^ 2) := by
      congr 1; funext k; rw [hLR k]
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hA : t * (ν * (C₁ * Real.log (2 / v))) ≤ 1 / 4 := by
      have e1 : t * (ν * (C₁ * Real.log (2 / v))) ≤ t * (ν * C₁ * (Ma / s)) := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hlogv (by positivity)
      have e2 : t * (ν * C₁ * (Ma / s)) = ν * C₁ * Ma * s ^ 19 := by
        rw [ht_eq]; field_simp
      have e3 : s ^ 19 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
      have e4 : ν * C₁ * Ma * s ^ 19 ≤ ν * C₁ * Ma * s :=
        mul_le_mul_of_nonneg_left e3 (by positivity)
      linarith
    have hB' : t * (Cq * (2 * (2 * d) / v ^ 3) / L) ≤ 1 / 4 := by
      have h0 : 0 ≤ Cq * (2 * (2 * d) / v ^ 3) / L := by positivity
      have := mul_le_mul ht1 (herr2.trans hKm2) h0 zero_le_one
      linarith
    calc t * ‖gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k) ^ 2)‖
        ≤ t * (ν * (C₁ * Real.log (2 / v)) + Cq * (2 * (2 * d) / v ^ 3) / L) :=
          mul_le_mul_of_nonneg_left hc3 ht.le
      _ ≤ 1 / 2 := by rw [mul_add]; linarith
  · -- the absolute average
    have habs : gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) =
        gridAvgReal (fun k : Torus d L => ‖bandRes d β v (gridAngle k)‖) := by
      congr 1; funext k; rw [hLR k]
    rw [habs]
    have hpow : t ^ (-(1 / 5 : ℝ)) = (s ^ 4)⁻¹ := by
      rw [Real.rpow_neg ht.le, twentieth_pow ht]; norm_num
    rw [hpow]
    have h1 : Cq * (2 * d / v ^ 2) / L ≤ 1 := herr1.trans (hKm1.trans (min_le_right _ _))
    have h2 : ν * (C₁ * Real.log (2 / v)) ≤ ν * C₁ * Ma / s := by
      rw [← mul_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlogv (by positivity)
    have h3 : ν * C₁ * Ma / s + 1 ≤ (s ^ 4)⁻¹ := by
      rw [le_inv_comm₀ (by positivity) (by positivity)]
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      have e : s ^ 4 * (ν * C₁ * Ma / s + 1) = ν * C₁ * Ma * s ^ 3 + s ^ 4 := by
        field_simp
      rw [e]
      have e3 : s ^ 3 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
      have e4 : s ^ 4 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
      have e5 : ν * C₁ * Ma * s ^ 3 ≤ ν * C₁ * Ma * s := mul_le_mul_of_nonneg_left e3 (by positivity)
      linarith
    linarith
  · -- the symbol
    intro ζ
    have hpow : t ^ (1 / 2 : ℝ) = s ^ 10 := by rw [twentieth_pow ht]; norm_num
    rw [hpow]
    by_cases hsmall : ∀ j, |gridAngle ζ j| ≤ η
    · have h := hSm t ht htts L hL4 hLe hLbig E hE1 hE2 r ⟨hrre, hrim1, hrim2⟩ ζ hsmall
      have hCsM : Cs * M ≤ K := by
        have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
          Cl * M ^ 2 := by positivity
        linarith
      calc t * ‖gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k))‖
          ≤ t * (Cs * (M / s)) := by
            apply mul_le_mul_of_nonneg_left (h.trans _) ht.le
            exact mul_le_mul_of_nonneg_left hlogt hCs.le
        _ = Cs * M * s ^ 9 * s ^ 10 := by rw [ht_eq]; field_simp
        _ ≤ δ * s ^ 10 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have e : s ^ 9 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
            have : Cs * M * s ^ 9 ≤ Cs * M * s := mul_le_mul_of_nonneg_left e (by positivity)
            have : Cs * M * s ≤ K * s := mul_le_mul_of_nonneg_right hCsM hs0.le
            linarith
    · push Not at hsmall
      obtain ⟨j, hj⟩ := hsmall
      have h := hLg t ht httl L hL4 hLe hLbig E hE1 hE2 r ⟨hrre, hrim1, hrim2⟩ ζ ⟨j, hj.le⟩
      have hClM : Cl * M ^ 2 ≤ K := by
        have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
          Cs * M := by positivity
        linarith
      have hn : ‖gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k))‖
          ≤ Cl * Real.log (2 / t) ^ 2 := by
        refine (norm_gridAvg_le _).trans (le_trans (le_of_eq ?_) h)
        congr 1; funext k; rw [norm_mul]
      have hlog2 : Real.log (2 / t) ^ 2 ≤ (M / s) ^ 2 := pow_le_pow_left₀ hlogt0 hlogt 2
      calc t * ‖gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k))‖
          ≤ t * (Cl * (M / s) ^ 2) := by
            apply mul_le_mul_of_nonneg_left (hn.trans _) ht.le
            exact mul_le_mul_of_nonneg_left hlog2 hCl.le
        _ = Cl * M ^ 2 * s ^ 8 * s ^ 10 := by rw [ht_eq]; field_simp
        _ ≤ δ * s ^ 10 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have e : s ^ 8 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
            have : Cl * M ^ 2 * s ^ 8 ≤ Cl * M ^ 2 * s := mul_le_mul_of_nonneg_left e (by positivity)
            have : Cl * M ^ 2 * s ≤ K * s := mul_le_mul_of_nonneg_right hClM hs0.le
            linarith


set_option maxHeartbeats 2000000 in
/-- **Grid bounds for every window edge `w`.** -/
theorem gridBoundsW_of_helpers (hQ : PeriodicGridQuadratureStatement)
    (hB : BottomResolventStatement) (hS : SmallSymbolWStatement) (hLS : LargeSymbolWStatement) :
    GridBoundsWStatement := by
  intro d hd w hw
  set bw : ℝ := min (w / 2) (1 / 800) with hbw
  have hbw0 : 0 < bw := lt_min (by positivity) (by norm_num)
  have hbw1 : bw ≤ w / 2 := min_le_left _ _
  have hbw2 : bw ≤ 1 / 800 := min_le_right _ _
  obtain ⟨Cq, C₁, c₁, hCq, hC₁, hc₁, hcore⟩ := scalar_core hQ hB hd (β₁ := bw)
    hbw0 (by linarith)
  set ν : ℝ := ((2 * Real.pi) ^ d)⁻¹ with hνdef
  have hν : 0 < ν := by positivity
  set a₀ : ℝ := ν * c₁ / 2 with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  set B : ℝ := ν * C₁ + 1 + a₀ with hBdef
  have hB0 : 0 < B := by positivity
  have haB : a₀ ≤ B := by
    have : 0 ≤ ν * C₁ := by positivity
    linarith
  refine ⟨a₀, B, ha₀, haB, ?_⟩
  intro δ hδ
  obtain ⟨η, Cs, ts, hη, hCs, hts, hSm⟩ := hS d hd w hw a₀ B ha₀ haB
  obtain ⟨Cl, tl, hCl, htl, hLg⟩ := hLS d hd w hw a₀ B ha₀ haB η hη
  set Ma : ℝ := 20 * (2 / a₀) ^ (1 / 20 : ℝ) with hMa
  set M : ℝ := 20 * (2 : ℝ) ^ (1 / 20 : ℝ) with hM
  have hMa0 : 0 < Ma := by positivity
  have hM0 : 0 < M := by positivity
  set K : ℝ := Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
    Cs * M + Cl * M ^ 2 + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
      Cs * M + Cl * M ^ 2 := by positivity
    linarith
  have hK0 : 0 < K := by linarith
  set m₀ : ℝ := min (min a₀ 1) (min (1 / 4) δ) with hm₀
  have hm₀pos : 0 < m₀ := lt_min (lt_min ha₀ one_pos) (lt_min (by norm_num) hδ)
  set s₀ : ℝ := min (1 / 2) (m₀ / K) with hs₀
  have hs₀pos : 0 < s₀ := lt_min (by norm_num) (by positivity)
  refine ⟨min (s₀ ^ 20) (min ts (min tl (bw / B))), by positivity, ?_⟩
  intro t ht htt₀ L _ hL4 hLe hLbig E hE1 hE2 r hr
  have htts : t ≤ ts := htt₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have httl : t ≤ tl := htt₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have htB : t ≤ bw / B := htt₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have htB' : t * B ≤ bw := by
    rw [le_div_iff₀ (by positivity)] at htB; linarith
  -- s = t^{1/20}
  set s : ℝ := t ^ (1 / 20 : ℝ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos ht _
  have hss₀ : s ≤ s₀ := by
    have h := Real.rpow_le_rpow ht.le (htt₀.trans (min_le_left _ _)) (by norm_num : (0 : ℝ) ≤ 1 / 20)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hs₀pos.le, show ((20 : ℕ) : ℝ) * (1 / 20) = 1 by
      norm_num, Real.rpow_one] at h
  have hs_half : s ≤ 1 / 2 := hss₀.trans (min_le_left _ _)
  have hs1 : s ≤ 1 := by linarith
  have hKs : K * s ≤ m₀ := by
    have := hss₀.trans (min_le_right _ _)
    rw [le_div_iff₀ hK0] at this; linarith
  have ht_eq : t = s ^ 20 := by
    rw [twentieth_pow ht]; norm_num
  have ht1 : t ≤ 1 := by rw [ht_eq]; exact pow_le_one₀ hs0.le hs1
  have hts_le : t ≤ s := by
    rw [ht_eq]; exact pow_le_of_le_one hs0.le hs1 (by norm_num)
  -- the parameters of the resolvent
  have hrim : 0 < r.im := rectangle_im_pos ha₀ hr
  obtain ⟨hrre, hrim1, hrim2⟩ := hr
  set β : ℝ := E + 2 * d + t * r.re with hβ
  set v : ℝ := t * r.im with hv
  have hv0 : 0 < v := mul_pos ht hrim
  have hva : a₀ * t ≤ v := by rw [hv, mul_comm]; exact mul_le_mul_of_nonneg_left hrim1 ht.le
  have hvB : v ≤ t * B := by rw [hv]; exact mul_le_mul_of_nonneg_left hrim2 ht.le
  have hv1 : v ≤ 1 := by linarith
  have hre : |t * r.re| ≤ bw := by
    rw [abs_mul, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hrre ht.le).trans htB'
  have hβ1 : bw ≤ β := by have := (abs_le.mp hre).1; linarith
  have hβ2 : β ≤ 3 / 200 := by have := (abs_le.mp hre).2; linarith
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcore L hL4 hLe β v hβ1 hβ2 hv0 hv1
  have hLR : ∀ k : Torus d L, gridResolvent E t r k = bandRes d β v (gridAngle k) :=
    fun k => gridResolvent_eq_bandRes E t r k
  -- error terms
  have herr1 : Cq * (2 * d / v ^ 2) / L ≤ K * s := by
    have h := err_le (k := 2) (c := 2 * (d : ℝ)) (by norm_num) hCq.le (by positivity) ha₀ ht ht1
      hva hLbig
    have : Cq * (2 * d) / a₀ ^ 2 * t ≤ Cq * (2 * d) / a₀ ^ 2 * s :=
      mul_le_mul_of_nonneg_left hts_le (by positivity)
    have hle : Cq * (2 * d) / a₀ ^ 2 ≤ K := by
      have : 0 ≤ ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 + Cs * M + Cl * M ^ 2 := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right hle hs0.le
    linarith
  have herr2 : Cq * (2 * (2 * d) / v ^ 3) / L ≤ K * s := by
    have h := err_le (k := 3) (c := 2 * (2 * (d : ℝ))) (by norm_num) hCq.le (by positivity) ha₀
      ht ht1 hva hLbig
    have : Cq * (2 * (2 * d)) / a₀ ^ 3 * t ≤ Cq * (2 * (2 * d)) / a₀ ^ 3 * s :=
      mul_le_mul_of_nonneg_left hts_le (by positivity)
    have hle : Cq * (2 * (2 * d)) / a₀ ^ 3 ≤ K := by
      have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cs * M + Cl * M ^ 2 := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right hle hs0.le
    linarith
  have hKm1 : K * s ≤ min a₀ 1 := hKs.trans (min_le_left _ _)
  have hKm2 : K * s ≤ 1 / 4 := hKs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hKm3 : K * s ≤ δ := hKs.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- logarithms
  have hlogv : Real.log (2 / v) ≤ Ma / s := by
    have h1 : Real.log (2 / v) ≤ Real.log ((2 / a₀) / t) := by
      apply Real.log_le_log (by positivity)
      rw [div_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hva
    exact h1.trans (log_le_twentieth (c := 2 / a₀) (by positivity) ht)
  have hlogt : Real.log (2 / t) ≤ M / s := by
    exact log_le_twentieth (c := 2) (by norm_num) ht
  have hlogt0 : 0 ≤ Real.log (2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hlogv0 : 0 ≤ Real.log (2 / v) := Real.log_nonneg (by rw [le_div_iff₀ hv0]; linarith)
  have hνC : ν * C₁ * Ma ≤ K := by
    have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + Cq * (2 * (2 * d)) / a₀ ^ 3 + Cs * M + Cl * M ^ 2 := by
      positivity
    linarith
  have hsMa : ν * C₁ * Ma * s ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hνC hs0.le).trans hKm2
  have hscalar : scalarMap (d := d) (L := L) E t r =
      gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k)) := by
    unfold scalarMap; congr 1; funext k; exact hLR k
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the rectangle is preserved
    rw [hscalar]
    set Φ := gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k))
    have hΦ : ‖Φ‖ ≤ B := by
      have := hc2
      have h1 : Cq * (2 * d / v ^ 2) / L ≤ 1 := herr1.trans (hKm1.trans (min_le_right _ _))
      linarith
    refine ⟨(Complex.abs_re_le_norm Φ).trans hΦ, ?_, (le_abs_self _).trans
      ((Complex.abs_im_le_norm Φ).trans hΦ)⟩
    have h1 : Cq * (2 * d / v ^ 2) / L ≤ a₀ := herr1.trans (hKm1.trans (min_le_left _ _))
    have : ν * c₁ = 2 * a₀ := by rw [ha₀def]; ring
    linarith
  · -- the contraction constant
    have hsq : gridAvg (fun k : Torus d L => gridResolvent E t r k ^ 2) =
        gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k) ^ 2) := by
      congr 1; funext k; rw [hLR k]
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hA : t * (ν * (C₁ * Real.log (2 / v))) ≤ 1 / 4 := by
      have e1 : t * (ν * (C₁ * Real.log (2 / v))) ≤ t * (ν * C₁ * (Ma / s)) := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hlogv (by positivity)
      have e2 : t * (ν * C₁ * (Ma / s)) = ν * C₁ * Ma * s ^ 19 := by
        rw [ht_eq]; field_simp
      have e3 : s ^ 19 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
      have e4 : ν * C₁ * Ma * s ^ 19 ≤ ν * C₁ * Ma * s :=
        mul_le_mul_of_nonneg_left e3 (by positivity)
      linarith
    have hB' : t * (Cq * (2 * (2 * d) / v ^ 3) / L) ≤ 1 / 4 := by
      have h0 : 0 ≤ Cq * (2 * (2 * d) / v ^ 3) / L := by positivity
      have := mul_le_mul ht1 (herr2.trans hKm2) h0 zero_le_one
      linarith
    calc t * ‖gridAvg (fun k : Torus d L => bandRes d β v (gridAngle k) ^ 2)‖
        ≤ t * (ν * (C₁ * Real.log (2 / v)) + Cq * (2 * (2 * d) / v ^ 3) / L) :=
          mul_le_mul_of_nonneg_left hc3 ht.le
      _ ≤ 1 / 2 := by rw [mul_add]; linarith
  · -- the absolute average
    have habs : gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖) =
        gridAvgReal (fun k : Torus d L => ‖bandRes d β v (gridAngle k)‖) := by
      congr 1; funext k; rw [hLR k]
    rw [habs]
    have hpow : t ^ (-(1 / 5 : ℝ)) = (s ^ 4)⁻¹ := by
      rw [Real.rpow_neg ht.le, twentieth_pow ht]; norm_num
    rw [hpow]
    have h1 : Cq * (2 * d / v ^ 2) / L ≤ 1 := herr1.trans (hKm1.trans (min_le_right _ _))
    have h2 : ν * (C₁ * Real.log (2 / v)) ≤ ν * C₁ * Ma / s := by
      rw [← mul_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlogv (by positivity)
    have h3 : ν * C₁ * Ma / s + 1 ≤ (s ^ 4)⁻¹ := by
      rw [le_inv_comm₀ (by positivity) (by positivity)]
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      have e : s ^ 4 * (ν * C₁ * Ma / s + 1) = ν * C₁ * Ma * s ^ 3 + s ^ 4 := by
        field_simp
      rw [e]
      have e3 : s ^ 3 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
      have e4 : s ^ 4 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
      have e5 : ν * C₁ * Ma * s ^ 3 ≤ ν * C₁ * Ma * s := mul_le_mul_of_nonneg_left e3 (by positivity)
      linarith
    linarith
  · -- the symbol
    intro ζ
    have hpow : t ^ (1 / 2 : ℝ) = s ^ 10 := by rw [twentieth_pow ht]; norm_num
    rw [hpow]
    by_cases hsmall : ∀ j, |gridAngle ζ j| ≤ η
    · have h := hSm t ht htts L hL4 hLe hLbig E hE1 hE2 r ⟨hrre, hrim1, hrim2⟩ ζ hsmall
      have hCsM : Cs * M ≤ K := by
        have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
          Cl * M ^ 2 := by positivity
        linarith
      calc t * ‖gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k))‖
          ≤ t * (Cs * (M / s)) := by
            apply mul_le_mul_of_nonneg_left (h.trans _) ht.le
            exact mul_le_mul_of_nonneg_left hlogt hCs.le
        _ = Cs * M * s ^ 9 * s ^ 10 := by rw [ht_eq]; field_simp
        _ ≤ δ * s ^ 10 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have e : s ^ 9 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
            have : Cs * M * s ^ 9 ≤ Cs * M * s := mul_le_mul_of_nonneg_left e (by positivity)
            have : Cs * M * s ≤ K * s := mul_le_mul_of_nonneg_right hCsM hs0.le
            linarith
    · push Not at hsmall
      obtain ⟨j, hj⟩ := hsmall
      have h := hLg t ht httl L hL4 hLe hLbig E hE1 hE2 r ⟨hrre, hrim1, hrim2⟩ ζ ⟨j, hj.le⟩
      have hClM : Cl * M ^ 2 ≤ K := by
        have : 0 ≤ Cq * (2 * d) / a₀ ^ 2 + ν * C₁ * Ma + Cq * (2 * (2 * d)) / a₀ ^ 3 +
          Cs * M := by positivity
        linarith
      have hn : ‖gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k))‖
          ≤ Cl * Real.log (2 / t) ^ 2 := by
        refine (norm_gridAvg_le _).trans (le_trans (le_of_eq ?_) h)
        congr 1; funext k; rw [norm_mul]
      have hlog2 : Real.log (2 / t) ^ 2 ≤ (M / s) ^ 2 := pow_le_pow_left₀ hlogt0 hlogt 2
      calc t * ‖gridAvg (fun k : Torus d L => gridResolvent E t r k * gridResolvent E t r (ζ - k))‖
          ≤ t * (Cl * (M / s) ^ 2) := by
            apply mul_le_mul_of_nonneg_left (hn.trans _) ht.le
            exact mul_le_mul_of_nonneg_left hlog2 hCl.le
        _ = Cl * M ^ 2 * s ^ 8 * s ^ 10 := by rw [ht_eq]; field_simp
        _ ≤ δ * s ^ 10 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have e : s ^ 8 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
            have : Cl * M ^ 2 * s ^ 8 ≤ Cl * M ^ 2 * s := mul_le_mul_of_nonneg_left e (by positivity)
            have : Cl * M ^ 2 * s ≤ K * s := mul_le_mul_of_nonneg_right hClM hs0.le
            linarith

end AndersonAC.S3
