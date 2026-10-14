import AndersonAC.S3.HelperStatements2

/-! Transfer the sliced joint-shell bound to the original frequency coordinates. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace AndersonAC.S3

private theorem arcsin_lipschitzOn_quarter :
    LipschitzOnWith (2 : ℝ≥0) Real.arcsin (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
  apply (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    apply Real.differentiableAt_arcsin.mpr
    constructor
    · intro h
      have h' := hx.1
      rw [h] at h'
      norm_num at h'
    · intro h
      have h' := hx.2
      rw [h] at h'
      norm_num at h'
  · intro x hx
    simp only [Real.deriv_arcsin]
    have hxabs : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr hx
    have hxlo : -(1 / 4 : ℝ) ≤ x := hx.1
    have hxhi : x ≤ (1 / 4 : ℝ) := hx.2
    have hx2 : x ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith
    have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - x ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hder : |1 / Real.sqrt (1 - x ^ 2)| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    exact_mod_cast hder

private theorem arcsinMap_lipschitzOn {d : ℕ} (S : Set (Frequency d))
    (hS : ∀ x ∈ S, ∀ j, |x j| ≤ 1 / 4) :
    LipschitzOnWith (2 : ℝ≥0) (fun x : Frequency d => fun j => Real.arcsin (x j)) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  apply (dist_pi_le_iff (by positivity)).2
  intro j
  have hxj : x j ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) := abs_le.mp (hS x hx j)
  have hyj : y j ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) := abs_le.mp (hS y hy j)
  calc
    dist (Real.arcsin (x j)) (Real.arcsin (y j)) ≤ (2 : ℝ) * dist (x j) (y j) :=
      arcsin_lipschitzOn_quarter.dist_le_mul (x j) hxj (y j) hyj
    _ ≤ (2 : ℝ) * dist x y := by
      exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y j) (by positivity)

private theorem dispersion_sliced_minus {d : ℕ} (ζ θ : Frequency d)
    (hθ : ∀ j, |θ j| ≤ 21 / 100) :
    dispersion (θ - ζ / 2) =
      slicedDispersion (-1) ζ (fun j => Real.sin (θ j)) := by
  have hcos (j : Fin d) :
      Real.cos (θ j) = Real.sqrt (1 - Real.sin (θ j) ^ 2) := by
    apply Real.cos_eq_sqrt_one_sub_sin_sq
    · have h' := abs_le.mp (hθ j)
      nlinarith [Real.pi_gt_three]
    · have h' := abs_le.mp (hθ j)
      nlinarith [Real.pi_gt_three]
  have hcoord (j : Fin d) :
      -2 * Real.cos (θ j - ζ j / 2) =
        -2 * (Real.cos (ζ j / 2) * Real.sqrt (1 - Real.sin (θ j) ^ 2)) -
          2 * (Real.sin (ζ j / 2) * Real.sin (θ j)) := by
    rw [Real.cos_sub, hcos j]
    ring
  unfold dispersion slicedDispersion
  calc
    -2 * ∑ j, Real.cos ((θ - ζ / 2) j) =
        ∑ j, (-2 * Real.cos (θ j - ζ j / 2)) := by
          simp [Pi.sub_apply, Pi.div_apply, Finset.mul_sum]
    _ = ∑ j,
        (-2 * (Real.cos (ζ j / 2) * Real.sqrt (1 - Real.sin (θ j) ^ 2)) -
          2 * (Real.sin (ζ j / 2) * Real.sin (θ j))) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcoord j
    _ = -2 * (∑ j, Real.cos (ζ j / 2) * Real.sqrt (1 - Real.sin (θ j) ^ 2)) -
          2 * (∑ j, Real.sin (ζ j / 2) * Real.sin (θ j)) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = slicedDispersion (-1) ζ (fun j => Real.sin (θ j)) := by
          simp only [slicedDispersion]
          ring

private theorem dispersion_sliced_plus {d : ℕ} (ζ θ : Frequency d)
    (hθ : ∀ j, |θ j| ≤ 21 / 100) :
    dispersion (θ + ζ / 2) =
      slicedDispersion 1 ζ (fun j => Real.sin (θ j)) := by
  have hcos (j : Fin d) :
      Real.cos (θ j) = Real.sqrt (1 - Real.sin (θ j) ^ 2) := by
    apply Real.cos_eq_sqrt_one_sub_sin_sq
    · have h' := abs_le.mp (hθ j)
      nlinarith [Real.pi_gt_three]
    · have h' := abs_le.mp (hθ j)
      nlinarith [Real.pi_gt_three]
  have hcoord (j : Fin d) :
      -2 * Real.cos (θ j + ζ j / 2) =
        -2 * (Real.cos (ζ j / 2) * Real.sqrt (1 - Real.sin (θ j) ^ 2)) +
          2 * (Real.sin (ζ j / 2) * Real.sin (θ j)) := by
    rw [Real.cos_add, hcos j]
    ring
  unfold dispersion slicedDispersion
  calc
    -2 * ∑ j, Real.cos ((θ + ζ / 2) j) =
        ∑ j, (-2 * Real.cos (θ j + ζ j / 2)) := by
          simp [Pi.add_apply, Pi.div_apply, Finset.mul_sum]
    _ = ∑ j,
        (-2 * (Real.cos (ζ j / 2) * Real.sqrt (1 - Real.sin (θ j) ^ 2)) +
          2 * (Real.sin (ζ j / 2) * Real.sin (θ j))) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcoord j
    _ = -2 * (∑ j, Real.cos (ζ j / 2) * Real.sqrt (1 - Real.sin (θ j) ^ 2)) +
          2 * (∑ j, Real.sin (ζ j / 2) * Real.sin (θ j)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = slicedDispersion 1 ζ (fun j => Real.sin (θ j)) := by
          simp [slicedDispersion]

private theorem theta_bound {d : ℕ} {k ζ : Frequency d}
    (hk : ∀ j, |k j| ≤ 21 / 100)
    (hkζ : ∀ j, |k j + ζ j| ≤ 21 / 100) :
    ∀ j, |(k + ζ / 2) j| ≤ 21 / 100 := by
  intro j
  have hrepr : (k + ζ / 2) j = (k j + (k j + ζ j)) / 2 := by
    simp [Pi.add_apply, Pi.div_apply]
    ring
  rw [hrepr, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htriangle := abs_add_le (k j) (k j + ζ j)
  have hsum := add_le_add (hk j) (hkζ j)
  nlinarith

theorem jointShellK_of_X_proof : JointShellXStatement → JointShellKStatement := by
  intro hX d hd
  have hdim : (d - 1) + 1 = d := by omega
  obtain ⟨C, hC, hX⟩ := hX (d - 1) (by omega)
  have hX' : ∀ ζ : Frequency d, (∀ j, |ζ j| ≤ 1 / 2) →
      ∀ j₀ : Fin d, ζ j₀ ≠ 0 → ∀ E s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ →
      volume {x : Frequency d | (∀ j, |x j| ≤ 1 / 4) ∧
          |slicedDispersion (-1) ζ x - E| ≤ s₁ ∧
          |slicedDispersion 1 ζ x - E| ≤ s₂} ≤
        ENNReal.ofReal (C * s₁ * s₂ / |ζ j₀|) := by
    rw [← hdim]
    exact hX
  refine ⟨(2 : ℝ) ^ d * C, by positivity, ?_⟩
  intro ζ j₀ hj₀ E s₁ s₂ hs₁ hs₂
  let A : Set (Frequency d) := {k | (∀ j, |k j| ≤ 21 / 100) ∧
    (∀ j, |k j + ζ j| ≤ 21 / 100) ∧
    |dispersion k - E| ≤ s₁ ∧ |dispersion (k + ζ) - E| ≤ s₂}
  let T : Frequency d → Frequency d := fun k => k + ζ / 2
  let F : Frequency d → Frequency d := fun x j => Real.arcsin (x j)
  let S : Set (Frequency d) := {x | (∀ j, |x j| ≤ 1 / 4) ∧
    |slicedDispersion (-1) ζ x - E| ≤ s₁ ∧ |slicedDispersion 1 ζ x - E| ≤ s₂}
  by_cases hAempty : A = ∅
  · simp [A, hAempty]
  · have ⟨k₀, hk₀⟩ : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
    have hζ : ∀ j, |ζ j| ≤ 1 / 2 := by
      intro j
      have h := hk₀.1 j
      have h' := hk₀.2.1 j
      have hid : ζ j = (k₀ j + ζ j) - k₀ j := by ring
      calc
        |ζ j| = |(k₀ j + ζ j) - k₀ j| := congrArg abs hid
        _ ≤ |k₀ j + ζ j| + |k₀ j| := abs_sub _ _
        _ ≤ 21 / 100 + 21 / 100 := add_le_add h' h
        _ ≤ 1 / 2 := by norm_num
    have hSbound (x : Frequency d) (hx : x ∈ S) : ∀ j, |x j| ≤ 1 / 4 := hx.1
    have hLip : LipschitzOnWith (2 : ℝ≥0) F S := by
      apply arcsinMap_lipschitzOn S hSbound
    have hLipVol : volume (F '' S) ≤ (2 : ℝ≥0∞) ^ d * volume S := by
      have h := hLip.hausdorffMeasure_image_le (d := (d : ℝ)) (by positivity)
      have hcard : (Fintype.card (Fin d) : ℝ) = d := by simp
      rw [← hcard] at h
      rw [hausdorffMeasure_pi_real] at h
      rw [ENNReal.rpow_natCast] at h
      norm_num at h ⊢
      exact h
    have hAmeas : MeasurableSet A := by
      have hbox : MeasurableSet {k : Frequency d | ∀ j, |k j| ≤ 21 / 100} := by
        have heq : {k : Frequency d | ∀ j, |k j| ≤ 21 / 100} =
            ⋂ j : Fin d, (fun k : Frequency d => k j) ⁻¹' Set.Icc (-(21 / 100 : ℝ)) (21 / 100) := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc, abs_le]
        rw [heq]
        exact MeasurableSet.iInter fun j => isClosed_Icc.measurableSet.preimage
          (measurable_pi_apply j)
      have hboxζ : MeasurableSet {k : Frequency d | ∀ j, |k j + ζ j| ≤ 21 / 100} := by
        have heq : {k : Frequency d | ∀ j, |k j + ζ j| ≤ 21 / 100} =
            ⋂ j : Fin d, (fun k : Frequency d => k j) ⁻¹'
              Set.Icc (-(21 / 100 : ℝ) - ζ j) (21 / 100 - ζ j) := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc, abs_le]
          constructor
          · intro h j
            have hj := h j
            constructor <;> linarith
          · intro h j
            have hj := h j
            constructor <;> linarith
        rw [heq]
        exact MeasurableSet.iInter fun j => isClosed_Icc.measurableSet.preimage
          (measurable_pi_apply j)
      have hcont : Continuous (dispersion : Frequency d → ℝ) := by
        unfold dispersion
        fun_prop
      have hcontζ : Continuous (fun k : Frequency d => dispersion (k + ζ)) := by
        fun_prop
      have hdisp (s : ℝ) : MeasurableSet {k : Frequency d | |dispersion k - E| ≤ s} := by
        have heq : {k : Frequency d | |dispersion k - E| ≤ s} =
            dispersion ⁻¹' Set.Icc (E - s) (E + s) := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
          constructor <;> intro h <;> constructor <;> linarith
        rw [heq]
        exact isClosed_Icc.measurableSet.preimage hcont.measurable
      have hdispζ (s : ℝ) :
          MeasurableSet {k : Frequency d | |dispersion (k + ζ) - E| ≤ s} := by
        have heq : {k : Frequency d | |dispersion (k + ζ) - E| ≤ s} =
            (fun k : Frequency d => dispersion (k + ζ)) ⁻¹' Set.Icc (E - s) (E + s) := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
          constructor <;> intro h <;> constructor <;> linarith
        rw [heq]
        exact isClosed_Icc.measurableSet.preimage hcontζ.measurable
      have hAeq : A = {k | ∀ j, |k j| ≤ 21 / 100} ∩
          ({k | ∀ j, |k j + ζ j| ≤ 21 / 100} ∩
            ({k | |dispersion k - E| ≤ s₁} ∩ {k | |dispersion (k + ζ) - E| ≤ s₂})) := by
        ext k
        simp [A]
      rw [hAeq]
      exact hbox.inter (hboxζ.inter ((hdisp s₁).inter (hdispζ s₂)))
    have hpre : (fun y : Frequency d => y - ζ / 2) ⁻¹' A = T '' A := by
      ext y
      change y - ζ / 2 ∈ A ↔ ∃ k, k ∈ A ∧ T k = y
      constructor
      · intro hy
        refine ⟨y - ζ / 2, hy, ?_⟩
        ext j
        simp [T]
      · rintro ⟨k, hk, hky⟩
        have hyk : y - ζ / 2 = k := by
          rw [← hky]
          ext j
          simp [T]
        simpa [hyk] using hk
    have htrans : volume (T '' A) = volume A := by
      rw [← hpre]
      simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right (volume : Measure (Frequency d)) (-(ζ / 2))).measure_preimage
          hAmeas.nullMeasurableSet
    have hsubset : T '' A ⊆ F '' S := by
      rintro y ⟨k, hk, rfl⟩
      let θ : Frequency d := T k
      let x : Frequency d := fun j => Real.sin (θ j)
      have hθ : ∀ j, |θ j| ≤ 21 / 100 := by
        intro j
        simpa [θ, T] using theta_bound hk.1 hk.2.1 j
      have hx : x ∈ S := by
        refine ⟨?_, ?_, ?_⟩
        · intro j
          dsimp [x]
          calc
            |Real.sin (θ j)| ≤ |θ j| := Real.abs_sin_le_abs
            _ ≤ 21 / 100 := hθ j
            _ ≤ 1 / 4 := by norm_num
        · have hkEq : k = θ - ζ / 2 := by
            ext j
            simp [θ, T]
          have hdisp := dispersion_sliced_minus ζ θ hθ
          rw [← hkEq] at hdisp
          have henergy := hk.2.2.1
          rw [hdisp] at henergy
          simpa [x] using henergy
        · have hkζEq : k + ζ = θ + ζ / 2 := by
            ext j
            simp [θ, T]
            ring
          have hdisp := dispersion_sliced_plus ζ θ hθ
          rw [← hkζEq] at hdisp
          have henergy := hk.2.2.2
          rw [hdisp] at henergy
          simpa [x] using henergy
      refine ⟨x, hx, ?_⟩
      funext j
      change Real.arcsin (Real.sin (θ j)) = θ j
      have hj := abs_le.mp (hθ j)
      exact Real.arcsin_sin
        (by nlinarith [Real.pi_gt_three])
        (by nlinarith [Real.pi_gt_three])
    have hXbound := hX' ζ hζ j₀ hj₀ E s₁ s₂ hs₁ hs₂
    have hvolX : volume S ≤ ENNReal.ofReal (C * s₁ * s₂ / |ζ j₀|) := by
      simpa [S] using hXbound
    calc
      volume A = volume (T '' A) := htrans.symm
      _ ≤ volume (F '' S) := measure_mono hsubset
      _ ≤ (2 : ℝ≥0∞) ^ d * volume S := hLipVol
      _ ≤ (2 : ℝ≥0∞) ^ d * ENNReal.ofReal (C * s₁ * s₂ / |ζ j₀|) :=
        by gcongr
      _ = ENNReal.ofReal ((2 : ℝ) ^ d * C * s₁ * s₂ / |ζ j₀|) := by
        have hpow : (2 : ℝ≥0∞) ^ d = ENNReal.ofReal ((2 : ℝ) ^ d) := by norm_num
        rw [hpow, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ d)]
        congr 1
        ring

end AndersonAC.S3
