import AndersonAC.S9Inf.VolumeErrorStatement

/-! Quantitative decay of the finite/infinite volume comparison error. -/

noncomputable section

open Filter OAI.Anderson
open scoped Topology

namespace AndersonAC.SolS9Inf

private lemma sideLength_real (m : ℕ) :
    (sideLength m : ℝ) = ((4 : ℝ) ^ m) ^ 20 := by
  calc
    (sideLength m : ℝ) = (4 : ℝ) ^ (20 * m) := by simp [sideLength]
    _ = (4 : ℝ) ^ (m * 20) := by congr 1; omega
    _ = ((4 : ℝ) ^ m) ^ 20 := by rw [pow_mul]

private lemma tendsto_four_pow :
    Tendsto (fun m : ℕ => (4 : ℝ) ^ m) atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).comp
    tendsto_natCast_atTop_atTop

theorem volumeComparisonError_proof : VolumeComparisonErrorStatement := by
  intro d η hη C c hc
  rcases hη with ⟨hηpos, a, b, ha, hb, hηevent⟩
  let D : ℕ := d - 1
  let P : ℕ := 20 * D + 2
  let lam : ℝ := c * a
  let q : ℕ → ℝ := fun m => (4 : ℝ) ^ m
  let z : ℕ → ℝ := fun m => q m ^ 19
  let x : ℕ → ℝ := fun m => lam * z m
  let K : ℝ := |C| * (a ^ 2)⁻¹ * (lam⁻¹) ^ P
  let hlam : 0 < lam := mul_pos hc ha
  have hqpos (m : ℕ) : 0 < q m := by positivity
  have hqone (m : ℕ) : 1 ≤ q m := by
    dsimp [q]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
  have hside (m : ℕ) : (sideLength m : ℝ) = q m ^ 20 := by
    simpa [q] using sideLength_real m
  have hqtop : Tendsto q atTop atTop := by
    simpa [q] using tendsto_four_pow
  have hqz (m : ℕ) : q m ≤ z m := by
    dsimp [z]
    calc
      q m = q m ^ 1 := by simp
      _ ≤ q m ^ 19 := by exact pow_le_pow_right₀ (hqone m) (by norm_num)
  have hztop : Tendsto z atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hqtop
    exact Eventually.of_forall hqz
  have hxtop : Tendsto x atTop atTop := by
    simpa [x, lam] using hztop.const_mul_atTop hlam
  have hdecay : Tendsto (fun m => x m ^ P * Real.exp (-x m)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero P).comp hxtop
  have hdom : Tendsto (fun m => K * (x m ^ P * Real.exp (-x m))) atTop (𝓝 0) :=
    by simpa using tendsto_const_nhds.mul hdecay
  have hbound : ∀ᶠ m in atTop,
      |C * (sideLength m : ℝ) ^ D * (η m)⁻¹ ^ 2 *
        Real.exp (-c * η m * sideLength m)| ≤ K * (x m ^ P * Real.exp (-x m)) := by
    filter_upwards [hηevent] with m hm
    have hηlower : a / q m ≤ η m := by simpa [q] using hm.1
    have hηlowerpos : 0 < a / q m := div_pos ha (hqpos m)
    have hinv : (η m)⁻¹ ≤ q m / a := by
      have h := (inv_le_inv₀ (hηpos m) hηlowerpos).2 hηlower
      simpa only [inv_div] using h
    have hinv2 : (η m)⁻¹ ^ 2 ≤ (q m / a) ^ 2 :=
      (sq_le_sq₀ (inv_nonneg.mpr (le_of_lt (hηpos m)))
        (div_nonneg (le_of_lt (hqpos m)) (le_of_lt ha))).2 hinv
    have hpref :
        (sideLength m : ℝ) ^ D * (η m)⁻¹ ^ 2 ≤ (a ^ 2)⁻¹ * q m ^ P := by
      calc
        (sideLength m : ℝ) ^ D * (η m)⁻¹ ^ 2 ≤
            (sideLength m : ℝ) ^ D * (q m / a) ^ 2 :=
          mul_le_mul_of_nonneg_left hinv2 (by positivity)
        _ = (a ^ 2)⁻¹ * q m ^ P := by
          rw [hside, ← pow_mul, div_pow]
          simp only [div_eq_mul_inv]
          dsimp [P, D]
          calc
            q m ^ (20 * (d - 1)) * (q m ^ 2 * (a ^ 2)⁻¹) =
                (a ^ 2)⁻¹ * (q m ^ (20 * (d - 1)) * q m ^ 2) := by ring
            _ = (a ^ 2)⁻¹ * q m ^ (20 * (d - 1) + 2) := by rw [← pow_add]
    have hprod : a * z m ≤ η m * (sideLength m : ℝ) := by
      have hid : a * q m ^ 19 = (a / q m) * q m ^ 20 := by
        rw [show (20 : ℕ) = 19 + 1 by norm_num, pow_succ]
        field_simp [ne_of_gt ha, ne_of_gt (hqpos m)]
      calc
        a * z m = (a / q m) * q m ^ 20 := by simpa [z] using hid
        _ ≤ η m * q m ^ 20 := mul_le_mul_of_nonneg_right hηlower (by positivity)
        _ = η m * (sideLength m : ℝ) := by rw [hside]
    have harg : -c * η m * sideLength m ≤ -x m := by
      have hmul := mul_le_mul_of_nonneg_left hprod hc.le
      have hneg := neg_le_neg hmul
      simpa [x, lam, mul_assoc, mul_left_comm, mul_comm] using hneg
    have hexp : Real.exp (-c * η m * sideLength m) ≤ Real.exp (-x m) :=
      Real.exp_le_exp.mpr harg
    have habs :
        |C * (sideLength m : ℝ) ^ D * (η m)⁻¹ ^ 2 *
          Real.exp (-c * η m * sideLength m)| =
        |C| * ((sideLength m : ℝ) ^ D * (η m)⁻¹ ^ 2) *
          Real.exp (-c * η m * sideLength m) := by
      simp [abs_mul, abs_of_nonneg (by positivity :
        0 ≤ (sideLength m : ℝ) ^ D), abs_of_pos (Real.exp_pos _)]; ring
    calc
      _ = |C| * ((sideLength m : ℝ) ^ D * (η m)⁻¹ ^ 2) *
          Real.exp (-c * η m * sideLength m) := habs
      _ ≤ |C| * ((a ^ 2)⁻¹ * q m ^ P) * Real.exp (-x m) := by
        gcongr
      _ ≤ |C| * ((a ^ 2)⁻¹ * z m ^ P) * Real.exp (-x m) := by
        gcongr
        exact hqz m
      _ = K * (x m ^ P * Real.exp (-x m)) := by
        have hscale : z m ^ P = (lam⁻¹) ^ P * x m ^ P := by
          change z m ^ P = lam⁻¹ ^ P * (lam * z m) ^ P
          rw [mul_pow]
          have hcancel : lam⁻¹ ^ P * lam ^ P = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hlam.ne', one_pow]
          calc
            z m ^ P = 1 * z m ^ P := by simp
            _ = (lam⁻¹ ^ P * lam ^ P) * z m ^ P := by rw [hcancel]
            _ = lam⁻¹ ^ P * (lam ^ P * z m ^ P) := by ac_rfl
        dsimp [K]
        rw [hscale]
        ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hdom
  filter_upwards [hbound] with m hm
  simpa only [Real.norm_eq_abs] using hm

end AndersonAC.SolS9Inf
