import AndersonAC.S3.DirectGap
import AndersonAC.S3.ScalarEquation
import AndersonAC.S3.SymbolStatements

/-!
The two-sided gap of the conjugate symbol `F̂(ζ) = fSymbol E t r ζ` at every nonzero
grid frequency (§3, Proposition 3.6, lines 600–700):

* the exact identity `1 - Re F̂(ζ) = (t/2) gridAvg |R(k) - R(k+ζ)|²` at the fixed point;
* the upper bound `1 - Re F̂ ≤ C min(1, |θ|∞²/t²)`;
* the lower bound from `product_patch_grid_gap` at small frequencies and from the absolute
  product (`LargeSymbolDecayWStatement`) at the others.
-/

noncomputable section
open scoped BigOperators

namespace AndersonAC.S3

variable {d L : ℕ} [NeZero L]

theorem gridAvgReal_add_shift (f : Torus d L → ℝ) (ζ : Torus d L) :
    gridAvgReal (fun k => f (k + ζ)) = gridAvgReal f := by
  unfold gridAvgReal
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight ζ) _ _ (fun _ => rfl)

theorem gridAvgReal_add (f g : Torus d L → ℝ) :
    gridAvgReal (fun k => f k + g k) = gridAvgReal f + gridAvgReal g := by
  unfold gridAvgReal
  rw [Finset.sum_add_distrib]; ring

theorem gridAvgReal_sub (f g : Torus d L → ℝ) :
    gridAvgReal (fun k => f k - g k) = gridAvgReal f - gridAvgReal g := by
  unfold gridAvgReal
  rw [Finset.sum_sub_distrib]; ring

theorem gridAvg_re (f : Torus d L → ℂ) :
    (gridAvg f).re = gridAvgReal (fun k => (f k).re) := by
  unfold gridAvg gridAvgReal
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]

/-- The exact gap identity at the fixed point. -/
theorem fSymbol_gap_identity (hL : 4 ≤ L) {E t : ℝ} {r : ℂ} (ht : 0 < t) (hp : 0 < r.im)
    (hr : scalarMap (d := d) (L := L) E t r = r) (ζ : Torus d L) :
    1 - (fSymbol E t r ζ).re =
      t / 2 * gridAvgReal (fun k : Torus d L =>
        ‖gridResolvent E t r k - gridResolvent E t r (k + ζ)‖ ^ 2) := by
  have hn := initial_normalization (d := d) hL E t r ht hp hr
  set R := gridResolvent (d := d) (L := L) E t r
  have hexp : ∀ k, ‖R k - R (k + ζ)‖ ^ 2 =
      ‖R k‖ ^ 2 + ‖R (k + ζ)‖ ^ 2 - 2 * (R k * star (R (k + ζ))).re := by
    intro k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
    rfl
  have h1 : gridAvgReal (fun k => ‖R k - R (k + ζ)‖ ^ 2) =
      gridAvgReal (fun k => ‖R k‖ ^ 2) + gridAvgReal (fun k => ‖R (k + ζ)‖ ^ 2) -
        gridAvgReal (fun k => 2 * (R k * star (R (k + ζ))).re) := by
    simp_rw [hexp]
    rw [gridAvgReal_sub, gridAvgReal_add]
  rw [h1, gridAvgReal_add_shift (fun k => ‖R k‖ ^ 2) ζ, gridAvgReal_mul_left]
  unfold fSymbol
  rw [Complex.re_ofReal_mul, gridAvg_re]
  have : t * gridAvgReal (fun k => ‖R k‖ ^ 2) = 1 := hn
  nlinarith

/-- The conjugate symbol is bounded by one. -/
theorem fSymbol_norm_le (hL : 4 ≤ L) {E t : ℝ} {r : ℂ} (ht : 0 < t) (hp : 0 < r.im)
    (hr : scalarMap (d := d) (L := L) E t r = r) (ζ : Torus d L) :
    ‖fSymbol E t r ζ‖ ≤ 1 := by
  have hn := initial_normalization (d := d) hL E t r ht hp hr
  set R := gridResolvent (d := d) (L := L) E t r
  unfold fSymbol
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have h1 := norm_gridAvg_le (fun k => R k * star (R (k + ζ)))
  have h2 : gridAvgReal (fun k => ‖R k * star (R (k + ζ))‖) ≤
      gridAvgReal (fun k => (‖R k‖ ^ 2 + ‖R (k + ζ)‖ ^ 2) / 2) := by
    apply gridAvgReal_mono
    intro k
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖R k‖ - ‖R (k + ζ)‖)]
  have h3 : gridAvgReal (fun k => (‖R k‖ ^ 2 + ‖R (k + ζ)‖ ^ 2) / 2) =
      gridAvgReal (fun k => ‖R k‖ ^ 2) := by
    have e : (fun k => (‖R k‖ ^ 2 + ‖R (k + ζ)‖ ^ 2) / 2) =
        fun k => (1 / 2 : ℝ) * (‖R k‖ ^ 2 + ‖R (k + ζ)‖ ^ 2) := by funext k; ring
    rw [e, gridAvgReal_mul_left, gridAvgReal_add, gridAvgReal_add_shift (fun k => ‖R k‖ ^ 2) ζ]
    ring
  have : t * gridAvgReal (fun k => ‖R k‖ ^ 2) = 1 := hn
  calc t * ‖gridAvg (fun k => R k * star (R (k + ζ)))‖
      ≤ t * gridAvgReal (fun k => ‖R k * star (R (k + ζ))‖) :=
        mul_le_mul_of_nonneg_left h1 ht.le
    _ ≤ t * gridAvgReal (fun k => ‖R k‖ ^ 2) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 ht.le
    _ = 1 := this

/-- Upper bound of the gap: `1 - Re F̂ ≤ 2 d² s² / (t Im r)²` when all `|θ_j| ≤ s`. -/
theorem fSymbol_gap_upper (hL : 4 ≤ L) {E t : ℝ} {r : ℂ} (ht : 0 < t) (hp : 0 < r.im)
    (hr : scalarMap (d := d) (L := L) E t r = r) (ζ : Torus d L) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : ∀ j, |gridAngle ζ j| ≤ s) :
    1 - (fSymbol E t r ζ).re ≤ 2 * d ^ 2 * s ^ 2 / (t * r.im) ^ 2 := by
  have hn := initial_normalization (d := d) hL E t r ht hp hr
  rw [fSymbol_gap_identity hL ht hp hr]
  set v := t * r.im with hv
  have hv0 : 0 < v := mul_pos ht hp
  set β := E + 2 * d + t * r.re
  have hpt : ∀ k : Torus d L, ‖gridResolvent E t r k - gridResolvent E t r (k + ζ)‖ ^ 2 ≤
      (2 * d * s / v) ^ 2 * ‖gridResolvent E t r k‖ ^ 2 := by
    intro k
    rw [gridResolvent_eq_bandRes, gridResolvent_eq_bandRes, bandRes_gridAngle_add,
      bandRes_sub_norm hv0]
    have hD := abs_dispersion_add_sub_le (gridAngle k) (gridAngle ζ) s hs
    have hden2 : v ≤ ‖bandDen d β v (gridAngle k + gridAngle ζ)‖ := by
      have := Complex.abs_im_le_norm (bandDen d β v (gridAngle k + gridAngle ζ))
      have him : (bandDen d β v (gridAngle k + gridAngle ζ)).im = -v := by simp [bandDen]
      rwa [him, abs_neg, abs_of_pos hv0] at this
    have hden1 : 0 < ‖bandDen d β v (gridAngle k)‖ := norm_pos_iff.mpr (bandDen_ne hv0 _)
    have hR : ‖bandRes d β v (gridAngle k)‖ = ‖bandDen d β v (gridAngle k)‖⁻¹ := by
      unfold bandRes; rw [norm_inv]; rfl
    rw [hR]
    have hq : |dispersion (gridAngle k + gridAngle ζ) - dispersion (gridAngle k)| /
        (‖bandDen d β v (gridAngle k)‖ * ‖bandDen d β v (gridAngle k + gridAngle ζ)‖) ≤
        2 * d * s / v * ‖bandDen d β v (gridAngle k)‖⁻¹ := by
      rw [div_le_iff₀ (mul_pos hden1 (lt_of_lt_of_le hv0 hden2))]
      calc |dispersion (gridAngle k + gridAngle ζ) - dispersion (gridAngle k)|
          ≤ 2 * d * s := hD
        _ = 2 * d * s / v * ‖bandDen d β v (gridAngle k)‖⁻¹ *
              (‖bandDen d β v (gridAngle k)‖ * v) := by field_simp
        _ ≤ 2 * d * s / v * ‖bandDen d β v (gridAngle k)‖⁻¹ *
              (‖bandDen d β v (gridAngle k)‖ *
                ‖bandDen d β v (gridAngle k + gridAngle ζ)‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hden2 hden1.le
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hq 2
  have h1 := gridAvgReal_mono hpt
  rw [gridAvgReal_mul_left] at h1
  have : t * gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖ ^ 2) = 1 := hn
  have hA : gridAvgReal (fun k : Torus d L => ‖gridResolvent E t r k‖ ^ 2) = 1 / t := by
    rw [eq_div_iff ht.ne']; linarith
  rw [hA] at h1
  calc t / 2 * gridAvgReal (fun k => ‖gridResolvent E t r k - gridResolvent E t r (k + ζ)‖ ^ 2)
      ≤ t / 2 * ((2 * d * s / v) ^ 2 * (1 / t)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * d ^ 2 * s ^ 2 / v ^ 2 := by field_simp

theorem angle1_neg {L : ℕ} [NeZero L] (x : ZMod L) :
    ∃ n : ℤ, angle1 L (-x) = -angle1 L x + 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := angle1_add x (-x)
  have h0 : angle1 L (x + -x) = 0 := by
    rw [add_neg_cancel]; simp [angle1]
  refine ⟨-n, ?_⟩
  rw [h0] at hn
  push_cast
  linarith

theorem gridResolvent_neg (E t : ℝ) (r : ℂ) (k : Torus d L) :
    gridResolvent E t r (-k) = gridResolvent E t r k := by
  unfold gridResolvent
  congr 3
  unfold dispersion
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨n, hn⟩ := angle1_neg (k j)
  show Real.cos (angle1 L (-k j)) = Real.cos (angle1 L (k j))
  rw [hn, show -angle1 L (k j) + 2 * Real.pi * n = -angle1 L (k j) + n * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi, Real.cos_neg]

theorem fSymbol_norm_le_product (E t : ℝ) (r : ℂ) (ht : 0 < t) (ζ : Torus d L) :
    ‖fSymbol E t r ζ‖ ≤ t * gridAvgReal (fun k : Torus d L =>
      ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) := by
  unfold fSymbol
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply mul_le_mul_of_nonneg_left _ ht.le
  refine (norm_gridAvg_le _).trans (le_of_eq ?_)
  unfold gridAvgReal
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (Torus d L)) _ _ (fun k => ?_)
  simp only [Equiv.neg_apply, norm_mul, norm_star]
  rw [gridResolvent_neg, show ζ - -k = k + ζ by abel]

theorem min_le_four_frac {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    min 1 (s ^ 2 / t ^ 2) ≤ 4 * (s ^ 2 / (t + s) ^ 2) := by
  have hts : 0 < t + s := by linarith
  rcases le_total s t with h | h
  · refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ (by positivity)]
    rw [show 4 * (s ^ 2 / (t + s) ^ 2) * t ^ 2 = s ^ 2 * (4 * t ^ 2 / (t + s) ^ 2) by
      field_simp]
    have : 1 ≤ 4 * t ^ 2 / (t + s) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    nlinarith [sq_nonneg s]
  · refine (min_le_left _ _).trans ?_
    rw [show 4 * (s ^ 2 / (t + s) ^ 2) = 4 * s ^ 2 / (t + s) ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    nlinarith

set_option maxHeartbeats 4000000 in
/-- **Two-sided gap at every nonzero grid frequency**, with the decay of the symbol. -/
theorem gap_two_sided (hLD : LargeSymbolDecayWStatement) (hd : 3 ≤ d) {w a₀ B : ℝ}
    (hw : 0 < w) (ha₀ : 0 < a₀) (haB : a₀ ≤ B) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, w ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          scalarMap (d := d) (L := L) E t r = r →
          ∀ (ζ : Torus d L) (j₀ : Fin d), gridAngle ζ j₀ ≠ 0 →
            (∀ j, |gridAngle ζ j| ≤ |gridAngle ζ j₀|) →
            c * min 1 (|gridAngle ζ j₀| ^ 2 / t ^ 2) ≤ 1 - (fSymbol E t r ζ).re ∧
            1 - (fSymbol E t r ζ).re ≤ C * min 1 (|gridAngle ζ j₀| ^ 2 / t ^ 2) ∧
            ‖fSymbol E t r ζ‖ ≤ C * t * Real.log (2 / t) ^ 2 / |gridAngle ζ j₀| := by
  have hB0 : 0 < B := lt_of_lt_of_le ha₀ haB
  obtain ⟨Cl, tl, hCl, htl, hdec⟩ := hLD d hd w hw a₀ B ha₀ haB
  obtain ⟨cg, ζ₀, tg, hcg, hζ₀, htg, hgap⟩ := product_patch_grid_gap (d := d) (by omega)
    (β₁ := w / 2) (β₂ := 3 / 200) (B := B) (by positivity) (by norm_num) hB0
  set M : ℝ := 20 * (2 : ℝ) ^ (1 / 20 : ℝ) with hM
  have hM0 : 0 < M := by positivity
  set s₀ : ℝ := min 1 (ζ₀ / (2 * Cl * M ^ 2 + 1)) with hs₀
  have hs₀0 : 0 < s₀ := lt_min one_pos (by positivity)
  refine ⟨min (cg / 8) (1 / 2), max (max 2 (2 * d ^ 2 / a₀ ^ 2)) Cl,
    min (s₀ ^ 20) (min tl (min tg (min (w / (2 * B)) 1))),
    lt_min (by positivity) (by norm_num), lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans
      (le_max_left _ _)), by positivity, ?_⟩
  intro t ht ht₀ L _ hL4 hLe hLb E hE1 hE2 r hr hfix ζ j₀ hθ0 hθ
  have htl' : t ≤ tl := ht₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htg' : t ≤ tg := ht₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have htw : t ≤ w / (2 * B) := ht₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have ht1 : t ≤ 1 := ht₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hrim : 0 < r.im := rectangle_im_pos ha₀ hr
  obtain ⟨hrre, hrim1, hrim2⟩ := hr
  have hp := hrim
  set s : ℝ := |gridAngle ζ j₀| with hsdef
  have hs0 : 0 < s := abs_pos.mpr hθ0
  set F := fSymbol (d := d) (L := L) E t r ζ with hF
  -- decay of the symbol
  have hdecay : ‖F‖ ≤ Cl * t * Real.log (2 / t) ^ 2 / s := by
    refine (fSymbol_norm_le_product E t r ht ζ).trans ?_
    have := hdec t ht htl' L hL4 hLe hLb E hE1 hE2 r ⟨hrre, hrim1, hrim2⟩ ζ j₀ hθ0
    calc t * gridAvgReal (fun k : Torus d L =>
          ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖)
        ≤ t * (Cl * Real.log (2 / t) ^ 2 / s) := mul_le_mul_of_nonneg_left this ht.le
      _ = Cl * t * Real.log (2 / t) ^ 2 / s := by ring
  -- upper bound
  have hupper : 1 - F.re ≤ max (max 2 (2 * d ^ 2 / a₀ ^ 2)) Cl * min 1 (s ^ 2 / t ^ 2) := by
    have hFn := fSymbol_norm_le (d := d) hL4 ht hp hfix ζ
    have h1 : 1 - F.re ≤ 2 := by
      have := Complex.re_le_norm F
      have := neg_le_abs F.re
      have := Complex.abs_re_le_norm F
      linarith
    have h2 : 1 - F.re ≤ 2 * d ^ 2 / a₀ ^ 2 * (s ^ 2 / t ^ 2) := by
      refine (fSymbol_gap_upper hL4 ht hp hfix ζ s hs0.le hθ).trans ?_
      rw [div_mul_div_comm]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha₀.le hrim1 2) (by positivity)
    rcases min_choice 1 (s ^ 2 / t ^ 2) with h | h
    · rw [h, mul_one]
      exact h1.trans ((le_max_left _ _).trans (le_max_left _ _))
    · rw [h]
      refine h2.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _))
        (by positivity))
  refine ⟨?_, hupper, hdecay.trans (by
    apply div_le_div_of_nonneg_right _ hs0.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le)⟩
  -- lower bound
  have hw1 : w ≤ 1 / 100 := hE1.trans hE2
  by_cases hsmall : s ≤ ζ₀
  · -- direct grid gap
    set β := E + 2 * d + t * r.re with hβ
    set v := t * r.im with hv
    have hre : |t * r.re| ≤ w / 2 := by
      rw [abs_mul, abs_of_pos ht]
      calc t * |r.re| ≤ t * B := mul_le_mul_of_nonneg_left hrre ht.le
        _ ≤ w / 2 := by rw [le_div_iff₀ (by positivity)] at htw; linarith
    have hβ1 : w / 2 ≤ β := by have := (abs_le.mp hre).1; linarith
    have hβ2 : β ≤ 3 / 200 := by have := (abs_le.mp hre).2; linarith
    have hvB : v ≤ B * t := by rw [hv, mul_comm]; exact mul_le_mul_of_nonneg_right hrim2 ht.le
    have hL2 : t⁻¹ ^ 2 ≤ (L : ℝ) := by
      refine le_trans ?_ hLb
      have : 1 ≤ t⁻¹ := by rw [le_inv_comm₀ one_pos ht]; simpa using ht1
      exact pow_le_pow_right₀ this (by norm_num)
    have hg := hgap t ht htg' L hL2 β v hβ1 hβ2 (mul_pos ht hrim) hvB ζ j₀ hθ0 hθ hsmall
    have hid := fSymbol_gap_identity (d := d) hL4 ht hp hfix ζ
    have hsame : gridAvgReal (fun k : Torus d L =>
        ‖gridResolvent E t r k - gridResolvent E t r (k + ζ)‖ ^ 2) =
        gridAvgReal (fun k : Torus d L =>
          ‖bandRes d β v (gridAngle k) - bandRes d β v (gridAngle (k + ζ))‖ ^ 2) := by
      congr 1; funext k; rw [gridResolvent_eq_bandRes, gridResolvent_eq_bandRes]
    rw [hsame] at hid
    rw [← hF] at hid
    have hfrac := min_le_four_frac hs0.le ht
    have key : cg / 2 * (s ^ 2 / (t + s) ^ 2) ≤ 1 - F.re := by
      rw [hid]
      have e : cg / 2 * (s ^ 2 / (t + s) ^ 2) = t / 2 * (cg * (s ^ 2 / (t * (t + s) ^ 2))) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hg (by positivity)
    calc min (cg / 8) (1 / 2) * min 1 (s ^ 2 / t ^ 2)
        ≤ cg / 8 * min 1 (s ^ 2 / t ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ cg / 8 * (4 * (s ^ 2 / (t + s) ^ 2)) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = cg / 2 * (s ^ 2 / (t + s) ^ 2) := by ring
      _ ≤ 1 - F.re := key
  · -- large frequency: the symbol is at most 1/2
    push Not at hsmall
    have hσ : t ^ (1 / 20 : ℝ) ≤ s₀ := by
      have h := Real.rpow_le_rpow ht.le (ht₀.trans (min_le_left _ _)) (by norm_num : (0 : ℝ) ≤ 1 / 20)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hs₀0.le, show ((20 : ℕ) : ℝ) * (1 / 20) = 1 by
        norm_num, Real.rpow_one] at h
    set σ := t ^ (1 / 20 : ℝ) with hσdef
    have hσ0 : 0 < σ := Real.rpow_pos_of_pos ht _
    have hσ1 : σ ≤ 1 := hσ.trans (min_le_left _ _)
    have ht_eq : t = σ ^ 20 := by rw [twentieth_pow ht]; norm_num
    have hlog : Real.log (2 / t) ≤ M / σ := log_le_twentieth (c := 2) (by norm_num) ht
    have hlog0 : 0 ≤ Real.log (2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    have hsmallF : ‖F‖ ≤ 1 / 2 := by
      refine hdecay.trans ?_
      have h1 : Cl * t * Real.log (2 / t) ^ 2 ≤ Cl * M ^ 2 * σ ^ 18 := by
        have : Real.log (2 / t) ^ 2 ≤ (M / σ) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
        calc Cl * t * Real.log (2 / t) ^ 2 ≤ Cl * t * (M / σ) ^ 2 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = Cl * M ^ 2 * σ ^ 18 := by rw [ht_eq]; field_simp
      have h2 : σ ^ 18 ≤ σ := pow_le_of_le_one hσ0.le hσ1 (by norm_num)
      have h3 : σ ≤ ζ₀ / (2 * Cl * M ^ 2 + 1) := hσ.trans (min_le_right _ _)
      rw [div_le_iff₀ hs0]
      have h4 : Cl * M ^ 2 * σ ≤ ζ₀ / 2 := by
        rw [le_div_iff₀ (by positivity)] at h3
        nlinarith [sq_nonneg M]
      have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ Cl * M ^ 2 by positivity)
      linarith
    have hre : F.re ≤ 1 / 2 := (Complex.re_le_norm F).trans hsmallF
    calc min (cg / 8) (1 / 2) * min 1 (s ^ 2 / t ^ 2) ≤ 1 / 2 * 1 :=
          mul_le_mul (min_le_right _ _) (min_le_left _ _) (by positivity) (by norm_num)
      _ ≤ 1 - F.re := by linarith

end AndersonAC.S3
