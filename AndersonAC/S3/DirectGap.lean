import AndersonAC.S3.GridBounds
import AndersonAC.S3.GridCount
import AndersonAC.S3.Dispersion

/-!
The direct grid gap at small nonzero frequencies (§3, Proposition 3.6, lines
629–700 of `03-initialization.tex`, inequality `initial-direct-grid-gap`):

  `gridAvg_k |R(k) - R(k+ζ)|² ≥ c |θ|² / (t (t + |θ|)²)`,  `θ = gridAngle ζ`, `0 < |θ|∞ ≤ ζ₀`,

with no additive quadrature error. Instead of the paper's polar patch we count a
product-shaped patch of grid points directly: the coordinates other than the
largest coordinate `j₀` of `θ` are small, and the `j₀` coordinate lies within
`t/2` of the (sign-matched) solution of `4 sin²(κ/2) = β - (other terms)`.
-/

noncomputable section
open scoped BigOperators

namespace AndersonAC.S3

variable {d : ℕ}

/-- The complex denominator of `bandRes`. -/
def bandDen (d : ℕ) (β v : ℝ) (κ : Frequency d) : ℂ :=
  ((dispersion κ + 2 * d - β : ℝ) : ℂ) - v * Complex.I

theorem bandDen_ne {β v : ℝ} (hv : 0 < v) (κ : Frequency d) : bandDen d β v κ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [bandDen] at this
  linarith

theorem bandDen_norm_le (β v : ℝ) (hv : 0 ≤ v) (κ : Frequency d) :
    ‖bandDen d β v κ‖ ≤ |dispersion κ + 2 * d - β| + v := by
  unfold bandDen
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Complex.norm_I,
    Real.norm_eq_abs, abs_of_nonneg hv, mul_one]

theorem bandRes_sub_norm {β v : ℝ} (hv : 0 < v) (x y : Frequency d) :
    ‖bandRes d β v x - bandRes d β v y‖ =
      |dispersion y - dispersion x| / (‖bandDen d β v x‖ * ‖bandDen d β v y‖) := by
  have hx := bandDen_ne (β := β) hv x
  have hy := bandDen_ne (β := β) hv y
  have e : bandRes d β v x - bandRes d β v y =
      (bandDen d β v y - bandDen d β v x) / (bandDen d β v x * bandDen d β v y) := by
    unfold bandRes
    rw [← inv_sub_inv hx hy]
    rfl
  rw [e, norm_div, norm_mul]
  congr 1
  rw [show bandDen d β v y - bandDen d β v x = ((dispersion y - dispersion x : ℝ) : ℂ) by
    unfold bandDen; push_cast; ring, Complex.norm_real, Real.norm_eq_abs]

/-- The coordinate increment of the dispersion (sum-to-product). -/
theorem dispersion_add_sub (x θ : Frequency d) :
    dispersion (x + θ) - dispersion x =
      ∑ j, 4 * Real.sin (x j + θ j / 2) * Real.sin (θ j / 2) := by
  unfold dispersion
  rw [show -2 * ∑ j, Real.cos ((x + θ) j) - -2 * ∑ j, Real.cos (x j) =
      ∑ j, 2 * (Real.cos (x j) - Real.cos (x j + θ j)) by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply]; ring]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub_cos]
  have e1 : (x j + (x j + θ j)) / 2 = x j + θ j / 2 := by ring
  have e2 : (x j - (x j + θ j)) / 2 = -(θ j / 2) := by ring
  rw [e1, e2, Real.sin_neg]
  ring

theorem abs_dispersion_add_sub_le (x θ : Frequency d) (s : ℝ) (hs : ∀ j, |θ j| ≤ s) :
    |dispersion (x + θ) - dispersion x| ≤ 2 * d * s := by
  rw [dispersion_add_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ j, |4 * Real.sin (x j + θ j / 2) * Real.sin (θ j / 2)| ≤ 2 * s := by
    intro j
    rw [abs_mul, abs_mul]
    have h1 := Real.abs_sin_le_one (x j + θ j / 2)
    have h2 : |Real.sin (θ j / 2)| ≤ |θ j / 2| := Real.abs_sin_le_abs
    rw [abs_div, abs_two] at h2
    have := hs j
    have h0 := abs_nonneg (Real.sin (θ j / 2))
    norm_num
    nlinarith [abs_nonneg (Real.sin (x j + θ j / 2))]
  calc ∑ j, |4 * Real.sin (x j + θ j / 2) * Real.sin (θ j / 2)| ≤ ∑ _j : Fin d, 2 * s :=
        Finset.sum_le_sum fun j _ => this j
    _ = 2 * d * s := by simp; ring

/-- Lower bound of the dispersion increment along a dominant coordinate `j₀`
when the base point sits on the matching side of the band bottom. -/
theorem dispersion_increment_lower (x θ : Frequency d) (j₀ : Fin d) (κlo ρ : ℝ)
    (hκ : 0 < κlo) (hρ : ρ ≤ 1 / 10) (hθ0 : θ j₀ ≠ 0) (hθ : ∀ j, |θ j| ≤ |θ j₀|)
    (hθρ : |θ j₀| ≤ ρ) (hx : ∀ j, j ≠ j₀ → |x j| ≤ ρ)
    (hsign : 0 ≤ x j₀ * θ j₀) (hxlo : κlo / 2 ≤ |x j₀|) (hxhi : |x j₀| ≤ 6 / 5)
    (hsmall : 3 * (d : ℝ) * ρ ≤ 2 * κlo / Real.pi ^ 2) :
    2 * κlo / Real.pi ^ 2 * |θ j₀| ≤ dispersion (x + θ) - dispersion x := by
  rw [dispersion_add_sub]
  set s := |θ j₀| with hs
  have hs0 : 0 < s := abs_pos.mpr hθ0
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- the dominant term
  have hmain : 4 * κlo / Real.pi ^ 2 * s ≤
      4 * Real.sin (x j₀ + θ j₀ / 2) * Real.sin (θ j₀ / 2) := by
    have key : ∀ a b : ℝ, 0 ≤ a → 0 < b → κlo / 2 ≤ a → a ≤ 6 / 5 → b ≤ 1 / 10 →
        4 * κlo / Real.pi ^ 2 * b ≤ 4 * Real.sin (a + b / 2) * Real.sin (b / 2) := by
      intro a b ha hb ha1 ha2 hb1
      have s1 := Real.mul_le_sin (x := a + b / 2) (by linarith) (by linarith)
      have s2 := Real.mul_le_sin (x := b / 2) (by linarith) (by linarith)
      have t1 : κlo / Real.pi ≤ Real.sin (a + b / 2) := by
        have : 2 / Real.pi * (κlo / 2) ≤ 2 / Real.pi * (a + b / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have e : 2 / Real.pi * (κlo / 2) = κlo / Real.pi := by field_simp
        linarith
      have t2 : b / Real.pi ≤ Real.sin (b / 2) := by
        have e : 2 / Real.pi * (b / 2) = b / Real.pi := by field_simp
        linarith
      have e : 4 * κlo / Real.pi ^ 2 * b = 4 * (κlo / Real.pi) * (b / Real.pi) := by
        field_simp
      rw [e]
      have p1 : 0 ≤ κlo / Real.pi := by positivity
      have p2 : 0 ≤ b / Real.pi := by positivity
      have := mul_le_mul t1 t2 p2 (p1.trans t1)
      linarith
    rcases lt_or_gt_of_ne hθ0 with hneg | hpos
    · have hx0 : x j₀ ≤ 0 := by
        by_contra h; push Not at h; nlinarith
      have habs : |x j₀| = -x j₀ := abs_of_nonpos hx0
      have hsθ : s = -θ j₀ := by rw [hs, abs_of_neg hneg]
      have := key (-x j₀) (-θ j₀) (by linarith) (by linarith) (by rw [← habs]; exact hxlo)
        (by rw [← habs]; exact hxhi) (by rw [← hsθ]; linarith)
      have e1 : Real.sin (-x j₀ + -θ j₀ / 2) = -Real.sin (x j₀ + θ j₀ / 2) := by
        rw [← Real.sin_neg]; ring_nf
      have e2 : Real.sin (-θ j₀ / 2) = -Real.sin (θ j₀ / 2) := by
        rw [← Real.sin_neg]; ring_nf
      rw [e1, e2, ← hsθ] at this
      linarith
    · have hx0 : 0 ≤ x j₀ := by
        by_contra h; push Not at h; nlinarith
      have habs : |x j₀| = x j₀ := abs_of_nonneg hx0
      have hsθ : s = θ j₀ := by rw [hs, abs_of_pos hpos]
      have := key (x j₀) (θ j₀) hx0 hpos (by rw [← habs]; exact hxlo)
        (by rw [← habs]; exact hxhi) (by rw [← hsθ]; linarith)
      convert this using 2
  -- the other terms
  have hother : ∀ j, j ≠ j₀ →
      -(3 * ρ * s) ≤ 4 * Real.sin (x j + θ j / 2) * Real.sin (θ j / 2) := by
    intro j hj
    have h1 : |Real.sin (x j + θ j / 2)| ≤ ρ + s / 2 := by
      refine Real.abs_sin_le_abs.trans ((abs_add_le _ _).trans ?_)
      have := hx j hj
      have h2 : |θ j / 2| ≤ s / 2 := by rw [abs_div, abs_two]; linarith [hθ j]
      linarith
    have h2 : |Real.sin (θ j / 2)| ≤ s / 2 := by
      refine Real.abs_sin_le_abs.trans ?_
      rw [abs_div, abs_two]; linarith [hθ j]
    have h3 : |4 * Real.sin (x j + θ j / 2) * Real.sin (θ j / 2)| ≤ 3 * ρ * s := by
      rw [abs_mul, abs_mul]
      norm_num
      have := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
      nlinarith
    linarith [neg_abs_le (4 * Real.sin (x j + θ j / 2) * Real.sin (θ j / 2))]
  rw [Fintype.sum_eq_add_sum_compl j₀]
  have hrest : -( (d : ℝ) * (3 * ρ * s)) ≤
      ∑ j ∈ ({j₀}ᶜ : Finset (Fin d)), 4 * Real.sin (x j + θ j / 2) * Real.sin (θ j / 2) := by
    have := Finset.sum_le_sum (s := ({j₀}ᶜ : Finset (Fin d)))
      (fun j hj => hother j (by simpa using hj))
    simp only [Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul] at this
    have hc : ((({j₀}ᶜ : Finset (Fin d))).card : ℝ) ≤ d := by
      have := Finset.card_le_univ ({j₀}ᶜ : Finset (Fin d))
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hp : 0 ≤ 3 * ρ * s := by
      have : 0 ≤ ρ := (abs_nonneg _).trans hθρ
      positivity
    nlinarith
  have hfin : (d : ℝ) * (3 * ρ * s) ≤ 2 * κlo / Real.pi ^ 2 * s := by
    have := mul_le_mul_of_nonneg_right hsmall hs0.le
    nlinarith
  have e : 4 * κlo / Real.pi ^ 2 * s = 2 * (2 * κlo / Real.pi ^ 2 * s) := by ring
  linarith

/-- One coordinate of the Laplacian symbol. -/
def hsq (κ : ℝ) : ℝ := 4 * Real.sin (κ / 2) ^ 2

theorem hsq_even (κ : ℝ) : hsq (-κ) = hsq κ := by
  simp [hsq, neg_div, Real.sin_neg]

theorem hsq_le_sq (κ : ℝ) : hsq κ ≤ κ ^ 2 := by
  unfold hsq
  have h : |Real.sin (κ / 2)| ≤ |κ / 2| := Real.abs_sin_le_abs
  have h2 : Real.sin (κ / 2) ^ 2 ≤ (κ / 2) ^ 2 := by
    rw [← sq_abs, ← sq_abs (κ / 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith

theorem hsq_nonneg (κ : ℝ) : 0 ≤ hsq κ := by unfold hsq; positivity

theorem abs_hsq_sub_le (a b : ℝ) : |hsq a - hsq b| ≤ 2 * |a - b| := by
  have e : ∀ κ, hsq κ = 2 - 2 * Real.cos κ := by
    intro κ
    unfold hsq
    have h := Real.sin_sq_eq_half_sub (x := κ / 2)
    rw [show 2 * (κ / 2) = κ by ring] at h
    linarith
  rw [e, e, show 2 - 2 * Real.cos a - (2 - 2 * Real.cos b) = 2 * (Real.cos b - Real.cos a) by ring,
    abs_mul, abs_two, abs_sub_comm a b]
  exact mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le b a) (by norm_num)

theorem dispersion_add_two_d (κ : Frequency d) :
    dispersion κ + 2 * d = ∑ j, hsq (κ j) := by
  rw [dispersion_identity_proof]
  unfold laplacianSymbol hsq
  rw [Finset.mul_sum]
  ring

theorem exists_kstar {y : ℝ} (hy : 0 ≤ y ∧ y ≤ 1 / 50) :
    ∃ κ ∈ Set.Icc (0 : ℝ) 1, hsq κ = y := by
  have hc : ContinuousOn hsq (Set.Icc (0 : ℝ) 1) := by
    unfold hsq; fun_prop
  have h0 : hsq 0 = 0 := by simp [hsq]
  have h1 : 1 / 50 ≤ hsq 1 := by
    unfold hsq
    have := Real.sin_gt_sub_cube (x := 1 / 2) (by norm_num)
    nlinarith
  have := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
  obtain ⟨κ, hκ, hκy⟩ := this ⟨by rw [h0]; exact hy.1, hy.2.trans h1⟩
  exact ⟨κ, hκ, hκy⟩

/-- The positive solution of `hsq κ = y` in `[0,1]` (junk outside `[0, 1/50]`). -/
def kstar (y : ℝ) : ℝ :=
  if h : 0 ≤ y ∧ y ≤ 1 / 50 then Classical.choose (exists_kstar h) else 0

theorem kstar_spec {y : ℝ} (hy : 0 ≤ y ∧ y ≤ 1 / 50) :
    kstar y ∈ Set.Icc (0 : ℝ) 1 ∧ hsq (kstar y) = y := by
  unfold kstar
  rw [dif_pos hy]
  exact Classical.choose_spec (exists_kstar hy)

theorem sqrt_le_kstar {y : ℝ} (hy : 0 ≤ y ∧ y ≤ 1 / 50) : Real.sqrt y ≤ kstar y := by
  obtain ⟨⟨h0, -⟩, hk⟩ := kstar_spec hy
  have := hsq_le_sq (kstar y)
  rw [hk] at this
  exact Real.sqrt_le_iff.mpr ⟨h0, this⟩

theorem dispersion_gridAngle_add {L : ℕ} [NeZero L] (k ζ : Torus d L) :
    dispersion (gridAngle (k + ζ)) = dispersion (gridAngle k + gridAngle ζ) := by
  unfold dispersion
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨n, hn⟩ := angle1_add (k j) (ζ j)
  show Real.cos (angle1 L (k j + ζ j)) = Real.cos (angle1 L (k j) + angle1 L (ζ j))
  rw [hn, show angle1 L (k j) + angle1 L (ζ j) + 2 * Real.pi * n =
    angle1 L (k j) + angle1 L (ζ j) + n * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]

theorem bandRes_gridAngle_add {L : ℕ} [NeZero L] (β v : ℝ) (k ζ : Torus d L) :
    bandRes d β v (gridAngle (k + ζ)) = bandRes d β v (gridAngle k + gridAngle ζ) := by
  unfold bandRes
  rw [dispersion_gridAngle_add]

/-- Pointwise lower bound for the resolvent increment on the patch. -/
theorem patch_pointwise {β v t B κlo ρ : ℝ} (hv : 0 < v) (hvB : v ≤ B * t) (ht : 0 < t)
    (hB : 0 < B) (hκ : 0 < κlo) (hρ : ρ ≤ 1 / 10)
    (hsmall : 3 * (d : ℝ) * ρ ≤ 2 * κlo / Real.pi ^ 2)
    (x θ : Frequency d) (j₀ : Fin d) (hθ0 : θ j₀ ≠ 0) (hθ : ∀ j, |θ j| ≤ |θ j₀|)
    (hθρ : |θ j₀| ≤ ρ) (hx : ∀ j, j ≠ j₀ → |x j| ≤ ρ)
    (hsign : 0 ≤ x j₀ * θ j₀) (hxlo : κlo / 2 ≤ |x j₀|) (hxhi : |x j₀| ≤ 6 / 5)
    (hshell : |dispersion x + 2 * d - β| ≤ t) :
    (2 * κlo / Real.pi ^ 2) ^ 2 / (1 + B + 2 * d) ^ 4 *
        (|θ j₀| ^ 2 / (t ^ 2 * (t + |θ j₀|) ^ 2)) ≤
      ‖bandRes d β v x - bandRes d β v (x + θ)‖ ^ 2 := by
  set s := |θ j₀| with hs
  have hs0 : 0 < s := abs_pos.mpr hθ0
  set K := 1 + B + 2 * (d : ℝ) with hK
  have hK1 : 1 ≤ K := by have : (0 : ℝ) ≤ 2 * d := by positivity
                         linarith
  have hD := dispersion_increment_lower x θ j₀ κlo ρ hκ hρ hθ0 hθ hθρ hx hsign hxlo hxhi hsmall
  have hDabs := abs_dispersion_add_sub_le x θ s hθ
  have hD0 : 0 < dispersion (x + θ) - dispersion x :=
    lt_of_lt_of_le (by positivity) hD
  rw [bandRes_sub_norm hv, abs_of_pos hD0]
  have hw1 : ‖bandDen d β v x‖ ≤ K * t := by
    refine (bandDen_norm_le β v hv.le x).trans ?_
    have : (0 : ℝ) ≤ 2 * d * t := by positivity
    nlinarith
  have hw2 : ‖bandDen d β v (x + θ)‖ ≤ K * (t + s) := by
    refine (bandDen_norm_le β v hv.le (x + θ)).trans ?_
    have e : dispersion (x + θ) + 2 * d - β =
        (dispersion (x + θ) - dispersion x) + (dispersion x + 2 * d - β) := by ring
    have h1 : |dispersion (x + θ) + 2 * d - β| ≤ 2 * d * s + t := by
      rw [e]; exact (abs_add_le _ _).trans (add_le_add hDabs hshell)
    have : (0 : ℝ) ≤ B * s := by positivity
    have : (0 : ℝ) ≤ s := hs0.le
    nlinarith
  have hw1p : 0 < ‖bandDen d β v x‖ := norm_pos_iff.mpr (bandDen_ne hv x)
  have hw2p : 0 < ‖bandDen d β v (x + θ)‖ := norm_pos_iff.mpr (bandDen_ne hv (x + θ))
  have hfrac : (2 * κlo / Real.pi ^ 2) * s / (K * t * (K * (t + s))) ≤
      (dispersion (x + θ) - dispersion x) / (‖bandDen d β v x‖ * ‖bandDen d β v (x + θ)‖) := by
    apply div_le_div₀ hD0.le hD (by positivity)
    exact mul_le_mul hw1 hw2 hw2p.le (by positivity)
  have hfrac0 : 0 ≤ (2 * κlo / Real.pi ^ 2) * s / (K * t * (K * (t + s))) := by positivity
  have hsq := pow_le_pow_left₀ hfrac0 hfrac 2
  refine le_trans (le_of_eq ?_) hsq
  field_simp

theorem card_torus {L : ℕ} [NeZero L] : (Fintype.card (Torus d L) : ℝ) = (L : ℝ) ^ d := by
  simp [Torus, ZMod.card]

set_option maxHeartbeats 4000000 in
/-- **Direct grid gap** (§3, inequality `initial-direct-grid-gap`, before the
normalization): for `0 < |θ_{j₀}| = |θ|∞ ≤ ζ₀`,
`gridAvg_k |R(k) - R(k+ζ)|² ≥ c θ_{j₀}² / (t (t + |θ_{j₀}|)²)`, with no quadrature error. -/
theorem product_patch_grid_gap (hd : 1 ≤ d) {β₁ β₂ B : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : β₂ ≤ 1 / 50)
    (hB : 0 < B) :
    ∃ c ζ₀ t₀ : ℝ, 0 < c ∧ 0 < ζ₀ ∧ 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (L : ℕ) [NeZero L], t⁻¹ ^ 2 ≤ (L : ℝ) →
        ∀ β v : ℝ, β₁ ≤ β → β ≤ β₂ → 0 < v → v ≤ B * t →
        ∀ (ζ : Torus d L) (j₀ : Fin d), gridAngle ζ j₀ ≠ 0 →
          (∀ j, |gridAngle ζ j| ≤ |gridAngle ζ j₀|) → |gridAngle ζ j₀| ≤ ζ₀ →
          c * (|gridAngle ζ j₀| ^ 2 / (t * (t + |gridAngle ζ j₀|) ^ 2)) ≤
            gridAvgReal (fun k : Torus d L =>
              ‖bandRes d β v (gridAngle k) - bandRes d β v (gridAngle (k + ζ))‖ ^ 2) := by
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set κlo : ℝ := Real.sqrt (β₁ / 2) with hκlo
  have hκ : 0 < κlo := Real.sqrt_pos.mpr (by positivity)
  have hκsq : κlo ^ 2 = β₁ / 2 := Real.sq_sqrt (by positivity)
  set ρ : ℝ := min (1 / 10) (κlo / (2 * Real.pi ^ 2 * d)) with hρdef
  have hρ0 : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 10 := min_le_left _ _
  have hρ2 : ρ ≤ κlo / (2 * Real.pi ^ 2 * d) := min_le_right _ _
  have hdρ : (d : ℝ) * ρ ≤ κlo / (2 * Real.pi ^ 2) := by
    rw [le_div_iff₀ (by positivity)] at hρ2 ⊢
    nlinarith
  have hpi2 : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hsmall : 3 * (d : ℝ) * ρ ≤ 2 * κlo / Real.pi ^ 2 := by
    have : κlo / (2 * Real.pi ^ 2) * 3 ≤ 2 * κlo / Real.pi ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    nlinarith
  have hρκ : ρ ≤ κlo / 2 := by
    refine hρ2.trans ?_
    have h1 : 1 ≤ Real.pi ^ 2 * d := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hκ.le]
  have hdρ2 : (d : ℝ) * ρ ^ 2 ≤ β₁ / 2 := by
    have h1 : (d : ℝ) * ρ ≤ κlo / 2 := hdρ.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    have : (d : ℝ) * ρ ^ 2 ≤ κlo / 2 * (κlo / 2) := by
      rw [sq, ← mul_assoc]; exact mul_le_mul h1 hρκ hρ0.le (by positivity)
    nlinarith
  set K : ℝ := 1 + B + 2 * (d : ℝ) with hK
  set a : ℝ := ρ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one (by positivity)]; linarith
  set c : ℝ := a ^ d / (4 * Real.pi) * ((2 * κlo / Real.pi ^ 2) ^ 2 / K ^ 4) with hc
  refine ⟨c, ρ, min κlo (min (1 / 5) (min (1 / (4 * Real.pi)) (ρ / (2 * Real.pi)))),
    by positivity, hρ0, by positivity, ?_⟩
  intro t ht ht₀ L _ hLt β v hβ1 hβ2' hv hvB ζ j₀ hθ0 hθ hθρ
  have htκ : t ≤ κlo := ht₀.trans (min_le_left _ _)
  have ht5 : t ≤ 1 / 5 := ht₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht4 : t ≤ 1 / (4 * Real.pi) :=
    ht₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htρ : t ≤ ρ / (2 * Real.pi) :=
    ht₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have htL : 1 / t ≤ t * L := by
    have e : t * t⁻¹ ^ 2 = 1 / t := by field_simp
    rw [← e]; exact mul_le_mul_of_nonneg_left hLt ht.le
  set θ : Frequency d := gridAngle ζ with hθdef
  set s : ℝ := |θ j₀| with hs
  have hs0 : 0 < s := abs_pos.mpr hθ0
  set σ : ℝ := if 0 < θ j₀ then 1 else -1 with hσ
  -- the patch
  set offSum : Torus d L → ℝ := fun k => ∑ j, if j = j₀ then 0 else hsq (gridAngle k j)
    with hoff
  set A := Finset.univ.filter fun x : ZMod L => |angle1 L x - 0| ≤ ρ with hA
  set T' : Fin d → Finset (ZMod L) := fun j => if j = j₀ then {0} else A with hT'
  set X : Torus d L → Finset (ZMod L) := fun k' => Finset.univ.filter fun x : ZMod L =>
    |angle1 L x - σ * kstar (β - offSum k')| ≤ t / 2 with hX
  set S := (Fintype.piFinset T').sigma X with hS
  set P := S.image (fun p : (Σ _ : Torus d L, ZMod L) => Function.update p.1 j₀ p.2) with hP
  -- off-axis coordinates of the base points
  have hoffρ : ∀ k' ∈ Fintype.piFinset T', ∀ j, j ≠ j₀ → |gridAngle k' j| ≤ ρ := by
    intro k' hk' j hj
    have := Fintype.mem_piFinset.mp hk' j
    simp only [hT', if_neg hj, hA, Finset.mem_filter, Finset.mem_univ, true_and, sub_zero] at this
    exact this
  have hoffSum : ∀ k : Torus d L, (∀ j, j ≠ j₀ → |gridAngle k j| ≤ ρ) →
      0 ≤ offSum k ∧ offSum k ≤ β₁ / 2 := by
    intro k hk
    constructor
    · exact Finset.sum_nonneg fun j _ => by split_ifs; exacts [le_rfl, hsq_nonneg _]
    · refine le_trans ?_ hdρ2
      calc offSum k ≤ ∑ _j : Fin d, ρ ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            split_ifs with hj
            · positivity
            · refine (hsq_le_sq _).trans ?_
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hk j hj) 2
        _ = d * ρ ^ 2 := by simp
  have hy : ∀ k : Torus d L, (∀ j, j ≠ j₀ → |gridAngle k j| ≤ ρ) →
      (0 ≤ β - offSum k ∧ β - offSum k ≤ 1 / 50) ∧ β₁ / 2 ≤ β - offSum k := by
    intro k hk
    obtain ⟨h1, h2⟩ := hoffSum k hk
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  -- the points of the patch satisfy the pointwise hypotheses
  have hpoint : ∀ k ∈ P,
      (2 * κlo / Real.pi ^ 2) ^ 2 / K ^ 4 * (s ^ 2 / (t ^ 2 * (t + s) ^ 2)) ≤
        ‖bandRes d β v (gridAngle k) - bandRes d β v (gridAngle (k + ζ))‖ ^ 2 := by
    intro k hk
    obtain ⟨⟨k', x⟩, hp, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hk', hx⟩ := Finset.mem_sigma.mp hp
    simp only at hk' hx
    set k := Function.update k' j₀ x with hkdef
    have hkj : ∀ j, j ≠ j₀ → gridAngle k j = gridAngle k' j := by
      intro j hj; rw [gridAngle_apply, gridAngle_apply, hkdef, Function.update_of_ne hj]
    have hkj₀ : gridAngle k j₀ = angle1 L x := by
      rw [gridAngle_apply, hkdef, Function.update_self]
    have hoffk : offSum k = offSum k' := by
      simp only [hoff]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rfl
      · rw [hkj j hj]
    have hk'ρ := hoffρ k' hk'
    obtain ⟨hyr, hylo⟩ := hy k' hk'ρ
    set y := β - offSum k' with hydef
    obtain ⟨⟨hκ0, hκ1⟩, hκy⟩ := kstar_spec hyr
    have hκlo' : κlo ≤ kstar y := by
      refine le_trans ?_ (sqrt_le_kstar hyr)
      exact Real.sqrt_le_sqrt hylo
    have hxc : |angle1 L x - σ * kstar y| ≤ t / 2 := by
      simpa [hX] using hx
    rw [bandRes_gridAngle_add]
    have hσ1 : σ = 1 ∨ σ = -1 := by rw [hσ]; split_ifs <;> simp
    have hσabs : |σ * kstar y| = kstar y := by
      rcases hσ1 with h | h <;> rw [h] <;> simp [abs_of_nonneg hκ0]
    refine patch_pointwise hv hvB ht hB hκ hρ1 hsmall (gridAngle k) θ j₀ hθ0 hθ hθρ
      (fun j hj => by rw [hkj j hj]; exact hk'ρ j hj) ?_ ?_ ?_ ?_
    · -- sign
      rw [hkj₀]
      rcases lt_or_gt_of_ne hθ0 with hneg | hpos
      · have hσv : σ = -1 := by rw [hσ, if_neg (not_lt.mpr hneg.le)]
        rw [hσv] at hxc
        have := (abs_le.mp hxc).2
        have : angle1 L x ≤ 0 := by linarith
        exact mul_nonneg_of_nonpos_of_nonpos this hneg.le
      · have hσv : σ = 1 := by rw [hσ, if_pos hpos]
        rw [hσv] at hxc
        have := (abs_le.mp hxc).1
        have : 0 ≤ angle1 L x := by linarith
        exact mul_nonneg this hpos.le
    · rw [hkj₀]
      have h1 := abs_sub_abs_le_abs_sub (σ * kstar y) (angle1 L x)
      rw [hσabs, abs_sub_comm] at h1
      linarith
    · rw [hkj₀]
      have h1 := abs_sub_abs_le_abs_sub (angle1 L x) (σ * kstar y)
      rw [hσabs] at h1
      linarith
    · -- the energy shell
      rw [dispersion_add_two_d]
      have hoffc : offSum k = ∑ j ∈ ({j₀}ᶜ : Finset (Fin d)), hsq (gridAngle k j) := by
        simp only [hoff]
        rw [Fintype.sum_eq_add_sum_compl j₀, if_pos rfl, zero_add]
        exact Finset.sum_congr rfl fun j hj => if_neg (by simpa using hj)
      have hsplit : ∑ j, hsq (gridAngle k j) = hsq (gridAngle k j₀) + offSum k := by
        rw [hoffc, Fintype.sum_eq_add_sum_compl j₀]
      rw [hsplit, hoffk]
      have hy' : hsq (σ * kstar y) = y := by
        rcases hσ1 with h | h <;> rw [h] <;> simp [hsq_even, hκy]
      have : hsq (gridAngle k j₀) + offSum k' - β = hsq (gridAngle k j₀) - hsq (σ * kstar y) := by
        rw [hy', hydef]; ring
      rw [this, hkj₀]
      refine (abs_hsq_sub_le _ _).trans ?_
      linarith
  -- counting
  have hinj : Set.InjOn (fun p : (Σ _ : Torus d L, ZMod L) => Function.update p.1 j₀ p.2)
      (S : Set (Σ _ : Torus d L, ZMod L)) := by
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq h
    simp only at h
    have hp1 := (Finset.mem_sigma.mp hp).1
    have hq1 := (Finset.mem_sigma.mp hq).1
    have h0 : ∀ k' ∈ Fintype.piFinset T', k' j₀ = 0 := by
      intro k' hk'
      have := Fintype.mem_piFinset.mp hk' j₀
      simpa [hT'] using this
    have e1 : p1 = q1 := by
      funext j
      by_cases hj : j = j₀
      · rw [hj, h0 p1 hp1, h0 q1 hq1]
      · have := congrFun h j
        rwa [Function.update_of_ne hj, Function.update_of_ne hj] at this
    have e2 : p2 = q2 := by
      have := congrFun h j₀
      rwa [Function.update_self, Function.update_self] at this
    subst e1; subst e2; rfl
  have hcardP : (P.card : ℝ) = ∑ k' ∈ Fintype.piFinset T', ((X k').card : ℝ) := by
    rw [Finset.card_image_of_injOn hinj, hS, Finset.card_sigma]
    push_cast; rfl
  have hX1 : ∀ k' ∈ Fintype.piFinset T', t * L / (4 * Real.pi) ≤ ((X k').card : ℝ) := by
    intro k' hk'
    obtain ⟨hyr, -⟩ := hy k' (hoffρ k' hk')
    obtain ⟨⟨hκ0, hκ1⟩, -⟩ := kstar_spec hyr
    have hσabs : |σ * kstar (β - offSum k')| ≤ 1 := by
      have hσ1 : σ = 1 ∨ σ = -1 := by rw [hσ]; split_ifs <;> simp
      rcases hσ1 with h | h <;> rw [h] <;> simp [abs_of_nonneg hκ0, hκ1]
    have := card_angle1_near (L := L) (σ * kstar (β - offSum k')) (t / 2) (by positivity)
      (by linarith)
    have e : t / 2 * L / Real.pi - 1 = t * L / (2 * Real.pi) - 1 := by ring
    have h4 : 1 ≤ t * L / (4 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      have : 4 * Real.pi ≤ 1 / t := by
        rw [le_div_iff₀ ht]; rw [le_div_iff₀ (by positivity)] at ht4; linarith
      linarith
    have e2 : t * L / (2 * Real.pi) = 2 * (t * L / (4 * Real.pi)) := by ring
    simp only [hX]
    linarith
  have hAcard : a * L ≤ (A.card : ℝ) := by
    have this : ρ * L / Real.pi - 1 ≤ (A.card : ℝ) :=
      card_angle1_near (L := L) 0 ρ hρ0.le (by simp; linarith)
    have h2 : 2 * Real.pi ≤ ρ * L := by
      have h1 : 1 / t ≤ (L : ℝ) := by
        have : 1 / t ≤ t * L := htL
        have : t * L ≤ L := by
          have : t ≤ 1 := by linarith
          nlinarith
        linarith
      have : 2 * Real.pi / ρ ≤ 1 / t := by
        rw [le_div_iff₀ ht, div_mul_eq_mul_div, div_le_one hρ0]
        rw [le_div_iff₀ (by positivity)] at htρ; linarith
      rw [div_le_iff₀ hρ0] at this
      nlinarith
    have e : a * L = ρ * L / (2 * Real.pi) := by rw [ha]; ring
    rw [e]
    have e2 : ρ * L / Real.pi - 1 = 2 * (ρ * L / (2 * Real.pi)) - 1 := by field_simp
    have h3 : 1 ≤ ρ * L / (2 * Real.pi) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hprod : (a * L) ^ d ≤ (∏ j, ((T' j).card : ℝ)) * L := by
    have hT'j₀ : ((T' j₀).card : ℝ) = 1 := by simp [hT']
    rw [Fintype.prod_eq_mul_prod_compl j₀, hT'j₀, one_mul]
    have hrest : ∏ j ∈ ({j₀}ᶜ : Finset (Fin d)), (a * L) ≤
        ∏ j ∈ ({j₀}ᶜ : Finset (Fin d)), ((T' j).card : ℝ) := by
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j hj => ?_
      have hj' : j ≠ j₀ := by simpa using hj
      simp only [hT', if_neg hj']
      exact hAcard
    have hpow : (a * L) ^ d = (a * L) * ∏ j ∈ ({j₀}ᶜ : Finset (Fin d)), (a * L) := by
      rw [← Fintype.prod_eq_mul_prod_compl j₀ (f := fun _ => a * L)]
      simp
    rw [hpow]
    have haL : a * L ≤ L := by nlinarith
    have h0 : 0 ≤ ∏ j ∈ ({j₀}ᶜ : Finset (Fin d)), (a * L) := by positivity
    calc a * L * ∏ j ∈ ({j₀}ᶜ : Finset (Fin d)), (a * L)
        ≤ L * ∏ j ∈ ({j₀}ᶜ : Finset (Fin d)), ((T' j).card : ℝ) :=
          mul_le_mul haL hrest h0 hL0.le
      _ = (∏ j ∈ ({j₀}ᶜ : Finset (Fin d)), ((T' j).card : ℝ)) * L := by ring
  have hcardP2 : (a * L) ^ d * (t / (4 * Real.pi)) ≤ (P.card : ℝ) := by
    rw [hcardP]
    have h1 : ∑ k' ∈ Fintype.piFinset T', t * L / (4 * Real.pi) ≤
        ∑ k' ∈ Fintype.piFinset T', ((X k').card : ℝ) := Finset.sum_le_sum hX1
    rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset] at h1
    push_cast at h1
    have e : (∏ j, ((T' j).card : ℝ)) * (t * L / (4 * Real.pi)) =
        ((∏ j, ((T' j).card : ℝ)) * L) * (t / (4 * Real.pi)) := by ring
    rw [e] at h1
    exact le_trans (mul_le_mul_of_nonneg_right hprod (by positivity)) h1
  -- averaging
  set m : ℝ := (2 * κlo / Real.pi ^ 2) ^ 2 / K ^ 4 * (s ^ 2 / (t ^ 2 * (t + s) ^ 2)) with hm
  have hm0 : 0 ≤ m := by positivity
  set f : Torus d L → ℝ := fun k =>
    ‖bandRes d β v (gridAngle k) - bandRes d β v (gridAngle (k + ζ))‖ ^ 2 with hf
  have hsumP : (P.card : ℝ) * m ≤ ∑ k, f k := by
    have h1 : ∑ k ∈ P, m ≤ ∑ k ∈ P, f k := Finset.sum_le_sum fun k hk => hpoint k hk
    have h2 : ∑ k ∈ P, f k ≤ ∑ k, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => by positivity)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith
  unfold gridAvgReal
  rw [card_torus]
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  rw [← div_eq_inv_mul, le_div_iff₀ hLd]
  calc c * (s ^ 2 / (t * (t + s) ^ 2)) * (L : ℝ) ^ d
      = (a * L) ^ d * (t / (4 * Real.pi)) * m := by
        rw [hc, hm, mul_pow]; field_simp
    _ ≤ (P.card : ℝ) * m := mul_le_mul_of_nonneg_right hcardP2 hm0
    _ ≤ ∑ k, f k := hsumP

end AndersonAC.S3
