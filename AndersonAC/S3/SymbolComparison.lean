import AndersonAC.S3.Definitions

/-!
Symbol-level comparisons behind the inverse-form bounds of Proposition 3.6 (§3,
lines 702–735): for one nonzero frequency with dominant angle `s`, Laplacian
symbol `ℓ ∈ [(4/π²) s², d s²]`, gap `u = 1 - Re F̂ ≍ min(1, s²/t²)`, and
`p = Im r ∈ [a₀, B]`, the inverse symbol `1/(p² u)` satisfies the four bounds.
Pure real inequalities.
-/

noncomputable section

namespace AndersonAC.S3

theorem inv_min_le (x : ℝ) (hx : 0 < x) : (min 1 x)⁻¹ ≤ 1 + x⁻¹ := by
  rcases min_choice 1 x with h | h
  · rw [h, inv_one]; have : 0 < x⁻¹ := inv_pos.mpr hx; linarith
  · rw [h]; linarith [zero_le_one (α := ℝ)]

/-- The four symbol bounds. -/
theorem symbol_bounds {d : ℝ} (hd : 1 ≤ d) {c₁ C₁ a₀ B p t s ℓ u κ' : ℝ}
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (ha₀ : 0 < a₀) (hp1 : a₀ ≤ p) (hp2 : p ≤ B)
    (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s)
    (hℓ1 : 4 / Real.pi ^ 2 * s ^ 2 ≤ ℓ) (hℓ2 : ℓ ≤ d * s ^ 2)
    (hu1 : c₁ * min 1 (s ^ 2 / t ^ 2) ≤ u) (hu2 : u ≤ C₁ * min 1 (s ^ 2 / t ^ 2))
    (hκ0 : 0 ≤ κ') (hsharp : t ≤ s ^ 2 → 1 - t ^ κ' / 2 ≤ u) (hκ1 : t ^ κ' ≤ 1) :
    (1 / (C₁ * B ^ 2 * Real.pi ^ 2)) * t ^ 2 * ℓ⁻¹ ≤ (p ^ 2 * u)⁻¹ ∧
    1 / (C₁ * B ^ 2) ≤ (p ^ 2 * u)⁻¹ ∧
    (p ^ 2 * u)⁻¹ ≤ 1 / (a₀ ^ 2 * c₁) + d / (a₀ ^ 2 * c₁) * t ^ 2 * ℓ⁻¹ ∧
    (p ^ 2 * u)⁻¹ ≤ (1 + t ^ κ') * (p ^ 2)⁻¹ + 2 * d / (a₀ ^ 2 * c₁) * t * ℓ⁻¹ := by
  have hpi := Real.pi_pos
  have hp0 : 0 < p := lt_of_lt_of_le ha₀ hp1
  have hB0 : 0 < B := lt_of_lt_of_le hp0 hp2
  have hm0 : 0 < min 1 (s ^ 2 / t ^ 2) := lt_min one_pos (by positivity)
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu1
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ1
  have hpu0 : 0 < p ^ 2 * u := by positivity
  have hp2' : p ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hp0.le hp2 2
  have hp1' : a₀ ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ ha₀.le hp1 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `c t² Λ⁺ ≤ X`
    rw [le_inv_comm₀ (by positivity) hpu0]
    rw [show (1 / (C₁ * B ^ 2 * Real.pi ^ 2) * t ^ 2 * ℓ⁻¹)⁻¹ =
      C₁ * B ^ 2 * Real.pi ^ 2 * ℓ / t ^ 2 by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have h1 : u ≤ C₁ * (s ^ 2 / t ^ 2) := hu2.trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC₁.le)
    have h2 : p ^ 2 * u * t ^ 2 ≤ B ^ 2 * (C₁ * s ^ 2) := by
      calc p ^ 2 * u * t ^ 2 ≤ B ^ 2 * (C₁ * (s ^ 2 / t ^ 2)) * t ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul hp2' h1 hu0.le (by positivity)
        _ = B ^ 2 * (C₁ * s ^ 2) := by field_simp
    have h3 : s ^ 2 ≤ Real.pi ^ 2 * ℓ / 4 := by
      have e : Real.pi ^ 2 * (4 / Real.pi ^ 2 * s ^ 2) = 4 * s ^ 2 := by field_simp
      have := mul_le_mul_of_nonneg_left hℓ1 (sq_nonneg Real.pi)
      rw [e] at this; linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ B ^ 2 * C₁ by positivity)
    have h5 : 0 ≤ C₁ * B ^ 2 * Real.pi ^ 2 * ℓ := by positivity
    nlinarith
  · -- `c ≤ X`
    rw [le_inv_comm₀ (by positivity) hpu0, one_div, inv_inv]
    have : u ≤ C₁ := hu2.trans (by
      have := min_le_left 1 (s ^ 2 / t ^ 2)
      nlinarith)
    calc p ^ 2 * u ≤ B ^ 2 * C₁ := mul_le_mul hp2' this hu0.le (by positivity)
      _ = C₁ * B ^ 2 := by ring
  · -- `X ≤ C₀ + C t² Λ⁺`
    have h1 : (p ^ 2 * u)⁻¹ ≤ (a₀ ^ 2 * (c₁ * min 1 (s ^ 2 / t ^ 2)))⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_mul hp1' hu1 (by positivity) (by positivity))
    have h2 : (a₀ ^ 2 * (c₁ * min 1 (s ^ 2 / t ^ 2)))⁻¹ =
        (a₀ ^ 2 * c₁)⁻¹ * (min 1 (s ^ 2 / t ^ 2))⁻¹ := by
      rw [← mul_inv, mul_assoc]
    have h3 := inv_min_le (s ^ 2 / t ^ 2) (by positivity)
    have h4 : (s ^ 2 / t ^ 2)⁻¹ ≤ d * t ^ 2 * ℓ⁻¹ := by
      rw [inv_div, div_le_iff₀ (by positivity)]
      rw [show d * t ^ 2 * ℓ⁻¹ * s ^ 2 = t ^ 2 * (d * s ^ 2 / ℓ) by field_simp]
      have : 1 ≤ d * s ^ 2 / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
      nlinarith [sq_nonneg t]
    calc (p ^ 2 * u)⁻¹ ≤ (a₀ ^ 2 * c₁)⁻¹ * (min 1 (s ^ 2 / t ^ 2))⁻¹ := h2 ▸ h1
      _ ≤ (a₀ ^ 2 * c₁)⁻¹ * (1 + d * t ^ 2 * ℓ⁻¹) :=
          mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
      _ = 1 / (a₀ ^ 2 * c₁) + d / (a₀ ^ 2 * c₁) * t ^ 2 * ℓ⁻¹ := by ring
  · -- the sharp bound
    have hX0 : 0 ≤ 2 * d / (a₀ ^ 2 * c₁) * t * ℓ⁻¹ := by
      have : 0 ≤ d := by linarith
      positivity
    by_cases hts : t ≤ s ^ 2
    · have hu := hsharp hts
      have hk : t ^ κ' ≤ 1 := hκ1
      have hk0 : 0 ≤ t ^ κ' := Real.rpow_nonneg ht.le _
      have hinv : u⁻¹ ≤ 1 + t ^ κ' := by
        rw [inv_le_iff_one_le_mul₀ hu0]
        nlinarith
      calc (p ^ 2 * u)⁻¹ = u⁻¹ * (p ^ 2)⁻¹ := by rw [mul_inv]; ring
        _ ≤ (1 + t ^ κ') * (p ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hinv (by positivity)
        _ ≤ _ := le_add_of_nonneg_right hX0
    · push Not at hts
      have h1 : (p ^ 2 * u)⁻¹ ≤ (a₀ ^ 2 * (c₁ * min 1 (s ^ 2 / t ^ 2)))⁻¹ :=
        inv_anti₀ (by positivity) (mul_le_mul hp1' hu1 (by positivity) (by positivity))
      have h2 : (a₀ ^ 2 * (c₁ * min 1 (s ^ 2 / t ^ 2)))⁻¹ =
          (a₀ ^ 2 * c₁)⁻¹ * (min 1 (s ^ 2 / t ^ 2))⁻¹ := by
        rw [← mul_inv, mul_assoc]
      have h3 := inv_min_le (s ^ 2 / t ^ 2) (by positivity)
      have h4 : 1 + (s ^ 2 / t ^ 2)⁻¹ ≤ 2 * d * t * ℓ⁻¹ := by
        have hts' : 1 ≤ t / s ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
        have e1 : (s ^ 2 / t ^ 2)⁻¹ ≤ t / s ^ 2 := by
          rw [inv_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have : t ^ 2 ≤ t := by nlinarith
          nlinarith [sq_nonneg s]
        have e2 : t / s ^ 2 ≤ d * t * ℓ⁻¹ := by
          rw [div_le_iff₀ (by positivity)]
          rw [show d * t * ℓ⁻¹ * s ^ 2 = t * (d * s ^ 2 / ℓ) by field_simp]
          have : 1 ≤ d * s ^ 2 / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
          nlinarith
        linarith
      have h5 : (p ^ 2 * u)⁻¹ ≤ (a₀ ^ 2 * c₁)⁻¹ * (2 * d * t * ℓ⁻¹) := by
        calc (p ^ 2 * u)⁻¹ ≤ (a₀ ^ 2 * c₁)⁻¹ * (min 1 (s ^ 2 / t ^ 2))⁻¹ := h2 ▸ h1
          _ ≤ (a₀ ^ 2 * c₁)⁻¹ * (2 * d * t * ℓ⁻¹) :=
              mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
      have e : (a₀ ^ 2 * c₁)⁻¹ * (2 * d * t * ℓ⁻¹) = 2 * d / (a₀ ^ 2 * c₁) * t * ℓ⁻¹ := by
        field_simp
      have hk0 : 0 ≤ (1 + t ^ κ') * (p ^ 2)⁻¹ := by
        have := Real.rpow_nonneg ht.le κ'
        positivity
      linarith

end AndersonAC.S3
