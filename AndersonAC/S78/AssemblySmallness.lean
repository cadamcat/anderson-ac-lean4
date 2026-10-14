import AndersonAC.S78.MatrixReset
import AndersonAC.S78Scale.Proofs

set_option autoImplicit false
open AndersonAC.S78
namespace AndersonAC.SolS78

/-- The exponent margin absorbs fixed local constants and the tail into a
strict improvement of the assembly comparison. The cutoff is uniform in
the volume and the number of operations. -/
theorem assembly_error_smallness (d : ℕ) (hd : 3 ≤ d) (C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      C * t ^ (0.125 * delta - (d : ℝ) * nu d) + t ^ (0.2 * delta) ≤
        (c / 2) * t ^ (0.10 * delta) := by
  have hmargin := (assembly_exponent_margins_proof d hd).2.2.2.1
  let s := 0.125 * delta - (d : ℝ) * nu d - 0.10 * delta
  have hs : 0 < s := sub_pos.mpr hmargin
  let L := max C 1
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨t₁, ht₁, h₁⟩ := reset_radius_small s (c / (4 * L)) hs (by positivity)
  obtain ⟨t₂, ht₂, h₂⟩ := reset_radius_small (0.10 * delta) (c / 4)
    (by norm_num [delta]) (by positivity)
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, ?_⟩
  intro t ht hsmall
  have hp₁ := h₁ t ht (hsmall.trans_le (min_le_left _ _))
  have hp₂ := h₂ t ht (hsmall.trans_le (min_le_right _ _))
  have hcoeff : C * t ^ s ≤ c / 4 := by
    calc
      C * t ^ s ≤ L * t ^ s := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg ht.le _)
      _ ≤ L * (c / (4 * L)) := mul_le_mul_of_nonneg_left hp₁ hL.le
      _ = c / 4 := by field_simp
  have hpower : t ^ (0.125 * delta - (d : ℝ) * nu d) =
      t ^ (0.10 * delta) * t ^ s := by
    rw [← Real.rpow_add ht]
    congr 1
    dsimp [s]
    ring
  have hpower₂ : t ^ (0.2 * delta) = t ^ (0.10 * delta) * t ^ (0.10 * delta) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ = t ^ (0.10 * delta) * (C * t ^ s + t ^ (0.10 * delta)) := by
      rw [hpower, hpower₂]
      ring
    _ ≤ t ^ (0.10 * delta) * (c / 4 + c / 4) :=
      mul_le_mul_of_nonneg_left (add_le_add hcoeff hp₂) (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

/-- Weighted local-energy coefficients obey the common dimension-independent
power estimate used for both survivor differences and Schur bridge weights. -/
theorem local_weight_coefficient_power (C t b α β : ℝ) (hC : 1 ≤ C)
    (ht : 0 < t) (ht1 : t ≤ 1) (hb : b ≤ t)
    (hexp : α ≤ 1 + α * (1 / 3 : ℝ) + β * (2 / 3 : ℝ)) :
    C * t ^ α + b * (C * t ^ α) ^ (1 / 3 : ℝ) * (C * t ^ β) ^ (2 / 3 : ℝ) ≤
      2 * C * t ^ α := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hCpow : C ^ (1 / 3 : ℝ) * C ^ (2 / 3 : ℝ) = C := by
    rw [← Real.rpow_add hCpos]
    norm_num
  have hproduct : t * (C * t ^ α) ^ (1 / 3 : ℝ) * (C * t ^ β) ^ (2 / 3 : ℝ) =
      C * t ^ (1 + α * (1 / 3 : ℝ) + β * (2 / 3 : ℝ)) := by
    rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg ht.le _),
      Real.mul_rpow hCpos.le (Real.rpow_nonneg ht.le _),
      ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
    calc
      _ = (C ^ (1 / 3 : ℝ) * C ^ (2 / 3 : ℝ)) *
          (t ^ (1 : ℝ) * t ^ (α * (1 / 3 : ℝ)) * t ^ (β * (2 / 3 : ℝ))) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [hCpow, ← Real.rpow_add ht, ← Real.rpow_add ht]
  have hweight : b * (C * t ^ α) ^ (1 / 3 : ℝ) * (C * t ^ β) ^ (2 / 3 : ℝ) ≤ C * t ^ α := by
    calc
      _ ≤ t * (C * t ^ α) ^ (1 / 3 : ℝ) * (C * t ^ β) ^ (2 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by positivity) _)
      _ = C * t ^ (1 + α * (1 / 3 : ℝ) + β * (2 / 3 : ℝ)) := hproduct
      _ ≤ C * t ^ α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ht ht1 hexp) hCpos.le
  linarith

theorem survivor_weight_coefficient (C t b : ℝ) (hC : 1 ≤ C)
    (ht : 0 < t) (ht1 : t ≤ 1) (hb : b ≤ t) :
    C * t ^ (0.25 * delta) +
      b * (C * t ^ (0.25 * delta)) ^ (1 / 3 : ℝ) *
        (C * t ^ (-1 - 0.47 * delta)) ^ (2 / 3 : ℝ) ≤ 2 * C * t ^ (0.25 * delta) := by
  apply local_weight_coefficient_power C t b _ _ hC ht ht1 hb
  norm_num [delta]

theorem bridge_weight_coefficient (C t b : ℝ) (hC : 1 ≤ C)
    (ht : 0 < t) (ht1 : t ≤ 1) (hb : b ≤ t) :
    C * t ^ (0.27 * delta) +
      b * (C * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (C * t ^ (-1 - 0.46 * delta)) ^ (2 / 3 : ℝ) ≤ 2 * C * t ^ (0.27 * delta) := by
  apply local_weight_coefficient_power C t b _ _ hC ht ht1 hb
  norm_num [delta]

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_error_smallness
#print axioms AndersonAC.SolS78.survivor_weight_coefficient
#print axioms AndersonAC.SolS78.bridge_weight_coefficient
