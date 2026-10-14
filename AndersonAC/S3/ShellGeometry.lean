import AndersonAC.S3.Definitions

/-! Pointwise geometry behind the tangential-shell argument in §3, lines 456–526. -/

noncomputable section
open scoped BigOperators

namespace AndersonAC.S3

variable {d : ℕ}

/-- The difference of the transformed dispersions is exactly a linear functional. -/
theorem sliced_dispersion_difference (ζ x : Frequency d) :
    slicedDispersion 1 ζ x - slicedDispersion (-1) ζ x =
      ∑ j, (4 * Real.sin (ζ j / 2)) * x j := by
  calc
    slicedDispersion 1 ζ x - slicedDispersion (-1) ζ x =
        4 * ∑ j, Real.sin (ζ j / 2) * x j := by unfold slicedDispersion; ring
    _ = _ := by simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

/-- Two energy-shell constraints force the thin slab used before hyperplane slicing. -/
theorem sliced_dispersion_slab (ζ x : Frequency d) (E s₁ s₂ : ℝ)
    (h₁ : |slicedDispersion (-1) ζ x - E| ≤ s₁)
    (h₂ : |slicedDispersion 1 ζ x - E| ≤ s₂) :
    |∑ j, (4 * Real.sin (ζ j / 2)) * x j| ≤ s₁ + s₂ := by
  rw [← sliced_dispersion_difference]
  calc
    |slicedDispersion 1 ζ x - slicedDispersion (-1) ζ x| =
        |(slicedDispersion 1 ζ x - E) + -(slicedDispersion (-1) ζ x - E)| := by ring_nf
    _ ≤ |slicedDispersion 1 ζ x - E| + |-(slicedDispersion (-1) ζ x - E)| := abs_add_le _ _
    _ ≤ s₁ + s₂ := by rw [abs_neg]; linarith

def slicedCoordinate (sign ζ u : ℝ) : ℝ :=
  -2 * Real.cos (ζ / 2) * Real.sqrt (1 - u ^ 2) + sign * 2 * Real.sin (ζ / 2) * u

def slicedCoordinateDeriv (sign ζ u : ℝ) : ℝ :=
  2 * Real.cos (ζ / 2) * u / Real.sqrt (1 - u ^ 2) + sign * 2 * Real.sin (ζ / 2)

def slicedCoordinateSecond (ζ u : ℝ) : ℝ :=
  2 * Real.cos (ζ / 2) / Real.sqrt (1 - u ^ 2) ^ 3

theorem sliced_coordinate_hasDerivAt (sign ζ u : ℝ) (hu : |u| < 1) :
    HasDerivAt (slicedCoordinate sign ζ) (slicedCoordinateDeriv sign ζ u) u := by
  have hq : 0 < 1 - u ^ 2 := by
    have h := abs_lt.mp hu
    nlinarith
  have hs := ((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).sqrt hq.ne'
  have h := (hs.const_mul (-2 * Real.cos (ζ / 2))).add
    ((hasDerivAt_id u).const_mul (sign * 2 * Real.sin (ζ / 2)))
  convert h using 1
  · rfl
  · dsimp [slicedCoordinateDeriv]
    field_simp
    <;> ring

theorem sliced_coordinate_deriv_hasDerivAt (sign ζ u : ℝ) (hu : |u| < 1) :
    HasDerivAt (slicedCoordinateDeriv sign ζ) (slicedCoordinateSecond ζ u) u := by
  have hq : 0 < 1 - u ^ 2 := by
    have h := abs_lt.mp hu
    nlinarith
  have hroot : Real.sqrt (1 - u ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hs := ((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).sqrt hq.ne'
  have h := (((hasDerivAt_id u).const_mul (2 * Real.cos (ζ / 2))).div hs hroot).add_const
    (sign * 2 * Real.sin (ζ / 2))
  convert h using 1
  · rfl
  · dsimp [slicedCoordinateSecond]
    field_simp [hroot]
    have he : 2 * Real.sqrt (1 - u ^ 2) ^ 2 - u * (0 - 2 * u) = 2 := by
      nlinarith [Real.sq_sqrt hq.le]
    rw [he]
    ring

theorem sliced_coordinate_second_bounds (ζ u : ℝ)
    (hζ : |ζ| ≤ 1 / 2) (hu : |u| ≤ 1 / 4) :
    1 ≤ slicedCoordinateSecond ζ u ∧ slicedCoordinateSecond ζ u ≤ 8 := by
  have hu' := abs_le.mp hu
  have hζ' := abs_le.mp hζ
  have hq : 0 < 1 - u ^ 2 := by nlinarith
  have hroot0 := Real.sqrt_nonneg (1 - u ^ 2)
  have hrootSq := Real.sq_sqrt hq.le
  have hrootLo : (3 / 4 : ℝ) ≤ Real.sqrt (1 - u ^ 2) := by nlinarith
  have hrootHi : Real.sqrt (1 - u ^ 2) ≤ 1 := by nlinarith [sq_nonneg u]
  have hcLo : (1 / 2 : ℝ) ≤ Real.cos (ζ / 2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ζ / 2)]
  have hcHi := Real.cos_le_one (ζ / 2)
  have hcube : 0 < Real.sqrt (1 - u ^ 2) ^ 3 := by positivity
  unfold slicedCoordinateSecond
  constructor
  · apply (le_div_iff₀ hcube).mpr
    nlinarith
  · apply (div_le_iff₀ hcube).mpr
    nlinarith

end AndersonAC.S3
