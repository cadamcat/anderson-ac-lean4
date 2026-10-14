import AndersonAC.S3.Definitions

/-! Exact dispersion / Laplacian-symbol identity (§3, line 223).
Proved without placeholders; imports only `Definitions` (never `Statements`). -/

noncomputable section

namespace AndersonAC.S3

variable {d : ℕ}

theorem dispersion_identity_proof (k : Frequency d) :
    dispersion k = -2 * (d : ℝ) + laplacianSymbol k := by
  unfold dispersion laplacianSymbol
  have hcoord : ∀ j : Fin d,
      -2 * Real.cos (k j) = -2 + 4 * Real.sin (k j / 2) ^ 2 := by
    intro j
    have h := Real.sin_sq_eq_half_sub (x := k j / 2)
    have h2 : 2 * (k j / 2) = k j := by ring
    rw [h2] at h
    linarith
  have hsum : (-2 : ℝ) * ∑ j, Real.cos (k j) = ∑ j, (-2 + 4 * Real.sin (k j / 2) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact hcoord j
  calc (-2 : ℝ) * ∑ j, Real.cos (k j)
      = ∑ j, (-2 + 4 * Real.sin (k j / 2) ^ 2) := hsum
    _ = -2 * (d : ℝ) + 4 * ∑ j, Real.sin (k j / 2) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end AndersonAC.S3
