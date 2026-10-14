import AndersonAC.AgentS78.ResetJoin

/-!
# Helper lemmas for the stage operation: fourth-row sums

* `rowFour_rpow_add_le`: Minkowski's inequality for the `ℓ⁴` row norm;
* `rowFour_smul_padM`: the fourth-row sum of a scaled padded block;
* `rowFour_reset_le`: a fourth-row sum below `.8 t^{1+δ}` plus a reset change with
  `ℓ⁴` row norm `≤ C t^{1/4} t^{.35δ}` stays below `t^{1+δ}` when `C t^{.10δ} ≤ 1/20`
  (07-assembly.tex:1020–1025).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **Minkowski for fourth-row sums.** -/
theorem rowFour_rpow_add_le {ι : Type} [Fintype ι] (a b : Matrix ι ι ℂ) (i : ι) :
    rowFour (a + b) i ^ (1 / 4 : ℝ) ≤ rowFour a i ^ (1 / 4 : ℝ) + rowFour b i ^ (1 / 4 : ℝ) := by
  have hp : (1 : ℝ) ≤ 4 := by norm_num
  have hM := Real.Lp_add_le_of_nonneg (s := Finset.univ) (f := fun j => ‖a i j‖)
    (g := fun j => ‖b i j‖) hp (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
  have hcast : ∀ x : ℝ, x ^ (4 : ℝ) = x ^ (4 : ℕ) := fun x => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hcast] at hM
  refine le_trans ?_ hM
  unfold rowFour
  apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) _ (by norm_num)
  refine Finset.sum_le_sum fun j _ => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 4

/-- Fourth-row sums of a scaled padded block. -/
theorem rowFour_smul_padM {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (s : ℂ)
    (X : Matrix A A ℂ) (a : A) : rowFour (s • padM A X) a.val = rowFour (s • X) a := by
  unfold rowFour
  rw [← Finset.sum_subset (Finset.subset_univ A) (fun j _ hj => by
    simp [padM, a.property, hj])]
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [padM_val]

theorem rowFour_smul_padM_out {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (s : ℂ)
    (X : Matrix A A ℂ) (i : ι) (hi : i ∉ A) : rowFour (s • padM A X) i = 0 := by
  unfold rowFour
  exact Finset.sum_eq_zero fun j _ => by simp [padM, hi]

theorem rowFour_nonneg {ι : Type} [Fintype ι] (h : Matrix ι ι ℂ) (i : ι) : 0 ≤ rowFour h i :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **A reset keeps the fourth-row bound.** -/
theorem rowFour_reset_le {ι : Type} [Fintype ι] (h h' : Matrix ι ι ℂ) (i : ι) (t C ρ : ℝ)
    (ht : 0 < t) (hρ : ρ ≤ t ^ (0.35 * delta)) (hC : 0 ≤ C)
    (hrow : rowFour h i < 0.8 * t ^ (1 + delta))
    (hdiff : rowFour (h' - h) i ^ (1 / 4 : ℝ) ≤ C * t ^ (1 / 4 : ℝ) * ρ)
    (hsmall : C * t ^ (0.10 * delta) ≤ 1 / 20) :
    rowFour h' i ≤ t ^ (1 + delta) := by
  have hT : 0 < t ^ ((1 + delta) / 4) := Real.rpow_pos_of_pos ht _
  have h1 : rowFour h i ^ (1 / 4 : ℝ) ≤ 0.95 * t ^ ((1 + delta) / 4) := by
    have : rowFour h i ≤ (0.95 * t ^ ((1 + delta) / 4)) ^ (4 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hT.le, ← Real.rpow_mul ht.le]
      have h95 : (0.8 : ℝ) ≤ 0.95 ^ (4 : ℝ) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      have : (1 + delta) / 4 * 4 = 1 + delta := by ring
      rw [this]
      nlinarith [Real.rpow_pos_of_pos ht (1 + delta)]
    calc rowFour h i ^ (1 / 4 : ℝ) ≤ ((0.95 * t ^ ((1 + delta) / 4)) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (rowFour_nonneg h i) this (by norm_num)
      _ = 0.95 * t ^ ((1 + delta) / 4) := by
          rw [← Real.rpow_mul (by positivity)]; norm_num
  have h2 : C * t ^ (1 / 4 : ℝ) * ρ ≤ (1 / 20) * t ^ ((1 + delta) / 4) := by
    have hsplit : t ^ (1 / 4 : ℝ) * t ^ (0.35 * delta) =
        t ^ (0.10 * delta) * t ^ ((1 + delta) / 4) := by
      rw [← Real.rpow_add ht, ← Real.rpow_add ht]; congr 1; norm_num [delta]
    calc C * t ^ (1 / 4 : ℝ) * ρ ≤ C * t ^ (1 / 4 : ℝ) * t ^ (0.35 * delta) :=
          mul_le_mul_of_nonneg_left hρ (by positivity)
      _ = (C * t ^ (0.10 * delta)) * t ^ ((1 + delta) / 4) := by rw [mul_assoc, hsplit]; ring
      _ ≤ (1 / 20) * t ^ ((1 + delta) / 4) := mul_le_mul_of_nonneg_right hsmall hT.le
  have hsum := rowFour_rpow_add_le h (h' - h) i
  rw [add_sub_cancel] at hsum
  have h3 : rowFour h' i ^ (1 / 4 : ℝ) ≤ t ^ ((1 + delta) / 4) := by linarith
  have h4 := Real.rpow_le_rpow (Real.rpow_nonneg (rowFour_nonneg h' i) _) h3
    (show (0 : ℝ) ≤ 4 by norm_num)
  have h5 : (1 + delta) / 4 * 4 = 1 + delta := by ring
  have h6 : (1 / 4 : ℝ) * 4 = 1 := by norm_num
  rw [← Real.rpow_mul (rowFour_nonneg h' i), ← Real.rpow_mul ht.le, h5, h6, Real.rpow_one] at h4
  exact h4

end AndersonAC.AgentS78
