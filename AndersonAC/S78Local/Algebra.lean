import AndersonAC.S78.Definitions

open scoped BigOperators

namespace AndersonAC.SolS78Local

variable {ι : Type*} [Fintype ι]

def pairEnergy (w : ι → ι → ℝ) (f : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (f i - f j) ^ 2

noncomputable def complexPairEnergy (w : ι → ι → ℝ) (f : ι → ℂ) : ℝ :=
  ∑ i, ∑ j, w i j * ‖f i - f j‖ ^ 2

lemma pairEnergy_add_le_two (w : ι → ι → ℝ) (f g : ι → ℝ)
    (hnonneg : ∀ i j, 0 ≤ w i j) :
    pairEnergy w (fun i => f i + g i) ≤ 2 * pairEnergy w f + 2 * pairEnergy w g := by
  classical
  have hpoint (i j : ι) :
      w i j * ((f i + g i) - (f j + g j)) ^ 2 ≤
        2 * (w i j * (f i - f j) ^ 2) + 2 * (w i j * (g i - g j) ^ 2) := by
    have hsq : ((f i + g i) - (f j + g j)) ^ 2 ≤
        2 * (f i - f j) ^ 2 + 2 * (g i - g j) ^ 2 := by
      have h := sq_nonneg ((f i - f j) - (g i - g j))
      nlinarith
    calc
      w i j * ((f i + g i) - (f j + g j)) ^ 2 ≤
          w i j * (2 * (f i - f j) ^ 2 + 2 * (g i - g j) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (hnonneg i j)
      _ = 2 * (w i j * (f i - f j) ^ 2) +
          2 * (w i j * (g i - g j) ^ 2) := by ring
  unfold pairEnergy
  calc
    (∑ i, ∑ j, w i j * ((f i + g i) - (f j + g j)) ^ 2) ≤
        ∑ i, ∑ j, (2 * (w i j * (f i - f j) ^ 2) +
          2 * (w i j * (g i - g j) ^ 2)) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact hpoint i j
    _ = 2 * (∑ i, ∑ j, w i j * (f i - f j) ^ 2) +
        2 * (∑ i, ∑ j, w i j * (g i - g j) ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]

lemma pairEnergy_le_four_rowVariance (w : ι → ι → ℝ) (f : ι → ℝ) (c : ℝ)
    (hnonneg : ∀ i j, 0 ≤ w i j) (hsymm : ∀ i j, w i j = w j i) :
    pairEnergy w f ≤ 4 * ∑ i, (∑ j, w i j) * (f i - c) ^ 2 := by
  classical
  unfold pairEnergy
  have hpoint (i j : ι) :
      w i j * (f i - f j) ^ 2 ≤
        w i j * (2 * (f i - c) ^ 2 + 2 * (f j - c) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (hnonneg i j)
    have h := sq_nonneg ((f i - c) + (f j - c))
    nlinarith
  have hleft :
      (∑ i, ∑ j, w i j * (2 * (f i - c) ^ 2)) =
        2 * ∑ i, (∑ j, w i j) * (f i - c) ^ 2 := by
    calc
      (∑ i, ∑ j, w i j * (2 * (f i - c) ^ 2)) =
          ∑ i, (∑ j, w i j) * (2 * (f i - c) ^ 2) := by
            congr 1
            ext i
            rw [Finset.sum_mul]
      _ = ∑ i, 2 * ((∑ j, w i j) * (f i - c) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 2 * ∑ i, (∑ j, w i j) * (f i - c) ^ 2 := by
            rw [Finset.mul_sum]
  have hright :
      (∑ i, ∑ j, w i j * (2 * (f j - c) ^ 2)) =
        2 * ∑ j, (∑ i, w i j) * (f j - c) ^ 2 := by
    calc
      (∑ i, ∑ j, w i j * (2 * (f j - c) ^ 2)) =
          ∑ j, ∑ i, w i j * (2 * (f j - c) ^ 2) := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, w i j) * (2 * (f j - c) ^ 2) := by
            congr 1
            ext j
            rw [Finset.sum_mul]
      _ = ∑ j, 2 * ((∑ i, w i j) * (f j - c) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = 2 * ∑ j, (∑ i, w i j) * (f j - c) ^ 2 := by
            rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, w i j * (f i - f j) ^ 2)
        ≤ ∑ i, ∑ j, w i j * (2 * (f i - c) ^ 2 + 2 * (f j - c) ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hpoint i j
    _ = 2 * (∑ i, (∑ j, w i j) * (f i - c) ^ 2) +
        2 * (∑ j, (∑ i, w i j) * (f j - c) ^ 2) := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [hleft, hright]
    _ = 4 * ∑ i, (∑ j, w i j) * (f i - c) ^ 2 := by
          have hcol :
              (∑ j, (∑ i, w i j) * (f j - c) ^ 2) =
                ∑ j, (∑ i, w j i) * (f j - c) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsymm]
          rw [hcol]
          ring

lemma complexPairEnergy_le_four_rowVariance (w : ι → ι → ℝ) (f : ι → ℂ) (c : ℂ)
    (hnonneg : ∀ i j, 0 ≤ w i j) (hsymm : ∀ i j, w i j = w j i) :
    complexPairEnergy w f ≤ 4 * ∑ i, (∑ j, w i j) * ‖f i - c‖ ^ 2 := by
  classical
  unfold complexPairEnergy
  have hpoint (i j : ι) :
      w i j * ‖f i - f j‖ ^ 2 ≤
        w i j * (2 * ‖f i - c‖ ^ 2 + 2 * ‖f j - c‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (hnonneg i j)
    have htriangle : ‖f i - f j‖ ≤ ‖f i - c‖ + ‖f j - c‖ := by
      calc
        ‖f i - f j‖ = ‖(f i - c) + (c - f j)‖ := by congr 1; abel
        _ ≤ ‖f i - c‖ + ‖c - f j‖ := norm_add_le _ _
        _ = ‖f i - c‖ + ‖f j - c‖ := by
          rw [show ‖c - f j‖ = ‖f j - c‖ from norm_sub_rev _ _]
    have hnorm_nonneg : 0 ≤ ‖f i - f j‖ := norm_nonneg _
    have hsum_nonneg : 0 ≤ ‖f i - c‖ + ‖f j - c‖ := by positivity
    have hsq : ‖f i - f j‖ ^ 2 ≤ (‖f i - c‖ + ‖f j - c‖) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (‖f i - c‖ - ‖f j - c‖)]
  have hleft :
      (∑ i, ∑ j, w i j * (2 * ‖f i - c‖ ^ 2)) =
        2 * ∑ i, (∑ j, w i j) * ‖f i - c‖ ^ 2 := by
    calc
      (∑ i, ∑ j, w i j * (2 * ‖f i - c‖ ^ 2)) =
          ∑ i, (∑ j, w i j) * (2 * ‖f i - c‖ ^ 2) := by
            congr 1
            ext i
            rw [Finset.sum_mul]
      _ = ∑ i, 2 * ((∑ j, w i j) * ‖f i - c‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 2 * ∑ i, (∑ j, w i j) * ‖f i - c‖ ^ 2 := by rw [Finset.mul_sum]
  have hright :
      (∑ i, ∑ j, w i j * (2 * ‖f j - c‖ ^ 2)) =
        2 * ∑ j, (∑ i, w i j) * ‖f j - c‖ ^ 2 := by
    calc
      (∑ i, ∑ j, w i j * (2 * ‖f j - c‖ ^ 2)) =
          ∑ j, ∑ i, w i j * (2 * ‖f j - c‖ ^ 2) := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, w i j) * (2 * ‖f j - c‖ ^ 2) := by
            congr 1
            ext j
            rw [Finset.sum_mul]
      _ = ∑ j, 2 * ((∑ i, w i j) * ‖f j - c‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 2 * ∑ j, (∑ i, w i j) * ‖f j - c‖ ^ 2 := by rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, w i j * ‖f i - f j‖ ^ 2)
        ≤ ∑ i, ∑ j, w i j * (2 * ‖f i - c‖ ^ 2 + 2 * ‖f j - c‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hpoint i j
    _ = 2 * (∑ i, (∑ j, w i j) * ‖f i - c‖ ^ 2) +
        2 * (∑ j, (∑ i, w i j) * ‖f j - c‖ ^ 2) := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [hleft, hright]
    _ = 4 * ∑ i, (∑ j, w i j) * ‖f i - c‖ ^ 2 := by
          have hcol :
              (∑ j, (∑ i, w i j) * ‖f j - c‖ ^ 2) =
                ∑ j, (∑ i, w j i) * ‖f j - c‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [hsymm]
          rw [hcol]
          ring

lemma rowSum_nonneg (w : ι → ι → ℝ) (hnonneg : ∀ i j, 0 ≤ w i j) (i : ι) :
    0 ≤ ∑ j, w i j := Finset.sum_nonneg fun j hj => hnonneg i j

lemma rowSum_eq_zero_of_supported {S : Finset ι} (w : ι → ι → ℝ)
    (hsupport : ∀ i j, i ∉ S ∨ j ∉ S → w i j = 0) (i : ι) (hi : i ∉ S) :
    (∑ j, w i j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact hsupport i j (Or.inl hi)

lemma columnSum_eq_rowSum (w : ι → ι → ℝ) (hsymm : ∀ i j, w i j = w j i) (j : ι) :
    (∑ i, w i j) = ∑ i, w j i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [hsymm]

lemma weightedVariance_bound_of_row_caps {S : Finset ι} (w : ι → ι → ℝ) (f : ι → ℝ)
    (Lmax : ℝ)
    (hsupport : ∀ i j, i ∉ S ∨ j ∉ S → w i j = 0)
    (hrow : ∀ i, (∑ j, w i j) ≤ Lmax) :
    (∑ i, (∑ j, w i j) * f i ^ 2) ≤ Lmax * ∑ i ∈ S, f i ^ 2 := by
  classical
  have hrow_zero (i : ι) (hi : i ∉ S) : (∑ j, w i j) = 0 :=
    rowSum_eq_zero_of_supported w hsupport i hi
  calc
    (∑ i, (∑ j, w i j) * f i ^ 2) =
        ∑ i ∈ S, (∑ j, w i j) * f i ^ 2 := by
          symm
          apply Finset.sum_subset (s₁ := S) (s₂ := Finset.univ)
          · exact Finset.subset_univ _
          · intro i hi hnot
            simp [hrow_zero i hnot]
    _ ≤ ∑ i ∈ S, Lmax * f i ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (f i))
    _ = Lmax * ∑ i ∈ S, f i ^ 2 := by
          rw [Finset.mul_sum]

theorem pairEnergy_le_local_terms {S : Finset ι} (w : ι → ι → ℝ) (f : ι → ℝ)
    (Lmax : ℝ) (hnonneg : ∀ i j, 0 ≤ w i j) (hsymm : ∀ i j, w i j = w j i)
    (hsupport : ∀ i j, i ∉ S ∨ j ∉ S → w i j = 0)
    (hrow : ∀ i, (∑ j, w i j) ≤ Lmax) :
    pairEnergy w f ≤ 4 * Lmax * ∑ i ∈ S, f i ^ 2 := by
  have hvar := weightedVariance_bound_of_row_caps w f Lmax hsupport hrow
  calc
    pairEnergy w f ≤ 4 * ∑ i, (∑ j, w i j) * (f i - 0) ^ 2 :=
      pairEnergy_le_four_rowVariance w f 0 hnonneg hsymm
    _ = 4 * ∑ i, (∑ j, w i j) * f i ^ 2 := by simp
    _ ≤ 4 * (Lmax * ∑ i ∈ S, f i ^ 2) := by nlinarith
    _ = 4 * Lmax * ∑ i ∈ S, f i ^ 2 := by ring

end AndersonAC.SolS78Local
