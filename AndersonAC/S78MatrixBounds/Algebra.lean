import AndersonAC.S78.Definitions
import AndersonAC.S78Row.Row

open scoped BigOperators

noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

def rowL4Root {ι : Type} [Fintype ι] (f : ι → ℂ) : ℝ :=
  (∑ i, ‖f i‖ ^ 4) ^ (1 / 4 : ℝ)

def rowL2Root {ι : Type} [Fintype ι] (f : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖f i‖ ^ 2)

theorem rowL2Root_nonneg {ι : Type} [Fintype ι] (f : ι → ℂ) : 0 ≤ rowL2Root f :=
  Real.sqrt_nonneg _

theorem rowL2Root_add_le {ι : Type} [Fintype ι] (f g : ι → ℂ) :
    rowL2Root (f + g) ≤ rowL2Root f + rowL2Root g := by
  have hnorm (v : ι → ℂ) :
      rowL2Root v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
    unfold rowL2Root
    rw [EuclideanSpace.norm_eq]
  calc
    rowL2Root (f + g) = ‖(WithLp.toLp 2 (f + g) : EuclideanSpace ℂ ι)‖ := hnorm _
    _ = ‖(WithLp.toLp 2 f : EuclideanSpace ℂ ι) +
          (WithLp.toLp 2 g : EuclideanSpace ℂ ι)‖ := by rw [WithLp.toLp_add]
    _ ≤ _ := norm_add_le _ _
    _ = _ := by rw [← hnorm, ← hnorm]

/-- Masking a row to a subset of columns cannot increase its finite ℓ² norm. -/
theorem rowL2Root_mask_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (f : ι → ℂ) :
    rowL2Root (fun j => if j ∈ A then f j else 0) ≤ rowL2Root f := by
  unfold rowL2Root
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : j ∈ A <;> simp [h]

theorem rowL2Root_sum_le {α ι : Type} [Fintype ι]
    (s : Finset α) (f : α → ι → ℂ) :
    rowL2Root (fun i => ∑ a ∈ s, f a i) ≤ ∑ a ∈ s, rowL2Root (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [rowL2Root]
  | @insert a s ha ih =>
      have hadd : (fun i => ∑ b ∈ insert a s, f b i) =
          (fun i => f a i + ∑ b ∈ s, f b i) := by
        funext i
        simp [Finset.sum_insert, ha]
      calc
        rowL2Root (fun i => ∑ b ∈ insert a s, f b i) =
            rowL2Root (fun i => f a i + ∑ b ∈ s, f b i) := by rw [hadd]
        _ ≤ rowL2Root (f a) + rowL2Root (fun i => ∑ b ∈ s, f b i) :=
              rowL2Root_add_le _ _
        _ ≤ rowL2Root (f a) + ∑ b ∈ s, rowL2Root (f b) := add_le_add_right ih _
        _ = ∑ b ∈ insert a s, rowL2Root (f b) := by simp [ha]

theorem rowTwo_eq_rowL2Root_sq {ι : Type} [Fintype ι]
    (A : Matrix ι ι ℂ) (i : ι) : rowTwo A i = (rowL2Root (fun j => A i j)) ^ 2 := by
  unfold rowTwo rowL2Root
  rw [Real.sq_sqrt (Finset.sum_nonneg fun j hj => sq_nonneg ‖A i j‖)]

/-- The row fourth-power quantity is the finite `ℓ⁴` norm to the fourth
power, so it obeys Minkowski under matrix addition. -/
theorem rowFour_root_add_le {ι : Type} [Fintype ι]
    (A B : Matrix ι ι ℂ) (i : ι) :
    (rowFour (A + B) i) ^ (1 / 4 : ℝ) ≤
      (rowFour A i) ^ (1 / 4 : ℝ) + (rowFour B i) ^ (1 / 4 : ℝ) := by
  let p : ENNReal := 4
  letI : Fact (1 ≤ p) := ⟨by norm_num [p]⟩
  letI : NormedAddCommGroup (PiLp p (fun _ : ι => ℂ)) :=
    PiLp.normedAddCommGroup p (fun _ : ι => ℂ)
  have hnorm (f : ι → ℂ) :
      ‖(WithLp.toLp p f : PiLp p (fun _ : ι => ℂ))‖ =
        (∑ j, ‖f j‖ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [PiLp.norm_eq_sum (by norm_num [p])]
    simp [p]
  have hadd :
      (WithLp.toLp p (fun j => A i j + B i j) : PiLp p (fun _ : ι => ℂ)) =
        WithLp.toLp p (fun j => A i j) + WithLp.toLp p (fun j => B i j) := by
    ext j
    rfl
  calc
    _ = ‖(WithLp.toLp p (fun j => A i j + B i j) : PiLp p (fun _ : ι => ℂ))‖ := by
      rw [hnorm]
      simp [rowFour]
    _ = ‖WithLp.toLp p (fun j => A i j) + WithLp.toLp p (fun j => B i j)‖ := by
      rw [hadd]
    _ ≤ ‖WithLp.toLp p (fun j => A i j)‖ + ‖WithLp.toLp p (fun j => B i j)‖ :=
      norm_add_le _ _
    _ = _ := by
      have hA : (∑ j, ‖A i j‖ ^ (4 : ℝ)) = rowFour A i := by
        unfold rowFour
        apply Finset.sum_congr rfl
        intro j hj
        exact Real.rpow_natCast _ 4
      have hB : (∑ j, ‖B i j‖ ^ (4 : ℝ)) = rowFour B i := by
        unfold rowFour
        apply Finset.sum_congr rfl
        intro j hj
        exact Real.rpow_natCast _ 4
      rw [hnorm, hnorm, hA, hB]

/-- Finite Minkowski for row vectors, obtained from the matrix row lemma. -/
theorem rowL4Root_add_le {ι : Type} [Fintype ι] [Nonempty ι]
    (f g : ι → ℂ) : rowL4Root (f + g) ≤ rowL4Root f + rowL4Root g := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  let A : Matrix ι ι ℂ := fun _ j => f j
  let B : Matrix ι ι ℂ := fun _ j => g j
  have h := rowFour_root_add_le A B i
  change rowL4Root (fun j => f j + g j) ≤ rowL4Root f + rowL4Root g at h
  exact h

/-- Minkowski over any finite family of rows. -/
theorem rowL4Root_sum_le {α ι : Type} [Fintype ι] [Nonempty ι]
    (s : Finset α) (f : α → ι → ℂ) :
    rowL4Root (fun i => ∑ a ∈ s, f a i) ≤ ∑ a ∈ s, rowL4Root (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [rowL4Root]
  | @insert a s ha ih =>
      have hadd : (fun i => ∑ b ∈ insert a s, f b i) =
          (fun i => f a i + ∑ b ∈ s, f b i) := by
        funext i
        simp [Finset.sum_insert, ha]
      calc
        rowL4Root (fun i => ∑ b ∈ insert a s, f b i) =
            rowL4Root (fun i => f a i + ∑ b ∈ s, f b i) := by rw [hadd]
        _ ≤ rowL4Root (f a) + rowL4Root (fun i => ∑ b ∈ s, f b i) :=
              rowL4Root_add_le _ _
        _ ≤ rowL4Root (f a) + ∑ b ∈ s, rowL4Root (f b) := add_le_add_right ih _
        _ = ∑ b ∈ insert a s, rowL4Root (f b) := by simp [ha]

/-- Masking a row to a subset of columns cannot increase its finite ℓ⁴ norm. -/
theorem rowL4Root_mask_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (f : ι → ℂ) :
    rowL4Root (fun j => if j ∈ A then f j else 0) ≤ rowL4Root f := by
  classical
  unfold rowL4Root
  apply Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => by positivity) ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : j ∈ A <;> simp [h]

/-- Entrywise and squared-row bounds give the corresponding ℓ⁴ row norm. -/
theorem rowL4Root_entry_row {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i : ι) (U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hentry : ∀ j, ‖A i j‖ ≤ U) (hrow : rowTwo A i ≤ V) :
    rowL4Root (fun j => A i j) ≤ Real.sqrt U * V ^ (1 / 4 : ℝ) := by
  have hfour := fourth_row_from_entry_and_two_proof A i U V hU hentry hrow
  have hnonneg : 0 ≤ rowFour A i := by
    unfold rowFour
    positivity
  have hroot := Real.rpow_le_rpow hnonneg hfour (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hfactor : (U ^ 2 * V) ^ (1 / 4 : ℝ) = Real.sqrt U * V ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (sq_nonneg U) hV]
    have hUsqrt : (U ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt U := by
      calc
        (U ^ 2) ^ (1 / 4 : ℝ) = (U ^ (2 : ℝ)) ^ (1 / 4 : ℝ) := by
          congr 1
          exact (Real.rpow_natCast U 2).symm
        _ = U ^ ((2 : ℝ) * (1 / 4 : ℝ)) := by rw [Real.rpow_mul hU]
        _ = U ^ (1 / 2 : ℝ) := by congr 1 <;> norm_num
        _ = Real.sqrt U := (Real.sqrt_eq_rpow U).symm
    rw [hUsqrt]
  change rowFour A i ^ (1 / 4 : ℝ) ≤ _
  calc
    rowFour A i ^ (1 / 4 : ℝ) ≤ (U ^ 2 * V) ^ (1 / 4 : ℝ) := hroot
    _ = Real.sqrt U * V ^ (1 / 4 : ℝ) := hfactor

/-- Raising the finite ℓ⁴ row norm to the fourth power recovers its sum. -/
theorem rowL4Root_pow_four {ι : Type} [Fintype ι] (f : ι → ℂ) :
    (rowL4Root f) ^ 4 = ∑ i, ‖f i‖ ^ 4 := by
  dsimp [rowL4Root]
  let S : ℝ := ∑ i, ‖f i‖ ^ 4
  have hS : 0 ≤ S := by dsimp [S]; exact Finset.sum_nonneg fun i _ => by positivity
  calc
    (S ^ (1 / 4 : ℝ)) ^ 4 = (S ^ (1 / 4 : ℝ)) ^ (4 : ℝ) := by
      exact (Real.rpow_natCast (S ^ (1 / 4 : ℝ)) 4).symm
    _ = S ^ ((1 / 4 : ℝ) * 4) :=
      (Real.rpow_mul hS (1 / 4 : ℝ) 4).symm
    _ = S := by norm_num [Real.rpow_one]

/-- A squared-kernel change has row sum controlled by the old row-two norm and
the row-two norm of the matrix increment. -/
theorem squareKernel_change_row_sum_bound {ι : Type} [Fintype ι]
    (H S : Matrix ι ι ℂ) (i : ι) (V W : ℝ)
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hrow : rowTwo H i ≤ V)
    (hS : rowL2Root (fun j => S i j) ≤ W) :
    (∑ j, ‖squareKernel (H + S) i j - squareKernel H i j‖) ≤
      2 * Real.sqrt V * W + W ^ 2 := by
  have hpoint (j : ι) :
      ‖squareKernel (H + S) i j - squareKernel H i j‖ ≤
        2 * ‖H i j‖ * ‖S i j‖ + ‖S i j‖ ^ 2 := by
    change ‖(H i j + S i j) ^ 2 - (H i j) ^ 2‖ ≤ _
    rw [show (H i j + S i j) ^ 2 - (H i j) ^ 2 =
      2 * H i j * S i j + (S i j) ^ 2 by ring]
    calc
      ‖2 * H i j * S i j + (S i j) ^ 2‖ ≤
          ‖2 * H i j * S i j‖ + ‖(S i j) ^ 2‖ := norm_add_le _ _
      _ = 2 * ‖H i j‖ * ‖S i j‖ + ‖S i j‖ ^ 2 := by
          simp [norm_mul, norm_pow]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    (fun j => ‖H i j‖) (fun j => ‖S i j‖)
  have hcs' :
      (∑ j, ‖H i j‖ * ‖S i j‖) ≤
        Real.sqrt (rowTwo H i) * Real.sqrt (rowTwo S i) := by
    simpa [rowTwo] using hcs
  have hrowS : rowTwo S i = (rowL2Root (fun j => S i j)) ^ 2 :=
    rowTwo_eq_rowL2Root_sq S i
  have hrootS : Real.sqrt (rowTwo S i) = rowL2Root (fun j => S i j) := by
    rw [hrowS, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (rowL2Root_nonneg (fun j => S i j))
  have hrootH : Real.sqrt (rowTwo H i) ≤ Real.sqrt V := Real.sqrt_le_sqrt hrow
  have hCSbound :
      (∑ j, ‖H i j‖ * ‖S i j‖) ≤ Real.sqrt V * W := by
    rw [hrootS] at hcs'
    exact (hcs'.trans
      (mul_le_mul hrootH hS (rowL2Root_nonneg (fun j => S i j)) (Real.sqrt_nonneg _)))
  have hsumS : rowTwo S i ≤ W ^ 2 := by
    rw [hrowS]
    exact (sq_le_sq₀ (rowL2Root_nonneg (fun j => S i j)) hW).2 hS
  have hsum :
      (∑ j, ‖squareKernel (H + S) i j - squareKernel H i j‖) ≤
        2 * (∑ j, ‖H i j‖ * ‖S i j‖) + rowTwo S i := by
    calc
      _ ≤ ∑ j, (2 * ‖H i j‖ * ‖S i j‖ + ‖S i j‖ ^ 2) :=
          Finset.sum_le_sum fun j hj => hpoint j
      _ = 2 * (∑ j, ‖H i j‖ * ‖S i j‖) + rowTwo S i := by
          unfold rowTwo
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          ring
  calc
    (∑ j, ‖squareKernel (H + S) i j - squareKernel H i j‖) ≤
        2 * (∑ j, ‖H i j‖ * ‖S i j‖) + rowTwo S i := hsum
    _ ≤ 2 * (Real.sqrt V * W) + W ^ 2 := by
      nlinarith [hCSbound, hsumS]
    _ = 2 * Real.sqrt V * W + W ^ 2 := by ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.rowFour_root_add_le
#print axioms AndersonAC.SolS78.rowL2Root_add_le
#print axioms AndersonAC.SolS78.rowL2Root_sum_le
#print axioms AndersonAC.SolS78.rowL2Root_nonneg
#print axioms AndersonAC.SolS78.rowTwo_eq_rowL2Root_sq
#print axioms AndersonAC.SolS78.rowL4Root_add_le
#print axioms AndersonAC.SolS78.rowL4Root_sum_le
#print axioms AndersonAC.SolS78.rowL4Root_mask_le
#print axioms AndersonAC.SolS78.rowL4Root_entry_row
#print axioms AndersonAC.SolS78.rowL4Root_pow_four
#print axioms AndersonAC.SolS78.squareKernel_change_row_sum_bound
