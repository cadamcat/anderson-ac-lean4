import AndersonAC.S6.Geometry
import AndersonAC.S6Schur.Schur

/-! Only direct hopping contributes to the exponentially weighted commutator. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem weighted_error_entry (a t : ℝ) (ρ : R → ℝ) (J K : Matrix R R ℝ) (r : R → ℂ)
    (hK : ∀ i j, K i j ≠ 0 → ρ i = ρ j) (i j : R) :
    (AndersonAC.S6.exponentialWeight a t ρ * AndersonAC.S6.dampedMatrix (J + K) t r *
      AndersonAC.S6.exponentialWeight (-a) t ρ - AndersonAC.S6.dampedMatrix (J + K) t r) i j =
        ((Real.exp (a * t * (ρ i - ρ j)) : ℂ) - 1) * (J i j : ℂ) := by
  rw [weighted_conjugation_entry]
  let z : ℂ := (Real.exp (a * t * (ρ i - ρ j)) : ℂ) - 1
  have hzk : z * (K i j : ℂ) = 0 := by
    by_cases hk : K i j = 0
    · simp [hk]
    · simp [z, hK i j hk]
  have hzr : z * Matrix.diagonal r i j = 0 := by
    by_cases hij : i = j
    · subst j
      simp [z]
    · simp [Matrix.diagonal, hij]
  change z * (((J i j + K i j : ℝ) : ℂ) - (t : ℂ) * Matrix.diagonal r i j) = z * (J i j : ℂ)
  push_cast
  linear_combination hzk - (t : ℂ) * hzr

theorem weighted_error_entry_bound (a t : ℝ) (ρ : R → ℝ) (J K : Matrix R R ℝ) (r : R → ℂ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hJ : ∀ i j, |J i j| ≤ 1)
    (hJρ : ∀ i j, J i j ≠ 0 → |ρ i - ρ j| ≤ 1)
    (hK : ∀ i j, K i j ≠ 0 → ρ i = ρ j) (i j : R) :
    ‖(AndersonAC.S6.exponentialWeight a t ρ * AndersonAC.S6.dampedMatrix (J + K) t r *
      AndersonAC.S6.exponentialWeight (-a) t ρ - AndersonAC.S6.dampedMatrix (J + K) t r) i j‖ ≤
        if J i j = 0 then 0 else Real.exp (a * t) - 1 := by
  rw [weighted_error_entry a t ρ J K r hK i j]
  by_cases hij : J i j = 0
  · simp [hij]
  · rw [if_neg hij]
    have hat : 0 ≤ a * t := mul_nonneg ha ht
    have hd : |a * t * (ρ i - ρ j)| ≤ a * t := by
      rw [abs_mul, abs_of_nonneg hat]
      exact (mul_le_mul_of_nonneg_left (hJρ i j hij) hat).trans_eq (mul_one _)
    have he := exp_difference_bound (a * t * (ρ i - ρ j)) (a * t) hat hd
    have hM : 0 ≤ Real.exp (a * t) - 1 := (abs_nonneg _).trans he
    calc
      _ = |Real.exp (a * t * (ρ i - ρ j)) - 1| * |J i j| := by
        simp only [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (Real.exp (a * t) - 1) * 1 := mul_le_mul he (hJ i j) (abs_nonneg _) hM
      _ = _ := mul_one _

theorem weighted_error_row_column_bounds (d : ℕ) (a t : ℝ) (ρ : R → ℝ)
    (J K : Matrix R R ℝ) (r : R → ℂ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hJs : J.IsSymm) (hJ : ∀ i j, |J i j| ≤ 1)
    (hdegree : ∀ i, ((Finset.univ.filter (fun j => J i j ≠ 0)).card : ℝ) ≤ 2 * d)
    (hJρ : ∀ i j, J i j ≠ 0 → |ρ i - ρ j| ≤ 1)
    (hK : ∀ i j, K i j ≠ 0 → ρ i = ρ j) :
    let E := AndersonAC.S6.exponentialWeight a t ρ * AndersonAC.S6.dampedMatrix (J + K) t r *
      AndersonAC.S6.exponentialWeight (-a) t ρ - AndersonAC.S6.dampedMatrix (J + K) t r
    (∀ i, ∑ j, ‖E i j‖ ≤ (2 * d) * (Real.exp (a * t) - 1)) ∧
    (∀ j, ∑ i, ‖E i j‖ ≤ (2 * d) * (Real.exp (a * t) - 1)) := by
  let M := Real.exp (a * t) - 1
  have hM : 0 ≤ M := by
    have h := Real.add_one_le_exp (a * t)
    dsimp [M]
    nlinarith [mul_nonneg ha ht]
  have hentry := weighted_error_entry_bound a t ρ J K r ha ht hJ hJρ hK
  have hcoldegree (j : R) :
      ((Finset.univ.filter (fun i => J i j ≠ 0)).card : ℝ) ≤ 2 * d := by
    have hfilter : Finset.univ.filter (fun i => J i j ≠ 0) =
        Finset.univ.filter (fun i => J j i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hJs.apply i j]
    rw [hfilter]
    exact hdegree j
  constructor
  · intro i
    calc
      _ ≤ ∑ j, if J i j = 0 then 0 else M := Finset.sum_le_sum (fun j _ => hentry i j)
      _ = ∑ j ∈ Finset.univ.filter (fun j => J i j ≠ 0), M := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : J i j = 0 <;> simp [h]
      _ = ((Finset.univ.filter (fun j => J i j ≠ 0)).card : ℝ) * M := by simp
      _ ≤ (2 * d) * M := mul_le_mul_of_nonneg_right (hdegree i) hM
  · intro j
    calc
      _ ≤ ∑ i, if J i j = 0 then 0 else M := Finset.sum_le_sum (fun i _ => hentry i j)
      _ = ∑ i ∈ Finset.univ.filter (fun i => J i j ≠ 0), M := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : J i j = 0 <;> simp [h]
      _ = ((Finset.univ.filter (fun i => J i j ≠ 0)).card : ℝ) * M := by simp
      _ ≤ (2 * d) * M := mul_le_mul_of_nonneg_right (hcoldegree j) hM

theorem weighted_commutator_bound (d n : ℕ)
    (a t : ℝ) (ρ : Fin n → ℝ) (J K : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℂ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hJs : J.IsSymm) (hJ : ∀ i j, |J i j| ≤ 1)
    (hdegree : ∀ i, ((Finset.univ.filter (fun j => J i j ≠ 0)).card : ℝ) ≤ 2 * d)
    (hJρ : ∀ i j, J i j ≠ 0 → |ρ i - ρ j| ≤ 1)
    (hK : ∀ i j, K i j ≠ 0 → ρ i = ρ j) :
    ‖AndersonAC.S6.exponentialWeight a t ρ * AndersonAC.S6.dampedMatrix (J + K) t r *
      AndersonAC.S6.exponentialWeight (-a) t ρ - AndersonAC.S6.dampedMatrix (J + K) t r‖ ≤
        (2 * d) * (Real.exp (a * t) - 1) := by
  let E := AndersonAC.S6.exponentialWeight a t ρ * AndersonAC.S6.dampedMatrix (J + K) t r *
    AndersonAC.S6.exponentialWeight (-a) t ρ - AndersonAC.S6.dampedMatrix (J + K) t r
  let U := (2 * d : ℝ) * (Real.exp (a * t) - 1)
  have hU : 0 ≤ U := by
    have h := Real.add_one_le_exp (a * t)
    have hM : 0 ≤ Real.exp (a * t) - 1 := by nlinarith [mul_nonneg ha ht]
    exact mul_nonneg (by positivity) hM
  obtain ⟨hrows, hcols⟩ := weighted_error_row_column_bounds d a t ρ J K r ha ht hJs hJ hdegree hJρ hK
  have h := schurNormBound_proof n n E U U hU hU hrows hcols
  simpa only [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hU] using h

end AndersonAC.SolS6

#print axioms AndersonAC.SolS6.weighted_error_entry
#print axioms AndersonAC.SolS6.weighted_error_entry_bound
#print axioms AndersonAC.SolS6.weighted_error_row_column_bounds
#print axioms AndersonAC.SolS6.weighted_commutator_bound
