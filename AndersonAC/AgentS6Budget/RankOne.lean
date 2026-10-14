import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace AndersonAC.AgentS6Budget

def packVector {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
  WithLp.toLp 2 (fun j => x ((Fintype.equivFin ι).symm j))

theorem packVector_norm_sq {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    ‖packVector x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun _ => rfl)

theorem packVector_adapted {Ω ι : Type*} [Fintype ι] {m : MeasurableSpace Ω}
    (x : Ω → ι → ℂ) (hx : ∀ i, StronglyMeasurable[m] (fun ω => x ω i)) :
    StronglyMeasurable[m] (fun ω => packVector (x ω)) := by
  exact ((WithLp.measurable_toLp 2 (Fin (Fintype.card ι) → ℂ)).comp
    (Measurable.of_eval fun j => (hx ((Fintype.equivFin ι).symm j)).measurable)).stronglyMeasurable

theorem packVector_apply {ι : Type*} [Fintype ι] (x : ι → ℂ)
    (j : Fin (Fintype.card ι)) : packVector x j = x ((Fintype.equivFin ι).symm j) := rfl

theorem packVector_smul {ι : Type*} [Fintype ι] (a : ℂ) (x : ι → ℂ) :
    packVector (fun i => a * x i) = a • packVector x := by
  ext j
  rfl

theorem packVector_add {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    packVector (fun i => x i + y i) = packVector x + packVector y := by
  ext j
  rfl

theorem packVector_sum {ι α : Type*} [Fintype ι] (s : Finset α) (x : α → ι → ℂ) :
    packVector (fun i => ∑ k ∈ s, x k i) = ∑ k ∈ s, packVector (x k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext j
    simp [packVector]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    rw [packVector_add, ih]

theorem packVector_tensor_norm {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    ‖packVector (fun ij : ι × ι => x ij.1 * x ij.2)‖ = ∑ i, ‖x i‖ ^ 2 := by
  have hmass : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (sq_eq_sq₀ (norm_nonneg _) hmass).mp
  rw [packVector_norm_sq, Fintype.sum_prod_type, pow_two]
  simp only [norm_mul, mul_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem packVector_row_norm {ι : Type*} [Fintype ι] (a : ℂ) (x : ι → ℂ) :
    ‖packVector (fun i => a * x i)‖ = ‖a‖ * Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  rw [packVector_smul, norm_smul, ← packVector_norm_sq x, Real.sqrt_sq (norm_nonneg _)]

/-- Removing either endpoint costs at most twice the outside column mass. -/
theorem rankOne_exterior_square_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset ι) (x : ι → ℂ) :
    ∑ i, ∑ j, (if i ∉ Q ∨ j ∉ Q then ‖x i * x j‖ ^ 2 else 0) ≤
      2 * (∑ i ∈ Finset.univ \ Q, ‖x i‖ ^ 2) * ∑ i, ‖x i‖ ^ 2 := by
  classical
  have hterm : ∀ i j,
      (if i ∉ Q ∨ j ∉ Q then ‖x i * x j‖ ^ 2 else 0) ≤
      (if i ∉ Q then ‖x i‖ ^ 2 * ‖x j‖ ^ 2 else 0) +
      (if j ∉ Q then ‖x i‖ ^ 2 * ‖x j‖ ^ 2 else 0) := by
    intro i j
    simp only [norm_mul, mul_pow]
    by_cases hi : i ∈ Q <;> by_cases hj : j ∈ Q <;> simp [hi, hj] <;> positivity
  calc
    _ ≤ ∑ i, ∑ j,
        ((if i ∉ Q then ‖x i‖ ^ 2 * ‖x j‖ ^ 2 else 0) +
          (if j ∉ Q then ‖x i‖ ^ 2 * ‖x j‖ ^ 2 else 0)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
      have hfilter : Finset.univ.filter (fun i => i ∉ Q) = Finset.univ \ Q := by
        ext i
        simp
      have hleft : (∑ i, ∑ j, if i ∉ Q then ‖x i‖ ^ 2 * ‖x j‖ ^ 2 else 0) =
          (∑ i ∈ Finset.univ \ Q, ‖x i‖ ^ 2) * ∑ i, ‖x i‖ ^ 2 := by
        simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.mul_sum]
        rw [← Finset.sum_filter, hfilter, ← Finset.sum_mul]
      have hright : (∑ i, ∑ j, if j ∉ Q then ‖x i‖ ^ 2 * ‖x j‖ ^ 2 else 0) =
          (∑ i, ‖x i‖ ^ 2) * ∑ i ∈ Finset.univ \ Q, ‖x i‖ ^ 2 := by
        calc
          _ = ∑ i, ‖x i‖ ^ 2 * ∑ j, if j ∉ Q then ‖x j‖ ^ 2 else 0 := by
            simp only [Finset.mul_sum, mul_ite, mul_zero]
          _ = _ := by rw [← Finset.sum_filter, hfilter, ← Finset.sum_mul]
      simp only [Finset.sum_add_distrib, hleft, hright]
      ring

theorem sum_norm_le_sqrt_card_mul_square {α E : Type*} [SeminormedAddCommGroup E]
    (s : Finset α) (x : α → E) :
    ∑ k ∈ s, ‖x k‖ ≤ Real.sqrt ((s.card : ℝ) * ∑ k ∈ s, ‖x k‖ ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun k => ‖x k‖)
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem sum_product_square_le {α : Type*} (s : Finset α) (x y : α → ℂ) (H : ℝ)
    (hx : ∑ k ∈ s, ‖x k‖ ^ 4 ≤ H) (hy : ∑ k ∈ s, ‖y k‖ ^ 4 ≤ H) :
    ∑ k ∈ s, ‖x k * y k‖ ^ 2 ≤ H := by
  have ht : ∀ k, 2 * ‖x k * y k‖ ^ 2 ≤ ‖x k‖ ^ 4 + ‖y k‖ ^ 4 := by
    intro k
    rw [norm_mul, mul_pow]
    nlinarith [sq_nonneg (‖x k‖ ^ 2 - ‖y k‖ ^ 2)]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ s) => ht k)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  linarith

theorem product_norm_le_sqrt_fourth (x y : ℂ) (H : ℝ)
    (hx : ‖x‖ ^ 4 ≤ H) (hy : ‖y‖ ^ 4 ≤ H) : ‖x * y‖ ≤ Real.sqrt H := by
  apply Real.le_sqrt_of_sq_le
  rw [norm_mul, mul_pow]
  nlinarith [sq_nonneg (‖x‖ ^ 2 - ‖y‖ ^ 2)]

theorem compress_square_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset ι) (x : ι → ℂ) :
    ∑ i : {i // i ∈ Q}, ‖x i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  rw [Finset.sum_coe_sort Q (fun i => ‖x i‖ ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => sq_nonneg _)

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.packVector_tensor_norm
#print axioms AndersonAC.AgentS6Budget.rankOne_exterior_square_le
