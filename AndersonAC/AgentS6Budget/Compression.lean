import AndersonAC.AgentS6Budget.RankOne
import AndersonAC.S6.Definitions

noncomputable section
open scoped BigOperators

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
def compressMatrix (Q : Finset ι) (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if i ∈ Q ∧ j ∈ Q then Z i j else 0

def frobVector (Z : Matrix ι ι ℂ) := packVector (fun ij : ι × ι => Z ij.1 ij.2)

theorem frobVector_norm_sq (Z : Matrix ι ι ℂ) : ‖frobVector Z‖ ^ 2 = hsSq Z := by
  rw [frobVector, packVector_norm_sq, Fintype.sum_prod_type]
  rfl

theorem entry_norm_le_frob (Z : Matrix ι ι ℂ) (i j : ι) : ‖Z i j‖ ≤ ‖frobVector Z‖ := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [frobVector_norm_sq]
  exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖Z i j‖) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖Z i j‖)
      (Finset.mem_univ i))

theorem row_norm_le_frob (Z : Matrix ι ι ℂ) (i : ι) : ‖packVector (Z i)‖ ≤ ‖frobVector Z‖ := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [packVector_norm_sq, frobVector_norm_sq]
  exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖Z i j‖)
    (Finset.mem_univ i)

theorem sum_mem_ite (Q : Finset ι) (f : ι → ℝ) :
    (∑ i, if i ∈ Q then f i else 0) = ∑ i ∈ Q, f i := by
  classical
  have hQ : Finset.univ.filter (fun i => i ∈ Q) = Q := by ext i; simp
  rw [← Finset.sum_filter, hQ]

theorem compress_row_norm (Q : Finset ι) (Z : Matrix ι ι ℂ) (i : ι) (hi : i ∈ Q) :
    ‖packVector ((compressMatrix Q Z) i)‖ =
      ‖packVector (fun j : {j // j ∈ Q} => Z i j)‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [packVector_norm_sq, packVector_norm_sq, Finset.sum_coe_sort Q (fun j => ‖Z i j‖ ^ 2)]
  simp only [compressMatrix, hi, true_and, apply_ite, norm_zero, ite_pow,
    zero_pow (by decide : 2 ≠ 0)]
  exact sum_mem_ite Q _

theorem compress_frob_norm (Q : Finset ι) (Z : Matrix ι ι ℂ) :
    ‖frobVector (compressMatrix Q Z)‖ =
      ‖packVector (fun ij : {i // i ∈ Q} × {j // j ∈ Q} => Z ij.1 ij.2)‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobVector_norm_sq, packVector_norm_sq, Fintype.sum_prod_type]
  have hR : (∑ i : {i // i ∈ Q}, ∑ j : {j // j ∈ Q}, ‖Z i j‖ ^ 2) =
      ∑ i ∈ Q, ∑ j ∈ Q, ‖Z i j‖ ^ 2 := by
    rw [Finset.sum_coe_sort Q (fun i => ∑ j : {j // j ∈ Q}, ‖Z i j‖ ^ 2)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_coe_sort Q (fun j => ‖Z i j‖ ^ 2)
  rw [hR]
  unfold hsSq sqRow
  calc
    _ = ∑ i, if i ∈ Q then ∑ j ∈ Q, ‖Z i j‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ Q
      · simp only [compressMatrix, hi, true_and, apply_ite, norm_zero, ite_pow,
          zero_pow (by decide : 2 ≠ 0), if_true]
        exact sum_mem_ite Q _
      · simp [compressMatrix, hi]
    _ = _ := sum_mem_ite Q _

theorem packVector_sub (x y : ι → ℂ) :
    packVector (fun i => x i - y i) = packVector x - packVector y := by
  ext j
  rfl

/-- Three compressed tests and a deterministic exterior Frobenius estimate imply all budgets. -/
theorem budgetsHold_of_compression (t : ℝ) (ht : 0 < t) (g0 hg : Matrix ι ι ℂ)
    (Q : Finset ι) (b : ℝ)
    (hentry : ∀ i ∈ Q, ∀ j ∈ Q,
      ‖scaledInverse t (hg - g0) i j‖ ≤ Real.sqrt t * entryBudget t / 2)
    (hrow : ∀ i ∈ Q,
      ‖packVector (fun j : {j // j ∈ Q} => scaledInverse t (hg - g0) i j)‖ ≤
        Real.sqrt (rowBudget t) / 2)
    (hfrob : ‖packVector (fun ij : {i // i ∈ Q} × {j // j ∈ Q} =>
      scaledInverse t (hg - g0) ij.1 ij.2)‖ ≤ Real.sqrt (frobeniusBudget t) / 2)
    (htail : ‖frobVector (scaledInverse t (hg - g0) -
      compressMatrix Q (scaledInverse t (hg - g0)))‖ ≤ b)
    (hbe : b ≤ Real.sqrt t * entryBudget t / 2)
    (hbr : b ≤ Real.sqrt (rowBudget t) / 2)
    (hbf : b ≤ Real.sqrt (frobeniusBudget t) / 2) : BudgetsHold t g0 hg := by
  classical
  let Z := scaledInverse t (hg - g0)
  let P := compressMatrix Q Z
  have hPentry : ∀ i j, ‖P i j‖ ≤ Real.sqrt t * entryBudget t / 2 := by
    intro i j
    by_cases hij : i ∈ Q ∧ j ∈ Q
    · simpa only [P, compressMatrix, if_pos hij] using hentry i hij.1 j hij.2
    · simp only [P, compressMatrix, if_neg hij, norm_zero]
      unfold entryBudget
      positivity
  have hProw : ∀ i, ‖packVector (P i)‖ ≤ Real.sqrt (rowBudget t) / 2 := by
    intro i
    by_cases hi : i ∈ Q
    · rw [show P = compressMatrix Q Z from rfl, compress_row_norm Q Z i hi]
      exact hrow i hi
    · have hz : P i = 0 := by funext j; simp [P, compressMatrix, hi]
      rw [hz]
      have hz' : packVector (0 : ι → ℂ) = 0 := by ext j; rfl
      rw [hz', norm_zero]
      positivity
  have hPfrob : ‖frobVector P‖ ≤ Real.sqrt (frobeniusBudget t) / 2 := by
    rw [show P = compressMatrix Q Z from rfl, compress_frob_norm Q Z]
    exact hfrob
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hZ : ‖Z i j‖ ≤ Real.sqrt t * entryBudget t := by
      have h := norm_le_norm_sub_add (Z i j) (P i j)
      have he := (entry_norm_le_frob (Z - P) i j).trans htail
      change ‖Z i j - P i j‖ ≤ b at he
      linarith [hPentry i j]
    have hs : ‖Z i j‖ = Real.sqrt t * ‖hg i j - g0 i j‖ := by
      simp [Z, scaledInverse, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
    rw [hs] at hZ
    exact le_of_mul_le_mul_left hZ (Real.sqrt_pos.mpr ht)
  · intro i
    have hZ : ‖packVector (Z i)‖ ≤ Real.sqrt (rowBudget t) := by
      have h := norm_le_norm_sub_add (packVector (Z i)) (packVector (P i))
      rw [← packVector_sub] at h
      have hr := (row_norm_le_frob (Z - P) i).trans htail
      change ‖packVector (fun j => Z i j - P i j)‖ ≤ b at hr
      linarith [hProw i]
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hZ 2
    rw [packVector_norm_sq, Real.sq_sqrt (by unfold rowBudget; positivity)] at hpow
    exact hpow
  · have hZ : ‖frobVector Z‖ ≤ Real.sqrt (frobeniusBudget t) := by
      have h := norm_le_norm_sub_add (frobVector Z) (frobVector P)
      have hsub : frobVector Z - frobVector P = frobVector (Z - P) := by
        exact (packVector_sub _ _).symm
      rw [hsub] at h
      linarith
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hZ 2
    rw [frobVector_norm_sq, Real.sq_sqrt (by unfold frobeniusBudget; positivity)] at hpow
    exact hpow

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.budgetsHold_of_compression
