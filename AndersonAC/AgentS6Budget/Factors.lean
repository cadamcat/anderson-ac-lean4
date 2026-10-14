import AndersonAC.AgentS6Budget.RankOne

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace AndersonAC.AgentS6Budget

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

def entryVector (u : ℕ → Ω → ι → ℂ) (t : ℝ) (i j : ι) (k : ℕ) (ω : Ω) :=
  packVector (fun _ : Unit => u k ω i * u k ω j / (Real.sqrt t : ℂ))

def rowVector (u : ℕ → Ω → ι → ℂ) (Q : Finset ι) (i : ι) (k : ℕ) (ω : Ω) :=
  packVector (fun j : {j // j ∈ Q} => u k ω i * u k ω j)

def matrixVector (u : ℕ → Ω → ι → ℂ) (Q : Finset ι) (k : ℕ) (ω : Ω) :=
  packVector (fun ij : {i // i ∈ Q} × {j // j ∈ Q} => u k ω ij.1 * u k ω ij.2)

theorem entryVector_norm_sq (u : ℕ → Ω → ι → ℂ) {t : ℝ} (ht : 0 < t)
    (i j : ι) (k : ℕ) (ω : Ω) :
    ‖entryVector u t i j k ω‖ ^ 2 = ‖u k ω i * u k ω j‖ ^ 2 / t := by
  rw [entryVector, packVector_norm_sq]
  simp only [Fintype.sum_unique, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg t), div_pow, Real.sq_sqrt ht.le]

theorem entryVector_bounds (u : ℕ → Ω → ι → ℂ) {t : ℝ} (ht : 0 < t)
    (N : ℕ) (H : ℝ)
    (hfourth : ∀ k ω i, ‖u k ω i‖ ^ 4 ≤ H)
    (htime : ∀ ω i, ∑ k ∈ Finset.range N, ‖u k ω i‖ ^ 4 ≤ 16 * H) (i j : ι) :
    (∀ k ω, ‖entryVector u t i j k ω‖ ≤ Real.sqrt (H / t)) ∧
    (∀ ω, ∑ k ∈ Finset.range N, ‖entryVector u t i j k ω‖ ^ 2 ≤ 16 * H / t) := by
  refine ⟨?_, ?_⟩
  · intro k ω
    apply Real.le_sqrt_of_sq_le
    rw [entryVector_norm_sq u ht]
    apply div_le_div_of_nonneg_right _ ht.le
    rw [norm_mul, mul_pow]
    nlinarith [hfourth k ω i, hfourth k ω j,
      sq_nonneg (‖u k ω i‖ ^ 2 - ‖u k ω j‖ ^ 2)]
  · intro ω
    simp only [entryVector_norm_sq u ht, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (sum_product_square_le (Finset.range N) (fun k => u k ω i) (fun k => u k ω j)
        (16 * H) (htime ω i) (htime ω j)) ht.le

theorem rowVector_norm_sq (u : ℕ → Ω → ι → ℂ) (Q : Finset ι) (i : ι)
    (k : ℕ) (ω : Ω) :
    ‖rowVector u Q i k ω‖ ^ 2 = ‖u k ω i‖ ^ 2 *
      ∑ j : {j // j ∈ Q}, ‖u k ω j‖ ^ 2 := by
  rw [rowVector, packVector_row_norm, mul_pow, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rowVector_bounds (u : ℕ → Ω → ι → ℂ) (Q : Finset ι) (N : ℕ) (H W B : ℝ)
    (hW : 0 ≤ W) (hfourth : ∀ k ω i, ‖u k ω i‖ ^ 4 ≤ H)
    (hmass : ∀ k ω, ∑ i, ‖u k ω i‖ ^ 2 ≤ W)
    (htime : ∀ ω i, ∑ k ∈ Finset.range N, ‖u k ω i‖ ^ 2 ≤ B) (i : ι) :
    (∀ k ω, ‖rowVector u Q i k ω‖ ≤ Real.sqrt (W * Real.sqrt H)) ∧
    (∀ ω, ∑ k ∈ Finset.range N, ‖rowVector u Q i k ω‖ ^ 2 ≤ W * B) := by
  have hcompressed : ∀ k ω, (∑ j : {j // j ∈ Q}, ‖u k ω j‖ ^ 2) ≤ W :=
    fun k ω => (compress_square_le Q (u k ω)).trans (hmass k ω)
  have hstep : ∀ k ω, ‖rowVector u Q i k ω‖ ^ 2 ≤ W * ‖u k ω i‖ ^ 2 := by
    intro k ω
    rw [rowVector_norm_sq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcompressed k ω) (sq_nonneg ‖u k ω i‖)
  refine ⟨?_, ?_⟩
  · intro k ω
    apply Real.le_sqrt_of_sq_le
    have hroot : ‖u k ω i‖ ^ 2 ≤ Real.sqrt H := by
      apply Real.le_sqrt_of_sq_le
      simpa only [← pow_mul] using hfourth k ω i
    exact (hstep k ω).trans (mul_le_mul_of_nonneg_left hroot hW)
  · intro ω
    calc
      _ ≤ ∑ k ∈ Finset.range N, W * ‖u k ω i‖ ^ 2 := Finset.sum_le_sum fun k _ => hstep k ω
      _ = W * ∑ k ∈ Finset.range N, ‖u k ω i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ W * B := mul_le_mul_of_nonneg_left (htime ω i) hW

theorem matrixVector_norm (u : ℕ → Ω → ι → ℂ) (Q : Finset ι) (k : ℕ) (ω : Ω) :
    ‖matrixVector u Q k ω‖ = ∑ i : {i // i ∈ Q}, ‖u k ω i‖ ^ 2 := by
  unfold matrixVector
  exact packVector_tensor_norm (fun i : {i // i ∈ Q} => u k ω i)

theorem matrixVector_bounds (u : ℕ → Ω → ι → ℂ) (Q : Finset ι) (N : ℕ) (W : ℝ)
    (hmass : ∀ k ω, ∑ i, ‖u k ω i‖ ^ 2 ≤ W) :
    (∀ k ω, ‖matrixVector u Q k ω‖ ≤ W) ∧
    (∀ ω, ∑ k ∈ Finset.range N, ‖matrixVector u Q k ω‖ ^ 2 ≤ (N : ℝ) * W ^ 2) := by
  have hstep : ∀ k ω, ‖matrixVector u Q k ω‖ ≤ W := by
    intro k ω
    rw [matrixVector_norm]
    exact (compress_square_le Q (u k ω)).trans (hmass k ω)
  refine ⟨hstep, fun ω => ?_⟩
  calc
    _ ≤ ∑ k ∈ Finset.range N, W ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hstep k ω) 2
    _ = _ := by simp

theorem entryVector_adapted [MeasurableSpace Ω] (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (u : ℕ → Ω → ι → ℂ) (hu : ∀ k i, StronglyMeasurable[F k] (fun ω => u k ω i))
    (t : ℝ) (i j : ι) (k : ℕ) : StronglyMeasurable[F k] (entryVector u t i j k) :=
  packVector_adapted _ (fun _ => ((hu k i).mul (hu k j)).div stronglyMeasurable_const)

theorem rowVector_adapted [MeasurableSpace Ω] (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (u : ℕ → Ω → ι → ℂ) (hu : ∀ k i, StronglyMeasurable[F k] (fun ω => u k ω i))
    (Q : Finset ι) (i : ι) (k : ℕ) : StronglyMeasurable[F k] (rowVector u Q i k) :=
  packVector_adapted _ (fun j => (hu k i).mul (hu k j))

theorem matrixVector_adapted [MeasurableSpace Ω] (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (u : ℕ → Ω → ι → ℂ) (hu : ∀ k i, StronglyMeasurable[F k] (fun ω => u k ω i))
    (Q : Finset ι) (k : ℕ) : StronglyMeasurable[F k] (matrixVector u Q k) :=
  packVector_adapted _ (fun ij => (hu k ij.1).mul (hu k ij.2))

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.entryVector_bounds
#print axioms AndersonAC.AgentS6Budget.rowVector_bounds
#print axioms AndersonAC.AgentS6Budget.matrixVector_bounds
