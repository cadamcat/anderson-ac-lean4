import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- `(a + b)^2 ≤ 2a^2 + 2b^2`. -/
theorem add_sq_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- `cubeGradient` is nonnegative. -/
theorem cubeGradient_nonneg (d m : ℕ) (Q : Finset (Torus d m)) (v : Torus d m → ℝ) :
    0 ≤ cubeGradient d m Q v := by
  unfold cubeGradient
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs with h
  · positivity
  · exact le_rfl

/-- Pointwise split of the trial difference. -/
theorem trial_diff_split (a b c : ℝ) : (a + b - c) ^ 2 ≤ 2 * a ^ 2 + 2 * (b - c) ^ 2 := by
  have h : a + b - c = a + (b - c) := by ring
  rw [h]
  exact add_sq_le_two a (b - c)

/-- General near-weight estimate from an abstract weighted deviation bound.
`c` is the cube mean; `l` is supported in `T`. -/
theorem near_weight_estimate {d m : ℕ} (z : Torus d m) (R Lmax Ltotal Cdev : ℝ)
    (l : Torus d m → ℝ) (α v : Torus d m → ℝ)
    (T : Finset (Torus d m))
    (hl_nonneg : ∀ i, 0 ≤ l i)
    (hl_le : ∀ i, l i ≤ Lmax)
    (hsupp : ∀ i, i ∉ T → l i = 0)
    (hdev : (∑ i, l i * (v i - localCubeMean d m z R v) ^ 2) ≤
      Cdev * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
        cubeGradient d m (cube d m z (2 * R)) v) :
    (∑ i, l i * ((α i + v i - localCubeMean d m z R v) ^ 2)) ≤
      2 * Lmax * (∑ i ∈ T, (α i) ^ 2) +
      2 * (Cdev * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
        cubeGradient d m (cube d m z (2 * R)) v) := by
  classical
  have hpoint : ∀ i, l i * ((α i + v i - localCubeMean d m z R v) ^ 2) ≤
      l i * (2 * (α i) ^ 2 + 2 * (v i - localCubeMean d m z R v) ^ 2) := by
    intro i
    apply mul_le_mul_of_nonneg_left _ (hl_nonneg i)
    exact trial_diff_split (α i) (v i) (localCubeMean d m z R v)
  have hsum : (∑ i, l i * ((α i + v i - localCubeMean d m z R v) ^ 2)) ≤
      (∑ i, l i * (2 * (α i) ^ 2 + 2 * (v i - localCubeMean d m z R v) ^ 2)) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hsplit : (∑ i, l i * (2 * (α i) ^ 2 + 2 * (v i - localCubeMean d m z R v) ^ 2)) =
      2 * (∑ i, l i * (α i) ^ 2) + 2 * (∑ i, l i * (v i - localCubeMean d m z R v) ^ 2) := by
    have heq : ∀ i : Torus d m,
        l i * (2 * (α i) ^ 2 + 2 * (v i - localCubeMean d m z R v) ^ 2) =
        2 * (l i * (α i) ^ 2) + 2 * (l i * (v i - localCubeMean d m z R v) ^ 2) := by
      intro i
      ring
    simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
  have halpha : (∑ i, l i * (α i) ^ 2) ≤ Lmax * (∑ i ∈ T, (α i) ^ 2) := by
    have hsub : (∑ i, l i * (α i) ^ 2) = ∑ i ∈ T, l i * (α i) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro i _ hi
      simp [hsupp i hi]
    rw [hsub]
    calc ∑ i ∈ T, l i * (α i) ^ 2
        ≤ ∑ i ∈ T, Lmax * (α i) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact hl_le i
      _ = Lmax * (∑ i ∈ T, (α i) ^ 2) := by rw [Finset.mul_sum]
  calc (∑ i, l i * ((α i + v i - localCubeMean d m z R v) ^ 2))
      ≤ 2 * (∑ i, l i * (α i) ^ 2) + 2 * (∑ i, l i * (v i - localCubeMean d m z R v) ^ 2) := by
        calc _ ≤ (∑ i, l i * (2 * (α i) ^ 2 + 2 * (v i - localCubeMean d m z R v) ^ 2)) := hsum
          _ = _ := hsplit
      _ ≤ 2 * (Lmax * (∑ i ∈ T, (α i) ^ 2)) +
          2 * (Cdev * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
            cubeGradient d m (cube d m z (2 * R)) v) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left halpha (by norm_num)
        · apply mul_le_mul_of_nonneg_left hdev (by norm_num)
      _ = _ := by ring

end AndersonAC.S78BridgeEnergy
