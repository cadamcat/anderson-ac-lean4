import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.EnergyInputs
import AndersonAC.S78BridgeEnergy.Basic
import AndersonAC.S78BridgeEnergy.Weights
import AndersonAC.S78BridgeEnergy.FarWeight
import AndersonAC.S78BridgeEnergy.Near

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- Three-term split for the far trial difference. -/
theorem far_diff_three (a0 a1 a2 : ℝ) :
    (a0 + a1 + a2) ^ 2 ≤ 3 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) :=
  add3_sq_le a0 a1 a2

/-- Per-operation far part is bounded by three weighted sums. -/
theorem far_part_three {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C₀ : ℝ)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C₀)
    (a : Fin k) (f α v : Torus d m → ℝ)
    (hf : ∀ i ∈ (I.state a.succ).active, f i = α i + v i) :
    ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 ≤
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
  classical
  have hWnn : ∀ i ∈ (I.state a.succ).active.filter
      (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
      0 ≤ ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 := by
    intro i _
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (mul_nonneg (hdamp i).1 (hdamp x).1) (sq_nonneg _)
  have hpoint : ∀ i ∈ (I.state a.succ).active.filter
      (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
      (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
        (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 ≤
      (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
        (3 * ((α i) ^ 2 + (v i - v (I.anchor a)) ^ 2 +
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) := by
    intro i hi
    have hiA : i ∈ (I.state a.succ).active := (Finset.mem_filter.mp hi).1
    have hfi : f i = α i + v i := hf i hiA
    have hsplit : f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v =
        α i + (v i - v (I.anchor a)) +
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) := by
      rw [hfi]; ring
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ (hWnn i hi)
    exact far_diff_three _ _ _
  have hsum := Finset.sum_le_sum (s := (I.state a.succ).active.filter
      (· ∉ cube d m (I.anchor a) (100 * I.Ds))) (fun i hi => hpoint i hi)
  have hsplit_sum : (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (3 * ((α i) ^ 2 + (v i - v (I.anchor a)) ^ 2 +
            (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2))) =
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
    have heq : ∀ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (3 * ((α i) ^ 2 + (v i - v (I.anchor a)) ^ 2 +
            (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) =
        (3 * ((∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) +
          3 * ((∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
            (v i - v (I.anchor a)) ^ 2) +
          3 * ((∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
            (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) := by
      intro i _
      ring
    rw [Finset.sum_congr rfl (fun i hi => heq i hi)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  exact hsum.trans_eq hsplit_sum

/-- Summed far part over operations. -/
theorem far_total_three {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C₀ : ℝ)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C₀)
    (S : Finset (Fin k)) (f α v : Torus d m → ℝ)
    (hf : ∀ a ∈ S, ∀ i ∈ (I.state a.succ).active, f i = α i + v i) :
    ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 ≤
      3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) +
      3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2) +
      3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
  classical
  have hper : ∀ a ∈ S,
      ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 ≤
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
    intro a ha
    exact far_part_three I C₀ hdamp a f α v (hf a ha)
  calc ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2
      ≤ ∑ a ∈ S, (3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2) +
      3 * (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) :=
        Finset.sum_le_sum fun a ha => hper a ha
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

end AndersonAC.S78BridgeEnergy
