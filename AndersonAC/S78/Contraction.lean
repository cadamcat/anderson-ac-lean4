import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open scoped NNReal Topology
open Filter
set_option autoImplicit false

namespace AndersonAC.SolS78

/-- Banach's theorem on a closed sup-norm ball. The center need not be fixed. -/
theorem fixedPoint_closedBall_with_iterates {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : E → E) (r : E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hball : ∀ z, ‖z - r‖ ≤ ρ → ‖F z - r‖ ≤ ρ)
    (hcontract : ∀ z w, ‖z - r‖ ≤ ρ → ‖w - r‖ ≤ ρ →
      ‖F z - F w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖) :
    ∃ z, ‖z - r‖ ≤ ρ ∧ F z = z ∧
      Tendsto (fun n : ℕ => F^[n] r) atTop (𝓝 z) := by
  let S := Metric.closedBall r ρ
  have hmem (z : E) : z ∈ S ↔ ‖z - r‖ ≤ ρ := by
    simp only [S, Metric.mem_closedBall, dist_eq_norm]
  have hmap : Set.MapsTo F S S := by
    intro z hz
    exact (hmem (F z)).mpr (hball z ((hmem z).mp hz))
  have hLip : LipschitzWith (1 / 2 : ℝ≥0) (hmap.restrict F S S) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [Subtype.dist_eq, Set.MapsTo.val_restrict_apply, dist_eq_norm, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat] using hcontract z.val w.val ((hmem z.val).mp z.property) ((hmem w.val).mp w.property)
  have hf : ContractingWith (1 / 2 : ℝ≥0) (hmap.restrict F S S) :=
    ⟨by norm_num, hLip⟩
  have hr : r ∈ S := by simpa [S] using hρ
  obtain ⟨z, hz, hfixed, hlim, _⟩ :=
    ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete) hmap hf hr
      (edist_ne_top r (F r))
  exact ⟨z, (hmem z).mp hz, hfixed, hlim⟩

/-- Fixed-point existence, with the iteration information discarded. -/
theorem fixedPoint_closedBall {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : E → E) (r : E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hball : ∀ z, ‖z - r‖ ≤ ρ → ‖F z - r‖ ≤ ρ)
    (hcontract : ∀ z w, ‖z - r‖ ≤ ρ → ‖w - r‖ ≤ ρ →
      ‖F z - F w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖) :
    ∃ z, ‖z - r‖ ≤ ρ ∧ F z = z := by
  obtain ⟨z, hz, hfixed, _⟩ := fixedPoint_closedBall_with_iterates F r ρ hρ hball hcontract
  exact ⟨z, hz, hfixed⟩

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.fixedPoint_closedBall_with_iterates
#print axioms AndersonAC.SolS78.fixedPoint_closedBall
