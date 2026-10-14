import AndersonAC.AgentS6Budget.Telescope
import AndersonAC.AgentS6Budget.Compression
import AndersonAC.AgentS6Budget.FarField

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
def exteriorVector (Q : Finset ι) (u : ι → ℂ) :=
  packVector (fun ij : ι × ι => if ij.1 ∉ Q ∨ ij.2 ∉ Q then u ij.1 * u ij.2 else 0)

theorem exteriorVector_norm_le (Q : Finset ι) (u : ι → ℂ) (F W : ℝ)
    (hF : 0 ≤ F) (hW : 0 ≤ W)
    (hout : ∑ i ∈ Finset.univ \ Q, ‖u i‖ ^ 2 ≤ F) (hmass : ∑ i, ‖u i‖ ^ 2 ≤ W) :
    ‖exteriorVector Q u‖ ≤ Real.sqrt (2 * F * W) := by
  classical
  apply Real.le_sqrt_of_sq_le
  rw [exteriorVector, packVector_norm_sq, Fintype.sum_prod_type]
  simp only [apply_ite, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  have hp := mul_le_mul hout hmass (Finset.sum_nonneg fun _ _ => sq_nonneg _) hF
  exact (rankOne_exterior_square_le Q u).trans (by nlinarith)

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

theorem stop_exterior_eq_sum (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (Q : Finset (Fin n)) :
    frobVector (scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) -
      compressMatrix Q (scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω))) =
      ∑ k ∈ Finset.range (heatLimit t), runningCoefficient q k ω • exteriorVector Q (heatColumn q k ω) := by
  classical
  calc
    _ = packVector (fun ij : Fin n × Fin n => ∑ k ∈ Finset.range (heatLimit t),
        runningCoefficient q k ω *
          (if ij.1 ∉ Q ∨ ij.2 ∉ Q then heatColumn q k ω ij.1 * heatColumn q k ω ij.2 else 0)) := by
      unfold frobVector
      congr 1
      funext ij
      by_cases hij : ij.1 ∈ Q ∧ ij.2 ∈ Q
      · simp [compressMatrix, hij, hij.1, hij.2]
      · have hout : ij.1 ∉ Q ∨ ij.2 ∉ Q := by tauto
        simp only [Matrix.sub_apply, compressMatrix, if_neg hij, sub_zero, if_pos hout]
        rw [scaled_stop_eq_sum q ht ω hr]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
      rw [packVector_sum]
      exact Finset.sum_congr rfl fun k _ => packVector_smul _ _

theorem cumulative_exterior_bound (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (Q : Finset (Fin n)) (L F W : ℝ)
    (hL : 0 ≤ L) (hF : 0 ≤ F) (hW : 0 ≤ W)
    (hcoef : ∀ k, ‖runningCoefficient q k ω‖ ≤ L)
    (hmass : ∀ k, ∑ i, ‖heatColumn q k ω i‖ ^ 2 ≤ W)
    (hfar : ∀ k, ∑ i ∈ Finset.univ \ Q, ‖heatColumn q k ω i‖ ^ 2 ≤ F) :
    ‖frobVector (scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) -
      compressMatrix Q (scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω)))‖ ≤
      (heatLimit t : ℝ) * L * Real.sqrt (2 * F * W) := by
  rw [stop_exterior_eq_sum q ht ω hr Q]
  calc
    _ ≤ ∑ k ∈ Finset.range (heatLimit t),
        ‖runningCoefficient q k ω • exteriorVector Q (heatColumn q k ω)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (heatLimit t), L * Real.sqrt (2 * F * W) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul (hcoef k) (exteriorVector_norm_le Q _ F W hF hW (hfar k) (hmass k))
        (norm_nonneg _) hL
    _ = _ := by simp; ring

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.cumulative_exterior_bound
