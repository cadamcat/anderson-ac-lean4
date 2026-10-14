import AndersonAC.AgentS6Budget.Coefficient
import AndersonAC.AgentS6Budget.HeatColumn
import AndersonAC.AgentS6Budget.Factors

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

theorem heatColumn_increment (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (k : ℕ) (ω : Ω) (hk : k < q.stop ω) (i j : Fin n) :
    (Real.sqrt t : ℂ) * hatIncrement q k ω i j =
      runningCoefficient q k ω * heatColumn q k ω i * heatColumn q k ω j := by
  have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have h := coefficient_times_entryFactor q k ω i j
  rw [if_pos hk, heatColumn_entryFactor q ht k ω i j] at h
  rw [runningCoefficient_of_running q k ω hk]
  rw [← h]
  field_simp <;> ring

theorem scaled_stop_eq_sum (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (i j : Fin n) :
    scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) i j =
      ∑ k ∈ Finset.range (heatLimit t),
        runningCoefficient q k ω * heatColumn q k ω i * heatColumn q k ω j := by
  have htel := hatG_telescope q ht ω hr (q.stop ω) le_rfl i j
  calc
    _ = (Real.sqrt t : ℂ) * ∑ k ∈ Finset.range (q.stop ω), hatIncrement q k ω i j := by
      simp only [scaledInverse, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, htel]
      ring
    _ = ∑ k ∈ Finset.range (q.stop ω),
        runningCoefficient q k ω * heatColumn q k ω i * heatColumn q k ω j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k hk => heatColumn_increment q ht k ω (Finset.mem_range.mp hk) i j
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (q.finite_stop ω))
      intro k _ hk
      have hkrun : ¬ k < q.stop ω := by simpa only [Finset.mem_range] using hk
      rw [runningCoefficient_of_stopped q k ω hkrun]
      simp

theorem stop_entry_eq_sum (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (i j : Fin n) :
    (q.state (q.stop ω) ω).hatG i j - g0 ω i j =
      ∑ k ∈ Finset.range (heatLimit t), runningCoefficient q k ω *
        (heatColumn q k ω i * heatColumn q k ω j / (Real.sqrt t : ℂ)) := by
  have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have hscaled := scaled_stop_eq_sum q ht ω hr i j
  calc
    _ = (∑ k ∈ Finset.range (heatLimit t),
        runningCoefficient q k ω * heatColumn q k ω i * heatColumn q k ω j) / (Real.sqrt t : ℂ) := by
      apply (eq_div_iff hs).mpr
      simpa only [scaledInverse, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_comm] using hscaled
    _ = _ := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring

theorem stop_rowVector_eq_sum (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (Q : Finset (Fin n)) (i : Fin n) :
    packVector (fun j : {j // j ∈ Q} => scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) i j) =
      ∑ k ∈ Finset.range (heatLimit t), runningCoefficient q k ω • rowVector (heatColumn q) Q i k ω := by
  calc
    _ = packVector (fun j : {j // j ∈ Q} => ∑ k ∈ Finset.range (heatLimit t),
        runningCoefficient q k ω * (heatColumn q k ω i * heatColumn q k ω j)) := by
      congr 1
      funext j
      rw [scaled_stop_eq_sum q ht ω hr]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
      rw [packVector_sum]
      exact Finset.sum_congr rfl fun k _ => packVector_smul _ _

theorem stop_matrixVector_eq_sum (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (Q : Finset (Fin n)) :
    packVector (fun ij : {i // i ∈ Q} × {j // j ∈ Q} =>
      scaledInverse t ((q.state (q.stop ω) ω).hatG - g0 ω) ij.1 ij.2) =
      ∑ k ∈ Finset.range (heatLimit t), runningCoefficient q k ω • matrixVector (heatColumn q) Q k ω := by
  calc
    _ = packVector (fun ij : {i // i ∈ Q} × {j // j ∈ Q} => ∑ k ∈ Finset.range (heatLimit t),
        runningCoefficient q k ω * (heatColumn q k ω ij.1 * heatColumn q k ω ij.2)) := by
      congr 1
      funext ij
      rw [scaled_stop_eq_sum q ht ω hr]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
      rw [packVector_sum]
      exact Finset.sum_congr rfl fun k _ => packVector_smul _ _

theorem stop_entryVector_norm (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (i j : Fin n) :
    ‖∑ k ∈ Finset.range (heatLimit t), runningCoefficient q k ω • entryVector (heatColumn q) t i j k ω‖ =
      ‖(q.state (q.stop ω) ω).hatG i j - g0 ω i j‖ := by
  have hvec : packVector (fun _ : Unit => (q.state (q.stop ω) ω).hatG i j - g0 ω i j) =
      ∑ k ∈ Finset.range (heatLimit t), runningCoefficient q k ω • entryVector (heatColumn q) t i j k ω := by
    rw [stop_entry_eq_sum q ht ω hr, packVector_sum]
    exact Finset.sum_congr rfl fun k _ => packVector_smul _ _
  rw [← hvec]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [packVector_norm_sq]
  simp

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.scaled_stop_eq_sum
#print axioms AndersonAC.AgentS6Budget.stop_entryVector_norm
