import AndersonAC.AgentS6Budget.Predictable
import AndersonAC.S6.ResolventBounds

noncomputable section
open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory
set_option maxHeartbeats 1000000

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

def heatColumn (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) (i : Fin n) : ℂ :=
  (survivorEvent q k i).indicator
    (fun ω => scaledInverse t (q.state k ω).hatG i (q.pivot k ω)) ω

theorem heatColumn_adapted (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    StronglyMeasurable[q.history k] (fun ω => heatColumn q k ω i) :=
  (stronglyMeasurable_const.mul (pivot_left_adapted q k i)).indicator
    (survivorEvent_measurable q k i)

theorem heatColumn_norm_le (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (i : Fin n) :
    ‖heatColumn q k ω i‖ ≤ ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ := by
  by_cases h : ω ∈ survivorEvent q k i <;> simp [heatColumn, h]

theorem heatColumn_eq_zero_of_not_running (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (hk : ¬ k < q.stop ω) (i : Fin n) : heatColumn q k ω i = 0 := by
  apply Set.indicator_of_notMem
  exact fun h => hk h.1

theorem trialInverse_symm (s : TrialState core) (t : ℝ) (r : Fin n → ℂ) :
    (trialInverse t r s).IsSymm := by
  unfold trialInverse activeInverse dampedMatrix
  exact ((s.symmetric.map Complex.ofReal).sub
    ((Matrix.isSymm_diagonal (fun i : {i // i ∈ s.active} => r i)).smul (t : ℂ))).inv

theorem heatColumn_entryFactor (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (k : ℕ) (ω : Ω) (i j : Fin n) :
    entryFactor q k i j ω = heatColumn q k ω i * heatColumn q k ω j / (Real.sqrt t : ℂ) := by
  classical
  by_cases hi : ω ∈ survivorEvent q k i
  · by_cases hj : ω ∈ survivorEvent q k j
    · have hk := hi.1
      have hia := active_antitone q ω (by omega : k ≤ k + 1) (by omega)
        ((mem_survivorEvent q k ω i).mp hi).2
      have hja := active_antitone q ω (by omega : k ≤ k + 1) (by omega)
        ((mem_survivorEvent q k ω j).mp hj).2
      have hx := (q.heat k ω hk).choose
      have hsym : (q.state k ω).hatG (q.pivot k ω) j =
          (q.state k ω).hatG j (q.pivot k ω) := by
        rw [hatG_eq_trialInverse q k ω hk.le ⟨_, hx⟩ ⟨j, hja⟩,
          hatG_eq_trialInverse q k ω hk.le ⟨j, hja⟩ ⟨_, hx⟩]
        exact (trialInverse_symm (q.state k ω) t (r ω)).apply _ _
      simp only [entryFactor, heatColumn, Set.indicator_of_mem hi, Set.indicator_of_mem hj,
        Set.indicator_of_mem (show ω ∈ survivorEvent q k i ∩ survivorEvent q k j from ⟨hi, hj⟩),
        scaledInverse, Matrix.smul_apply, smul_eq_mul, hsym]
      have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
      field_simp <;> ring
    · simp [entryFactor, heatColumn, hj]
  · simp [entryFactor, heatColumn, hi]

theorem heatColumn_fourth_le (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (C : ℝ)
    (hpre : ∀ k ω, k < q.stop ω → HeatPrestate t C
      (fun i : {i // i ∈ (q.state k ω).active} => r ω i) (trialInverse t (r ω) (q.state k ω)))
    (k : ℕ) (ω : Ω) (i : Fin n) : ‖heatColumn q k ω i‖ ^ 4 ≤ fourthCap t := by
  by_cases hi : ω ∈ survivorEvent q k i
  · have hk := hi.1
    have hia := active_antitone q ω (by omega : k ≤ k + 1) (by omega)
      ((mem_survivorEvent q k ω i).mp hi).2
    have hx := (q.heat k ω hk).choose
    rw [heatColumn, Set.indicator_of_mem hi]
    have he : scaledInverse t (q.state k ω).hatG i (q.pivot k ω) =
        scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hia⟩ ⟨q.pivot k ω, hx⟩ := by
      simp only [scaledInverse, Matrix.smul_apply]
      rw [hatG_eq_trialInverse q k ω hk.le ⟨i, hia⟩ ⟨_, hx⟩]
    rw [he]
    have hsingle :
        ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hia⟩ ⟨q.pivot k ω, hx⟩‖ ^ 4 ≤
        ∑ j : {j // j ∈ (q.state k ω).active},
          ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hia⟩ j‖ ^ 4 :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j : {j // j ∈ (q.state k ω).active} =>
          ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hia⟩ j‖ ^ 4)
        (fun _ _ => pow_nonneg (norm_nonneg _) 4)
        (Finset.mem_univ (⟨q.pivot k ω, hx⟩ : {j // j ∈ (q.state k ω).active}))
    exact hsingle.trans ((hpre k ω hk).2.2 ⟨i, hia⟩)
  · simp only [heatColumn, Set.indicator_of_notMem hi, norm_zero, zero_pow (by decide : 4 ≠ 0)]
    exact Real.rpow_nonneg ht.le _

theorem heatColumn_square_sum_le (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hb : ∀ ω i, c ≤ (r ω i).im)
    (hpre : ∀ k ω, k < q.stop ω → HeatPrestate t C
      (fun i : {i // i ∈ (q.state k ω).active} => r ω i) (trialInverse t (r ω) (q.state k ω)))
    (k : ℕ) (ω : Ω) : ∑ i, ‖heatColumn q k ω i‖ ^ 2 ≤ C / c := by
  classical
  by_cases hk : k < q.stop ω
  · let A := {i // i ∈ (q.state k ω).active}
    have hx := (q.heat k ω hk).choose
    have hw : (t : ℂ) • (trialInverse t (r ω) (q.state k ω) *
        Matrix.diagonal (fun i : A => ((r ω i).im : ℂ)) *
        (trialInverse t (r ω) (q.state k ω))ᴴ) =
        matrixImag (trialInverse t (r ω) (q.state k ω)) := by
      have hmap : AndersonAC.S2.realMatrix (q.state k ω).M = (q.state k ω).M.map Complex.ofReal := by
        ext i j
        rfl
      have hw0 := AndersonAC.SolS2.unnormalized_ward (q.state k ω).M (q.state k ω).symmetric ht
        (fun i : A => r ω i) (fun i => hc.trans_le (hb ω i))
      unfold AndersonAC.S2.resolvent AndersonAC.S2.dampedMatrix at hw0
      rw [hmap] at hw0
      simpa only [AndersonAC.S2.hermitianImaginary, matrixImag,
        AndersonAC.Blueprint.matrixImag, one_div, trialInverse, activeInverse, dampedMatrix] using hw0
    have hrow := (AndersonAC.S6.ward_row_bound t c C (fun i : A => (r ω i).im)
      (trialInverse t (r ω) (q.state k ω)) ht hc (fun i => hb ω i)
      (fun i => by linarith [(hpre k ω hk).1 i, norm_nonneg (r ω i)]) hw ⟨_, hx⟩).2
    calc
      ∑ i, ‖heatColumn q k ω i‖ ^ 2
          = ∑ i ∈ (q.state k ω).active, ‖heatColumn q k ω i‖ ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp only [heatColumn, Set.indicator_of_notMem (show ω ∉ survivorEvent q k i from
          fun h => hi (active_antitone q ω (by omega : k ≤ k + 1) (by omega)
            ((mem_survivorEvent q k ω i).mp h).2)), norm_zero, zero_pow (by decide : 2 ≠ 0)]
      _ ≤ ∑ i ∈ (q.state k ω).active,
          ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (heatColumn_norm_le q k ω i) 2
      _ = sqRow (scaledInverse t (trialInverse t (r ω) (q.state k ω))) ⟨_, hx⟩ := by
        rw [← Finset.sum_coe_sort]
        unfold sqRow
        apply Finset.sum_congr rfl
        intro i _
        simp only [scaledInverse, Matrix.smul_apply]
        rw [hatG_eq_trialInverse q k ω hk.le i ⟨_, hx⟩,
          (trialInverse_symm (q.state k ω) t (r ω)).apply i ⟨_, hx⟩]
      _ ≤ C / c := hrow
  · simp only [heatColumn_eq_zero_of_not_running q k ω hk, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact div_nonneg hC hc.le

theorem heatColumn_fourth_sum_le (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hstart : ∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t)
    (ω : Ω) (i : Fin n) :
    ∑ k ∈ Finset.range (heatLimit t), ‖heatColumn q k ω i‖ ^ 4 ≤ 16 * fourthCap t := by
  calc
    ∑ k ∈ Finset.range (heatLimit t), ‖heatColumn q k ω i‖ ^ 4
        = ∑ k ∈ Finset.range (q.stop ω), ‖heatColumn q k ω i‖ ^ 4 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (q.finite_stop ω))
      intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [heatColumn_eq_zero_of_not_running q k ω (by omega), norm_zero]
      norm_num
    _ ≤ ∑ k ∈ Finset.range (q.stop ω),
        ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 4 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (heatColumn_norm_le q k ω i) 4
    _ ≤ 16 * fourthCap t := by
      have h := pivot_fourth_sum_le q ω ht ht1 (hstart ω) (q.stop ω) le_rfl i
      rw [← Finset.sum_range (fun k : ℕ =>
        ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 4)] at h
      exact h

theorem heatColumn_square_time_sum_le (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hstart : ∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t)
    (ω : Ω) (i : Fin n) :
    ∑ k ∈ Finset.range (heatLimit t), ‖heatColumn q k ω i‖ ^ 2 ≤
      4 * t ^ ((27 / 100) * delta) := by
  calc
    ∑ k ∈ Finset.range (heatLimit t), ‖heatColumn q k ω i‖ ^ 2
        = ∑ k ∈ Finset.range (q.stop ω), ‖heatColumn q k ω i‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (q.finite_stop ω))
      intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [heatColumn_eq_zero_of_not_running q k ω (by omega), norm_zero]
      norm_num
    _ ≤ ∑ k ∈ Finset.range (q.stop ω),
        ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (heatColumn_norm_le q k ω i) 2
    _ ≤ 4 * t ^ ((27 / 100) * delta) := by
      have h := pivot_square_sum_le q ω ht ht1 (hstart ω) (q.stop ω) le_rfl i
      rw [← Finset.sum_range (fun k : ℕ =>
        ‖scaledInverse t (q.state k ω).hatG i (q.pivot k ω)‖ ^ 2)] at h
      exact h

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.heatColumn_entryFactor
#print axioms AndersonAC.AgentS6Budget.heatColumn_square_sum_le
#print axioms AndersonAC.AgentS6Budget.heatColumn_fourth_le
#print axioms AndersonAC.AgentS6Budget.heatColumn_fourth_sum_le
#print axioms AndersonAC.AgentS6Budget.heatColumn_square_time_sum_le
