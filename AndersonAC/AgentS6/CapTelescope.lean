import AndersonAC.AgentS6.InitialCap
import AndersonAC.AgentS6.Margins

/-! Deterministic cap argument (06-clearing.tex:1036–1052): if every prefix sum of the recorded
fixed-ridge row changes is at most `l_*/2` in absolute value, then at the stop every leverage at
the last heat ridge is at most `3 l_*`. The ridge is constant since the last lowering (or the
start), where every leverage was at most `2 l_*`. -/

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

theorem leverage_zero_row {R B : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
    (C : Matrix R B ℂ) (τ : ℝ) (i : R) (h : ∀ b, C i b = 0) : leverage C τ i = 0 := by
  unfold leverage ridgeProjection
  simp [Matrix.mul_apply, h]

theorem trialWeights_inactive {ι : Type*} [Fintype ι] [DecidableEq ι] {core : Finset ι}
    (t : ℝ) (r : ι → ℂ) (s : TrialState core) (τ : ℝ) (i : ι)
    (h : i ∉ s.active ∨ i ∈ core) : trialWeights t r s τ i = 0 := by
  unfold trialWeights
  apply leverage_zero_row
  intro b
  unfold trialCross
  rcases h with h | h
  · rw [dif_neg h]
  · by_cases hi : i ∈ s.active
    · rw [dif_pos hi, if_pos h]
    · rw [dif_neg hi]

theorem active_succ_subset (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω)
    (hk : k < q.stop ω) : (q.state (k + 1) ω).active ⊆ (q.state k ω).active := by
  obtain ⟨-, -, hact, -⟩ := q.heat k ω hk
  rw [hact]; exact Finset.erase_subset _ _

theorem active_antitone (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) {j m : ℕ}
    (hjm : j ≤ m) (hm : m ≤ q.stop ω) : (q.state m ω).active ⊆ (q.state j ω).active := by
  induction m, hjm using Nat.le_induction with
  | base => exact subset_rfl
  | succ m hjm ih =>
    exact (active_succ_subset q m ω (by omega)).trans (ih (by omega))

/-- Since the last lowering (or the start) the ridge is constant and all leverages were `≤ 2l`. -/
theorem last_lowering (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ht1 : t ≤ 1)
    (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (k : ℕ) (hk : k < q.stop ω) :
    ∃ j ≤ k, (∀ m, j ≤ m → m ≤ k → q.ridge m ω = q.ridge j ω) ∧
      ∀ i, trialWeights t (r ω) (q.state j ω) (q.ridge j ω) i ≤ 2 * leverageScale t := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, fun m _ hm => by rw [Nat.le_zero.mp hm], fun i => ?_⟩
    exact initial_weights_cap q ht ht1 ω hr hk i
  | succ k ih =>
    obtain ⟨j, hj, hconst, hcap⟩ := ih (by omega)
    have hrule := q.ridge_rule k ω hk
    have hτ := q.running_ridge k ω (by omega)
    have hτ' := q.running_ridge (k + 1) ω hk
    rw [hrule] at hτ'
    rcases chooseRidge_cap (trialCross t (r ω) (q.state (k + 1) ω)) hτ hτ' with h | h
    · refine ⟨j, by omega, fun m hjm hm => ?_, hcap⟩
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact hconst m hjm (by omega)
      · have : m = k + 1 := by omega
        rw [this, hrule, h]; exact hconst k hj le_rfl
    · refine ⟨k + 1, le_rfl, fun m h1 h2 => by rw [show m = k + 1 by omega], fun i => ?_⟩
      have := h i
      rw [← hrule] at this
      exact this

/-- Telescoping over a constant-ridge interval for a surviving exterior row. -/
theorem telescope (q : StoppedTrial (Ω := Ω) core t r g0 order) (ω : Ω) (j : ℕ) (i : Fin n)
    (hi : i ∉ core) : ∀ m, j ≤ m → m ≤ q.stop ω →
      (∀ k, j ≤ k → k < m → q.ridge k ω = q.ridge j ω) →
      i ∈ (q.state m ω).active →
      trialWeights t (r ω) (q.state m ω) (q.ridge j ω) i =
        trialWeights t (r ω) (q.state j ω) (q.ridge j ω) i +
          ∑ k ∈ Finset.Ico j m, recordedLeverageIncrement q k ω i := by
  intro m hjm
  induction m, hjm using Nat.le_induction with
  | base => intro _ _ _; simp
  | succ m hjm ih =>
    intro hm hconst hact
    have hmstop : m < q.stop ω := by omega
    have hact' : i ∈ (q.state m ω).active := active_succ_subset q m ω hmstop hact
    rw [Finset.sum_Ico_succ_top hjm, ← add_assoc,
      ← ih (by omega) (fun k h1 h2 => hconst k h1 (by omega)) hact']
    have hrid : q.ridge m ω = q.ridge j ω := hconst m hjm (by omega)
    unfold recordedLeverageIncrement
    rw [if_pos ⟨hmstop, hact, hi⟩, hrid]
    ring

theorem cap_of_prefix (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ht1 : t ≤ 1)
    (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (hstop : 0 < q.stop ω)
    (hpre : ∀ i, (∀ s, |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i| ≤
      leverageScale t / 2) ∨
      trialWeights t (r ω) (q.state (q.stop ω) ω) (q.ridge (q.stop ω - 1) ω) i ≤
        3 * leverageScale t) :
    maxWeight (trialWeights t (r ω) (q.state (q.stop ω) ω) (q.ridge (q.stop ω - 1) ω)) ≤
      3 * leverageScale t := by
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  obtain ⟨j, hj, hconst, hcap⟩ := last_lowering q ht ht1 ω hr (q.stop ω - 1) (by omega)
  refine maxWeight_le (by linarith) fun i => ?_
  rcases hpre i with hpre | hdirect
  swap; · exact hdirect
  rw [hconst (q.stop ω - 1) hj le_rfl]
  by_cases hz : i ∉ (q.state (q.stop ω) ω).active ∨ i ∈ core
  · rw [trialWeights_inactive _ _ _ _ i hz]; linarith
  · push_neg at hz
    obtain ⟨hact, hi⟩ := hz
    rw [telescope q ω j i hi (q.stop ω) (by omega) le_rfl
      (fun k h1 h2 => hconst k h1 (by omega)) hact]
    have hint := AndersonAC.S6.prefix_interval_bound (leverageScale t)
      (fun k => recordedLeverageIncrement q k ω i) hl.le hpre j (q.stop ω) (by omega)
    have := hcap i
    have habs := le_abs_self (∑ k ∈ Finset.Ico j (q.stop ω), recordedLeverageIncrement q k ω i)
    linarith

/-- A ridge rule that returns a nonpositive ridge has found no positive ridge with maximum `2l`;
then the zero-ridge leverages are at most `2l` as limits of positive-ridge ones. -/
theorem chooseRidge_nonpos_cap {B : Type*} [Fintype B] [DecidableEq B]
    (C : Matrix (Fin n) B ℂ) {l τ : ℝ} (hτ : 0 < τ) (hτ' : chooseRidge C l τ ≤ 0) (i : Fin n) :
    leverage C (chooseRidge C l τ) i ≤ 2 * l := by
  unfold chooseRidge at hτ' ⊢
  split_ifs at hτ' ⊢ with h
  swap; · linarith
  set S : Set ℝ := {s : ℝ | 0 < s ∧ 2 * l ≤ maxWeight (leverage C s)} with hS
  have hthr : ridgeThreshold C l = sSup S := rfl
  have hbdd : ∀ s ∈ S, s ≤ τ := by
    intro s hs
    by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    have := maxWeight_leverage_antitone C hτ hlt.le
    linarith [hs.2]
  have hempty : ∀ s, 0 < s → maxWeight (leverage C s) < 2 * l := by
    intro s hs
    by_contra hge
    have hsS : s ∈ S := ⟨hs, le_of_not_gt hge⟩
    have : s ≤ sSup S := le_csSup ⟨τ, hbdd⟩ hsS
    rw [← hthr] at this
    linarith
  have hSe : S = ∅ := by
    ext s; simp only [Set.mem_empty_iff_false, iff_false]
    intro hs; exact absurd hs.2 (not_le.mpr (hempty s hs.1))
  rw [hthr, hSe, Real.sSup_empty]
  have hpos : ∀ s, 0 < s → leverage C s i ≤ 2 * l := fun s hs =>
    ((le_maxWeight _ i).trans (hempty s hs).le)
  by_cases hdet : IsUnit (gram C).det
  · -- continuity of the ridge projection at zero
    have hA : ContinuousAt (fun A : Matrix B B ℂ => A⁻¹) (gram C) := by
      apply continuousAt_matrix_inv
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ ((isUnit_iff_ne_zero).mp hdet)
    have hG : Continuous (fun s : ℝ => ridgeGram C s) := by
      unfold ridgeGram
      exact continuous_const.add ((Complex.continuous_ofReal).smul continuous_const)
    have hG0 : ridgeGram C 0 = gram C := by simp [ridgeGram]
    have hcont : ContinuousAt (fun s : ℝ => leverage C s i) 0 := by
      unfold leverage ridgeProjection
      have h1 : ContinuousAt (fun s : ℝ => (ridgeGram C s)⁻¹) 0 := by
        exact ContinuousAt.comp_of_eq hA hG.continuousAt hG0
      have hK : Continuous (fun X : Matrix B B ℂ => C * X * Cᴴ) :=
        (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      have h2 : ContinuousAt (fun s : ℝ => C * (ridgeGram C s)⁻¹ * Cᴴ) 0 :=
        hK.continuousAt.comp h1
      exact (Complex.continuous_re.comp (continuous_id.matrix_elem i i)).continuousAt.comp h2
    have htend := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun s hs => hpos s hs)
  · unfold leverage ridgeProjection
    have hG0 : ridgeGram C 0 = gram C := by simp [ridgeGram]
    rw [hG0, Matrix.nonsing_inv_apply_not_isUnit _ hdet]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, Complex.zero_re]
    by_contra hneg
    have hl : 2 * l < 0 := lt_of_not_ge hneg
    have := hpos 1 one_pos
    have h0 := leverage_nonneg C (zero_le_one) i
    linarith

/-- Every start weight is at most `2 l_*` (no running hypothesis). -/
theorem initial_weights_cap' (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t)
    (ht1 : t ≤ 1) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (i : Fin n) :
    trialWeights t (r ω) (q.state 0 ω) (q.ridge 0 ω) i ≤ 2 * leverageScale t := by
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hτ : 0 < leverageScale t ^ (-2 : ℤ) := zpow_pos hl _
  rcases lt_or_ge 0 (q.ridge 0 ω) with h0 | h0
  · set C := trialCross t (r ω) (q.state 0 ω)
    have hl1 : leverageScale t ≤ 1 := Real.rpow_le_one ht.le ht1 (by unfold e0 delta; norm_num)
    rw [q.start_ridge ω] at h0 ⊢
    rcases chooseRidge_cap C hτ h0 with h | h
    · rw [h]
      have hC := trialCross_norm_le_one ht (r ω) hr (q.state 0 ω)
      obtain ⟨h1, h2⟩ := AndersonAC.SolS6.ridgeInitial_proof _ _ C (leverageScale t) hl
        (by linarith) hC
      calc leverage C (leverageScale t ^ (-2 : ℤ)) i
          ≤ maxWeight (leverage C (leverageScale t ^ (-2 : ℤ))) := le_maxWeight _ i
        _ ≤ _ := h1
        _ ≤ _ := h2.le
    · exact h i
  · rw [q.start_ridge ω] at h0 ⊢
    exact chooseRidge_nonpos_cap _ hτ h0 i

/-- The cap failure mode cannot occur at `stop = 0`. -/
theorem not_capMode_stop_zero (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t)
    (ht1 : t ≤ 1) (ω : Ω) (hr : ∀ i, 0 < (r ω i).im) (h0 : q.stop ω = 0) :
    maxWeight (trialWeights t (r ω) (q.state (q.stop ω) ω) (q.ridge (q.stop ω - 1) ω)) ≤
      2 * leverageScale t := by
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  rw [h0]
  exact maxWeight_le (by linarith) fun i => initial_weights_cap' q ht ht1 ω hr i

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.not_capMode_stop_zero

#print axioms AndersonAC.AgentS6.cap_of_prefix
