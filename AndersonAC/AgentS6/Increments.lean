import AndersonAC.AgentS6.RunningPrestate
import AndersonAC.AgentS6.TrialStep

/-! Bookkeeping increments of the stopped trial (06-clearing.tex:788–800, 905–911,
equation `clearing-entry-increment`): on surviving pairs a heat changes `ĝ` by
`c_x √t ĝ_{ix} ĝ_{xj}` (i.e. `Δĥ = c_x h_{ix} h_{xj}`), other entries are frozen, and the stop
matrix is the start matrix plus the sum of the running increments. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

open Classical in
/-- The heat increment of `ĝ` at step `k` (zero off the surviving pairs). -/
def hatIncrement (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω)
    (i j : Fin n) : ℂ :=
  if i ∈ (q.state (k + 1) ω).active ∧ j ∈ (q.state (k + 1) ω).active then
    heatCoefficient t (r ω (q.pivot k ω)) ((q.state k ω).hatG (q.pivot k ω) (q.pivot k ω))
        (q.residual k ω) * (Real.sqrt t : ℂ) *
      (q.state k ω).hatG i (q.pivot k ω) * (q.state k ω).hatG (q.pivot k ω) j
  else 0

theorem hatG_step (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ω : Ω)
    (hr : ∀ i, 0 < (r ω i).im) (k : ℕ) (hk : k < q.stop ω) (i j : Fin n) :
    (q.state (k + 1) ω).hatG i j = (q.state k ω).hatG i j + hatIncrement q k ω i j := by
  obtain ⟨hx, hden, hform⟩ := trial_heat_step ht (r ω) hr (q.heat k ω hk)
  have hT := q.heat k ω hk
  obtain ⟨-, -, hact, -, -, hG⟩ := hT
  rw [hG i j]
  unfold hatIncrement
  by_cases hij : i ∈ (q.state (k + 1) ω).active ∧ j ∈ (q.state (k + 1) ω).active
  · obtain ⟨hi, hj⟩ := hij
    rw [dif_pos hi, dif_pos hj, if_pos ⟨hi, hj⟩]
    have hsub : ∀ m, m ∈ (q.state (k + 1) ω).active → m ∈ (q.state k ω).active := by
      intro m hm; rw [hact] at hm; exact Finset.mem_of_mem_erase hm
    rw [hform ⟨i, hi⟩ ⟨j, hj⟩ (hsub i hi) (hsub j hj)]
    have hinv := hatG_eq_trialInverse q k ω hk.le
    rw [← hinv ⟨i, hsub i hi⟩ ⟨j, hsub j hj⟩, ← hinv ⟨i, hsub i hi⟩ ⟨_, hx⟩,
      ← hinv ⟨_, hx⟩ ⟨j, hsub j hj⟩, ← hinv ⟨_, hx⟩ ⟨_, hx⟩] at *
    have hs : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
    dsimp only at hden ⊢
    unfold heatCoefficient
    field_simp
    ring
  · rw [if_neg hij]
    by_cases hi : i ∈ (q.state (k + 1) ω).active
    · have hj : j ∉ (q.state (k + 1) ω).active := fun hj => hij ⟨hi, hj⟩
      rw [dif_pos hi, dif_neg hj]
    · rw [dif_neg hi]

/-- The stop matrix is the start matrix plus the running increments. -/
theorem hatG_telescope (q : StoppedTrial (Ω := Ω) core t r g0 order) (ht : 0 < t) (ω : Ω)
    (hr : ∀ i, 0 < (r ω i).im) (m : ℕ) (hm : m ≤ q.stop ω) (i j : Fin n) :
    (q.state m ω).hatG i j = g0 ω i j + ∑ k ∈ Finset.range m, hatIncrement q k ω i j := by
  induction m with
  | zero => simp [q.start_entries ω]
  | succ m ih =>
    rw [hatG_step q ht ω hr m (by omega), ih (by omega), Finset.sum_range_succ]
    ring

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.hatG_step
#print axioms AndersonAC.AgentS6.hatG_telescope
