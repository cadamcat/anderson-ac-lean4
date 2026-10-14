import AndersonAC.AgentS6Construct.CrossFormula
import AndersonAC.AgentS6.TrialStep

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shermanMorrisonEntry (t : ℝ) (r : ι → ℂ) (ξ : ℝ)
    (H : Matrix ι ι ℂ) (x i j : ι) : ℂ :=
  H i j - ((ξ : ℂ) + (t : ℂ) * r x) * H i x * H x j /
    (1 + ((ξ : ℂ) + (t : ℂ) * r x) * H x x)

set_option maxHeartbeats 1000000 in
theorem heatTransition_hatG_entry_formula {core : Finset ι} (t : ℝ)
    (ht : 0 < t) (r : ι → ℂ) (hr : ∀ i, 0 < (r i).im) (s s' : TrialState core)
    (x : ι) (ξ : ℝ) (h : HeatTransition t r s s' x ξ)
    (hmatch : ∀ (i j : {i // i ∈ s.active}),
      trialInverse t r s i j = s.hatG i j) (i j : ι) :
    s'.hatG i j = if hi : i ∈ s'.active then if hj : j ∈ s'.active then
      shermanMorrisonEntry t r ξ s.hatG x i j else s.hatG i j else s.hatG i j := by
  classical
  have hHeat := h
  rcases h with ⟨hx, hxc, hactive, hden, hM, hG⟩
  by_cases hi : i ∈ s'.active
  · by_cases hj : j ∈ s'.active
    · have hiOldErase : i ∈ s.active.erase x := by rw [← hactive]; exact hi
      have hjOldErase : j ∈ s.active.erase x := by rw [← hactive]; exact hj
      have hiOld : i ∈ s.active := (Finset.mem_erase.mp hiOldErase).2
      have hjOld : j ∈ s.active := (Finset.mem_erase.mp hjOldErase).2
      let iA : {i // i ∈ s.active} := ⟨i, hiOld⟩
      let jA : {i // i ∈ s.active} := ⟨j, hjOld⟩
      let xA : {i // i ∈ s.active} := ⟨x, hx⟩
      obtain ⟨hx', hden', hformula⟩ :=
        AndersonAC.AgentS6.trial_heat_step ht r hr hHeat
      have hnew : s'.hatG i j = trialInverse t r s'
          ⟨i, hi⟩ ⟨j, hj⟩ := by
        have h := hG i j
        simpa [hi, hj] using h
      have hform := hformula ⟨i, hi⟩ ⟨j, hj⟩ hiOld hjOld
      have holdIJ : trialInverse t r s iA jA = s.hatG i j := by
        simpa [iA, jA] using hmatch iA jA
      have holdI : trialInverse t r s iA xA = s.hatG i x := by
        simpa [iA, xA] using hmatch iA xA
      have holdJ : trialInverse t r s xA jA = s.hatG x j := by
        simpa [xA, jA] using hmatch xA jA
      have holdX : trialInverse t r s xA xA = s.hatG x x := by
        simpa [xA] using hmatch xA xA
      have hformula' : trialInverse t r s' ⟨i, hi⟩ ⟨j, hj⟩ =
          shermanMorrisonEntry t r ξ s.hatG x i j := by
        unfold shermanMorrisonEntry
        simpa [iA, jA, xA, holdIJ, holdI, holdJ, holdX] using hform
      simp [hi, hj, hnew, hformula']
    · have h := hG i j
      simpa [hi, hj] using h
  · have h := hG i j
    simpa [hi] using h

end AndersonAC.AgentS6Construct
