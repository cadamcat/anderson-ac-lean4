import AndersonAC.AgentS6Construct.Core
import AndersonAC.AgentS6Construct.Procedure
import AndersonAC.AgentS6.LeverageFacts
import AndersonAC.AgentS6.RidgeStep
import AndersonAC.AgentS6.CrossNorm
import AndersonAC.S6.Ridge
import AndersonAC.S6.RidgeSelection

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem chooseRidge_bounds {B : Type*} [Fintype B] [DecidableEq B]
    (C : Matrix ι B ℂ) (l τ : ℝ) (hl : 0 < l) (hτ : 0 < τ)
    (hcap : maxWeight (leverage C τ) ≤ 4 * l)
    (hlarge : 2 * l < maxWeight (projectionWeight C)) :
    0 < chooseRidge C l τ ∧
      2 * l ≤ maxWeight (leverage C (chooseRidge C l τ)) ∧
      maxWeight (leverage C (chooseRidge C l τ)) ≤ 4 * l := by
  unfold chooseRidge
  by_cases hlow : maxWeight (leverage C τ) < 2 * l
  · rw [if_pos hlow]
    obtain ⟨hρ, hmax, _⟩ := AndersonAC.S6.ridge_threshold C l hl hlarge
    refine ⟨hρ, hmax.symm.le, ?_⟩
    nlinarith
  · rw [if_neg hlow]
    exact ⟨hτ, le_of_not_gt hlow, hcap⟩

theorem selectedRidge_pos_of_not_ready {core : Finset ι} (t : ℝ) (ht : 0 < t)
    (r : ι → ℂ) (s : TrialState core) (τ : ℝ) (hτ : 0 < τ)
    (hready : ¬ projectionReady t r s) : 0 < selectedRidge t r s τ := by
  classical
  let C := trialCross t r s
  have hproj : ∃ i, 2 * leverageScale t < projectionWeight C i := by
    by_contra h
    push_neg at h
    apply hready
    intro i
    exact h i
  obtain ⟨i, hi⟩ := hproj
  have hlarge : 2 * leverageScale t < maxWeight (projectionWeight C) :=
    lt_of_lt_of_le hi (AndersonAC.AgentS6.le_maxWeight _ _)
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  unfold selectedRidge chooseRidge
  by_cases hlow : maxWeight (leverage C τ) <
      2 * leverageScale t
  · rw [if_pos hlow]
    exact (AndersonAC.S6.ridge_threshold C (leverageScale t) hl hlarge).1
  · rw [if_neg hlow]
    exact hτ

set_option maxHeartbeats 1000000 in
theorem selectedPivot_active_exterior {core : Finset ι} (t l : ℝ) (r : ι → ℂ)
    (s : TrialState core) (τ : ℝ) (order : ι ≃ Fin (Fintype.card ι))
    (hl : 0 < l) (hlscale : l = leverageScale t) (hτ : 0 < τ)
    (hprevCap : maxWeight (trialWeights t r s τ) ≤ 4 * l)
    (hready : ¬ projectionReady t r s) :
    let ρ := selectedRidge t r s τ
    let p := leastMaximizerTotal order (trialWeights t r s ρ)
    p ∈ s.active ∧ p ∉ core ∧ 0 < ρ ∧
      2 * l ≤ maxWeight (trialWeights t r s ρ) ∧
      maxWeight (trialWeights t r s ρ) ≤ 4 * l := by
  classical
  let C := trialCross t r s
  have hready' : ¬ ∀ i, projectionWeight C i ≤ 2 * leverageScale t := by
    simpa [projectionReady] using hready
  have hready'' : ¬ ∀ i, projectionWeight C i ≤ 2 * l := by
    intro hall
    apply hready'
    intro i
    simpa [hlscale] using hall i
  have hproj : ∃ i, 2 * l < projectionWeight C i := by
    by_contra h
    push_neg at h
    apply hready''
    intro i
    exact h i
  obtain ⟨i₀, hi₀⟩ := hproj
  have hlarge : 2 * l < maxWeight (projectionWeight C) :=
    lt_of_lt_of_le hi₀ (AndersonAC.AgentS6.le_maxWeight _ _)
  have hbounds := chooseRidge_bounds C l τ hl hτ hprevCap hlarge
  let ρ := selectedRidge t r s τ
  have hρeq : ρ = chooseRidge C l τ := by
    simp [ρ, selectedRidge, C, hlscale]
  have hboundsρ := hbounds
  rw [← hρeq] at hboundsρ
  let m := trialWeights t r s ρ
  let p := leastMaximizerTotal order m
  have hnonneg : ∀ i, 0 ≤ m i := by
    intro i
    change 0 ≤ leverage C ρ i
    exact AndersonAC.AgentS6.leverage_nonneg C hboundsρ.1.le i
  have hmax := leastMaximizerTotal_spec order m hnonneg
  have hpmax : m p = maxWeight m := hmax.1
  have hposMax : 0 < maxWeight m := by
    have hlow : 2 * l ≤ maxWeight m := hboundsρ.2.1
    nlinarith
  have hactive : p ∈ s.active := by
    by_contra hnot
    have hz := trialWeights_eq_zero_of_inactive t r s ρ hnot
    have hz' : m p = 0 := by simpa [m] using hz
    rw [hpmax] at hz'
    linarith
  have hcore : p ∉ core := by
    by_contra hmem
    have hz := trialWeights_eq_zero_of_core t r s ρ hmem
    have hz' : m p = 0 := by simpa [m] using hz
    rw [hpmax] at hz'
    linarith
  refine ⟨hactive, hcore, hboundsρ.1, hboundsρ.2.1, hboundsρ.2.2⟩

end AndersonAC.AgentS6Construct
