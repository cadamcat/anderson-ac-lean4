import AndersonAC.AgentS6Construct.MeasurableHelpers
import AndersonAC.AgentS6Construct.Data
import AndersonAC.AgentS6Construct.RunHeat
import AndersonAC.AgentS6Construct.StopFacts

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

def trialHatGMatches {ι : Type*} [Fintype ι] [DecidableEq ι] {core : Finset ι}
    (t : ℝ) (r : ι → ℂ) (s : TrialState core) : Prop :=
  ∀ (i j : ι) (hi : i ∈ s.active) (hj : j ∈ s.active),
    trialInverse t r s ⟨i, hi⟩ ⟨j, hj⟩ = s.hatG i j

theorem initialState_hatGMatches {ι : Type*} [Fintype ι] [DecidableEq ι]
    (core : Finset ι) (t : ℝ) (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    (r : ι → ℂ) :
    trialHatGMatches t r (initialState core M (activeInverse M t r) hM) := by
  intro i j hi hj
  calc
    trialInverse t r (initialState core M (activeInverse M t r) hM) ⟨i, hi⟩ ⟨j, hj⟩ =
        activeInverse M t r i j := initialState_inverse core M
          (activeInverse M t r) hM t r ⟨i, hi⟩ ⟨j, hj⟩
    _ = (initialState core M (activeInverse M t r) hM).hatG i j := rfl

theorem heatTransition_hatGMatches {ι : Type*} [Fintype ι] [DecidableEq ι]
    {core : Finset ι} (t : ℝ) (r : ι → ℂ) (s s' : TrialState core)
    (x : ι) (ξ : ℝ) (h : HeatTransition t r s s' x ξ) :
    trialHatGMatches t r s' := by
  classical
  rcases h with ⟨_, _, _, _, _, hG⟩
  intro i j hi hj
  have hstep := hG i j
  have hstep' : s'.hatG i j = s.hatG i j +
      (trialInverse t r s' ⟨i, hi⟩ ⟨j, hj⟩ - s.hatG i j) := by
    simpa [hi, hj] using hstep
  calc
    trialInverse t r s' ⟨i, hi⟩ ⟨j, hj⟩ =
        s.hatG i j + (trialInverse t r s' ⟨i, hi⟩ ⟨j, hj⟩ - s.hatG i j) := by abel
    _ = s'.hatG i j := hstep'.symm

theorem runAt_hatGMatches {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace Ω] (core : Finset ι) (t : ℝ) (ht : 0 < t)
    (r : Ω → ι → ℂ) (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (ξ : ι → Ω → ℝ) (order : ι ≃ Fin (Fintype.card ι)) (ω : Ω)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M0 ω + Matrix.diagonal (fun i => ξ i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det)) :
    ∀ k, trialHatGMatches t (r ω) (stateAt core t r M0 hM ξ order k ω) := by
  let q0 := initialCursor core t (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)
  have h0 : trialHatGMatches t (r ω) q0.state := by
    simpa [q0, initialCursor] using
      initialState_hatGMatches core t (M0 ω) (hM ω) (r ω)
  intro k
  induction k with
  | zero => simpa [stateAt, runAt, runCursor, q0, initialCursor] using h0
  | succ k ih =>
      by_cases hrun : k < stopAt core t r M0 hM ξ order ω
      · have hheat := runAt_heatTransition core t ht r M0 hM ξ order ω k hterminal hrun
        exact heatTransition_hatGMatches t (r ω)
          (stateAt core t r M0 hM ξ order k ω)
          (stateAt core t r M0 hM ξ order (k + 1) ω)
          (pivotAt core t r M0 hM ξ order k ω)
          (residualAt core t r M0 hM ξ order k ω) hheat
      · have hstop : stopAt core t r M0 hM ξ order ω ≤ k := le_of_not_gt hrun
        have hEq0 := stateAt_eq_stop_of_le core t r M0 hM ξ order ω k hstop
        have hEq1 := stateAt_eq_stop_of_le core t r M0 hM ξ order ω (k + 1)
          (by omega)
        have hEq : stateAt core t r M0 hM ξ order (k + 1) ω =
            stateAt core t r M0 hM ξ order k ω := hEq1.trans hEq0.symm
        rw [hEq]
        exact ih

end AndersonAC.AgentS6Construct
