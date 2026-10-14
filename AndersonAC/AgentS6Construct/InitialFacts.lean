import AndersonAC.AgentS6Construct.Data
import AndersonAC.AgentS6.CrossNorm
import AndersonAC.S6.Ridge

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω]

theorem initial_previous_cap (core : Finset ι) (t : ℝ) (ht : 0 < t)
    (hl : leverageScale t < 2) (c K : ℝ) (r : Ω → ι → ℂ)
    (M0 : Ω → Matrix ι ι ℝ) (hM : ∀ ω, (M0 ω).IsSymm)
    (hr : ∀ ω, BroadBounds c K (r ω)) (ω : Ω) :
    maxWeight (trialWeights t (r ω)
      (initialState core (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω))
      ((leverageScale t) ^ (-2 : ℤ))) ≤ 4 * leverageScale t := by
  let s := initialState core (M0 ω) (activeInverse (M0 ω) t (r ω)) (hM ω)
  let C := trialCross t (r ω) s
  have hrpos : ∀ i, 0 < ((r ω) i).im := by
    intro i
    exact lt_of_lt_of_le (hr ω).1 ((hr ω).2 i).2.1
  have hC : ‖C‖ ≤ 1 := by
    exact AndersonAC.AgentS6.trialCross_norm_le_one ht (r ω) hrpos s
  have hlpos : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hinitial := AndersonAC.S6.ridge_initial C (leverageScale t) hlpos hl hC
  change maxWeight (leverage C ((leverageScale t) ^ (-2 : ℤ))) ≤
    4 * leverageScale t
  nlinarith [hinitial.1, hinitial.2]

end AndersonAC.AgentS6Construct
