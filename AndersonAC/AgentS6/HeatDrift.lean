import AndersonAC.S6.Statements

/-! Paper 06-clearing.tex, lines 650–684, equation `clearing-phi-drift`:
the potential `Φ = 𝒫 - 10 l_* 𝒜` drifts down by `m_*²/2` at an admissible heat,
given the conclusion of Lemma 6.4 in the conditional form `LeverageDriftInput`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6

variable {ι : Type*} [Fintype ι]

theorem maxWeight_nonneg (m : ι → ℝ) : 0 ≤ AndersonAC.S6.maxWeight m := by
  unfold AndersonAC.S6.maxWeight
  exact NNReal.coe_nonneg _

/-- Scalar step of `clearing-phi-drift`: with `2 l ≤ m`, `0 ≤ ε ≤ 1/20`. -/
theorem phi_scalar (l ε m a p : ℝ) (hl : 0 < l) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 20)
    (hm : 2 * l ≤ m) (ha : |a| ≤ ε * m) (hp : p ≤ -(1 - ε) * m ^ 2) :
    p - 10 * l * a ≤ -(1 / 2) * m ^ 2 := by
  have hm0 : 0 ≤ m := by linarith
  have h1 : -(10 * l * a) ≤ 10 * l * (ε * m) := by
    have := neg_abs_le a
    have : -a ≤ ε * m := by linarith
    nlinarith
  have h2 : 10 * l * (ε * m) ≤ 5 * ε * m ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm (mul_nonneg hε0 hm0)
    nlinarith
  have h3 : 5 * ε * m ^ 2 + ε * m ^ 2 ≤ (3 / 10) * m ^ 2 := by nlinarith [sq_nonneg m]
  nlinarith [sq_nonneg m]

theorem potential_sub (l : ℝ) (m n : ι → ℝ) :
    AndersonAC.S6.potential l n - AndersonAC.S6.potential l m =
      (AndersonAC.S6.squareWeight n - AndersonAC.S6.squareWeight m) -
        10 * l * (AndersonAC.S6.totalWeight n - AndersonAC.S6.totalWeight m) := by
  unfold AndersonAC.S6.potential; ring

end AndersonAC.AgentS6

namespace AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω]

open AndersonAC.AgentS6 in
/-- Equation `clearing-phi-drift` (06-clearing.tex:672–676) from the Lemma 6.4 input. -/
theorem heat_potential_drift (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (ε l : ℝ) (running : ℕ → Set Ω)
    (pre post : ℕ → Ω → ι → ℝ) (hl : 0 < l) (hε : 0 ≤ ε ∧ ε ≤ 1 / 20)
    (hinput : LeverageDriftInput μ F ε running pre post)
    (hmax : ∀ k ω, ω ∈ running k → 2 * l ≤ maxWeight (pre k ω)) :
    Planned.heat_potential_drift μ F ε l running pre post hl hε hinput hmax := by
  intro k
  set dP : Ω → ℝ := fun ω => squareWeight (post k ω) - squareWeight (pre k ω)
  set dA : Ω → ℝ := fun ω => totalWeight (post k ω) - totalWeight (pre k ω)
  have hP : Integrable dP μ :=
    (hinput.integrable_postP k).sub (hinput.integrable_preP k)
  have hA : Integrable dA μ :=
    (hinput.integrable_postA k).sub (hinput.integrable_preA k)
  have hfun : (fun ω => potential l (post k ω) - potential l (pre k ω)) =
      dP - (10 * l) • dA := by
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dP, dA]
    exact potential_sub l (pre k ω) (post k ω)
  have hce : μ[dP - (10 * l) • dA | F k] =ᵐ[μ] μ[dP | F k] - (10 * l) • μ[dA | F k] := by
    filter_upwards [condExp_sub hP (hA.smul (10 * l)) (F k), condExp_smul (10 * l) dA (F k)]
      with ω h1 h2
    rw [h1, Pi.sub_apply, Pi.sub_apply, h2]
  filter_upwards [hce, hinput.total_drift k, hinput.square_drift k] with ω h hA' hP' hrun
  rw [hfun, h]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact phi_scalar l ε (maxWeight (pre k ω)) _ _ hl hε.1 hε.2 (hmax k ω hrun)
    (hA' hrun) (hP' hrun)

end AndersonAC.S6

#print axioms AndersonAC.S6.heat_potential_drift
