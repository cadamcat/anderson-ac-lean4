import AndersonAC.S6.RidgeStatements
import AndersonAC.S6RidgeLim.RidgeGenericLimits
import AndersonAC.S6RidgeAlg.Proof
import AndersonAC.S6RidgeInit.RidgeInitial

/-! Positive ridge limit, derivative, and strict monotonicity of every nonzero row. -/
noncomputable section
open scoped Matrix.Norms.L2Operator

namespace AndersonAC.S6
variable {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

theorem ridge_limit (C : Matrix R B ℂ) : Planned.ridge_limit C :=
  (AndersonAC.SolS6.ridgeGenericLimits_proof B R C).1

theorem ridge_derivative (C : Matrix R B ℂ) (i : R) (τ : ℝ) (hτ : 0 < τ) :
    Planned.ridge_derivative C i τ hτ :=
  (AndersonAC.SolS6.ridgeGenericLimits_proof B R C).2.1 i τ hτ

theorem ridge_continuous_monotone (C : Matrix R B ℂ) (i : R) :
    Planned.ridge_continuous_monotone C i :=
  (AndersonAC.SolS6.ridgeGenericLimits_proof B R C).2.2 i

theorem ridge_calculus (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) :
    Planned.ridge_calculus C τ hτ :=
  AndersonAC.SolS6.ridgeAlgebra_proof B R C τ hτ

theorem ridge_initial (C : Matrix R B ℂ) (l : ℝ) (hl : 0 < l) (hsmall : l < 2)
    (hC : ‖C‖ ≤ 1) : Planned.ridge_initial C l hl hsmall hC :=
  AndersonAC.SolS6.ridgeInitial_proof B R C l hl hsmall hC

end AndersonAC.S6
#print axioms AndersonAC.S6.ridge_limit
#print axioms AndersonAC.S6.ridge_derivative
#print axioms AndersonAC.S6.ridge_continuous_monotone
#print axioms AndersonAC.S6.ridge_calculus
#print axioms AndersonAC.S6.ridge_initial
