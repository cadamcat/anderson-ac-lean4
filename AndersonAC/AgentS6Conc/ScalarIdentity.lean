import AndersonAC.AgentS6Conc.Support

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder

namespace AndersonAC.AgentS6Conc

def scalarIdentityLinear (n : Type*) [Fintype n] [DecidableEq n] :
    ℝ →ₗ[ℝ] Matrix n n ℂ where
  toFun a := (a : ℂ) • 1
  map_add' a b := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_smul' a b := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, mul_assoc]

noncomputable def scalarIdentityCLM (n : Type*) [Fintype n] [DecidableEq n] :
    ℝ →L[ℝ] Matrix n n ℂ where
  toLinearMap := scalarIdentityLinear n
  cont := by fun_prop

theorem scalarIdentityCLM_apply {n : Type*} [Fintype n] [DecidableEq n] (a : ℝ) :
    scalarIdentityCLM n a = (a : ℂ) • (1 : Matrix n n ℂ) := rfl

end AndersonAC.AgentS6Conc

end
