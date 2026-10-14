import AndersonAC.S78.AssemblyForms
import AndersonAC.S78.AssemblySummation

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- The analytic comparison is a genuine finite-prefix induction: its step
may use earlier errors, and improves the current error by a fixed factor. -/
theorem assembly_error_induction {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ a : Fin (k + 1), 0 < a.val →
      (∀ q : Fin (k + 1), q.val < a.val → ∀ f : Torus d m → ℝ,
        |assemblyError I q f| ≤ ε * endpointEnergy (I.state 0) r t f) →
      ∀ f : Torus d m → ℝ,
        |assemblyError I a f| ≤ (ε / 2) * endpointEnergy (I.state 0) r t f) :
    ∀ (a : Fin (k + 1)) (f : Torus d m → ℝ),
      |assemblyError I a f| ≤ ε * endpointEnergy (I.state 0) r t f := by
  have haux : ∀ n : ℕ, ∀ a : Fin (k + 1), a.val = n → ∀ f : Torus d m → ℝ,
      |assemblyError I a f| ≤ ε * endpointEnergy (I.state 0) r t f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha f
      by_cases hn : n = 0
      · have ha0 : a = 0 := Fin.ext (ha.trans hn)
        subst a
        rw [assembly_error_zero, abs_zero]
        exact mul_nonneg hε (assembly_energy_nonneg I 0 f)
      · have hprev : ∀ q : Fin (k + 1), q.val < a.val → ∀ F : Torus d m → ℝ,
          |assemblyError I q F| ≤ ε * endpointEnergy (I.state 0) r t F := by
          intro q hq F
          exact ih q.val (by omega) q rfl F
        exact (hstep a (by omega) hprev f).trans
          (mul_le_mul_of_nonneg_right (by linarith) (assembly_energy_nonneg I 0 f))
  intro a f
  exact haux a.val a rfl f

/-- Any common-split bound transfers to the initial Ward energy through the
initial lower comparison. No minimizing split is selected. -/
theorem assembly_error_of_common_split {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin (k + 1)) (B : ℝ) (hB : 0 ≤ B)
    (f : Torus d m → ℝ)
    (hbound : ∀ α v : Torus d m → ℝ, (∀ i ∈ (I.state 0).active, f i = α i + v i) →
      |assemblyError I a f| ≤ B *
        ((∑ i ∈ (I.state 0).active, (α i) ^ 2) + b⁻¹ * gradientEnergy (nnGraph d m) v)) :
    |assemblyError I a f| ≤ (B / I.c) * endpointEnergy (I.state 0) r t f := by
  have hc := I.positive.2.2.2.2.1
  have hsp := spatial_bound_of_all_splits (nnGraph d m) (I.state 0).active b B
    (assemblyError I a f) hB f hbound
  calc
    _ ≤ B * spatialEnergy (nnGraph d m) (I.state 0).active b f := hsp
    _ = (B / I.c) * (I.c * spatialEnergy (nnGraph d m) (I.state 0).active b f) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (I.initialComparison f).1 (div_nonneg hB hc.le)

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_error_induction
#print axioms AndersonAC.SolS78.assembly_error_of_common_split
