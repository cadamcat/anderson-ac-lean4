import AndersonAC.AgentS78.Construction.FinalCertificate
import AndersonAC.AgentS78.Construction.TrueSpace
import AndersonAC.S2.PrincipalInvertibility

/-!
# WP10 construction, C5d: the null exceptional set

02-state.tex:220–229: almost surely every principal matrix of the true `H_m − E` is
invertible (S2 `true_principal_invertible`). On the enlarged space this is the null
`exceptionalSet` of `RunLaw`/`BlockRun`; off it, every terminal block is invertible, the
`hT` input of `certificate_of_final_record`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-- Samples at which some principal matrix of the true `H_m − E` is singular. -/
def exceptionalSet (n₀ : ℕ) (u E : ℝ) (M : ℕ → ℕ) : Set (RandomSources (Torus d m) M) :=
  {ω | ¬ ∀ U : Finset (Torus d m), IsUnit ((trueShifted n₀ u E (trueConfig ω)).submatrix
      (fun i : {i // i ∈ U} => i.val) (fun i : {i // i ∈ U} => i.val))}

theorem scaleCoupling_ne_zero (n₀ : ℕ) {u : ℝ} (hu : 0 < u) :
    OAI.Anderson.scaleCoupling n₀ u ≠ 0 := by
  unfold OAI.Anderson.scaleCoupling
  have : 0 < Real.sqrt (3 * u) := Real.sqrt_pos.mpr (by linarith)
  positivity

/-- **The exceptional set is null.** -/
theorem exceptionalSet_null (n₀ : ℕ) {u : ℝ} (hu : 0 < u) (E : ℝ) (M : ℕ → ℕ) :
    sourcesLaw (Torus d m) M (exceptionalSet (d := d) (m := m) n₀ u E M) = 0 := by
  have h := AndersonAC.S2.true_principal_invertible d m (OAI.Anderson.scaleCoupling n₀ u) E
    (scaleCoupling_ne_zero n₀ hu)
  have h2 : ∀ᵐ c ∂(sourcesLaw (Torus d m) M).map trueConfig,
      ∀ U : Finset (Torus d m), IsUnit ((trueShifted n₀ u E c).submatrix
        (fun i : {i // i ∈ U} => i.val) (fun i : {i // i ∈ U} => i.val)) := by
    rw [trueConfig_law d m M]; exact h
  have h' := ae_of_ae_map (trueConfig_measurable d m M).aemeasurable h2
  exact measure_eq_zero_iff_ae_notMem.mpr (by
    filter_upwards [h'] with ω hω hmem
    exact hmem hω)

/-- **Off the exceptional set every terminal block is invertible.** -/
theorem terminal_invertible (n₀ : ℕ) (u E : ℝ) (M : ℕ → ℕ) (ω : RandomSources (Torus d m) M)
    (hω : ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M) (A : Finset (Torus d m)) :
    IsUnit ((trueShifted n₀ u E (trueConfig ω)).submatrix
      (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val)).det := by
  classical
  have hall : ∀ U : Finset (Torus d m), IsUnit ((trueShifted n₀ u E (trueConfig ω)).submatrix
      (fun i : {i // i ∈ U} => i.val) (fun i : {i // i ∈ U} => i.val)) := by
    by_contra h; exact hω h
  have hU := hall (Finset.univ.filter fun i => i ∉ A)
  rw [Matrix.isUnit_iff_isUnit_det] at hU
  let e : {i // i ∉ A} ≃ {i // i ∈ Finset.univ.filter fun i => i ∉ A} :=
    Equiv.subtypeEquivRight (fun i => by simp)
  have hdet : ((trueShifted n₀ u E (trueConfig ω)).submatrix
      (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val)).det =
      ((trueShifted n₀ u E (trueConfig ω)).submatrix
      (fun i : {i // i ∈ Finset.univ.filter fun i => i ∉ A} => i.val)
      (fun i : {i // i ∈ Finset.univ.filter fun i => i ∉ A} => i.val)).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  rw [hdet]; exact hU

end AndersonAC.AgentS78
