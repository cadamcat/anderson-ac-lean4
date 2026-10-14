import AndersonAC.S78.Definitions

open MeasureTheory
open AndersonAC.S78
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

theorem success_projects_to_true_law_proof {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (d m : ℕ) (trueConfig : Ω → OAI.Anderson.TorusConfiguration d m)
    (hmap : Measurable trueConfig) (hlaw : μ.map trueConfig = OAI.Anderson.torusLaw d m)
    (S : Set Ω) (event : Set (OAI.Anderson.TorusConfiguration d m))
    (hevent : MeasurableSet event) (hsuccess : S ⊆ trueConfig ⁻¹' event) :
    μ S ≤ OAI.Anderson.torusLaw d m event := by
  calc
    μ S ≤ μ (trueConfig ⁻¹' event) := measure_mono hsuccess
    _ = (μ.map trueConfig) event := (Measure.map_apply hmap hevent).symm
    _ = OAI.Anderson.torusLaw d m event := by rw [hlaw]

theorem rollback_has_zero_error_proof {ι Q : Type} (T : TrialRecord ι Q)
    (hf : T.outcome = .fail) (r : ι → ℂ) (t : ℝ) :
    endpointEnergy T.output r t = endpointEnergy T.before r t ∧
      normalizedInverse T.output t = normalizedInverse T.before t := by
  have hrollback : T.output = T.before := T.rollback hf
  constructor <;> simp [hrollback]

theorem localized_pivot_excludes_old_marks_proof {d m : ℕ} (B bad : Finset (Torus d m))
    (x : Torus d m) (R ℓ : ℝ) (hR : ℓ < R)
    (hnear : ∃ y ∈ B, physicalDistance d m x y ≤ ℓ / 2)
    (hbad : ∀ z ∈ bad, ∀ y ∈ B, R - ℓ / 2 < physicalDistance d m z y) : x ∉ bad := by
  rcases hnear with ⟨y, hy, hxy⟩
  intro hx
  have hsep := hbad x hx y hy
  linarith

end AndersonAC.SolS78
