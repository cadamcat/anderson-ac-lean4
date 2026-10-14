import AndersonAC

/-!
# Non-vacuity of the final statement

`AndersonChallenge.Statement` quantifies over every probability space that carries an i.i.d. family of
potentials uniform on `[a, b]`. Two checks show that it is not vacuous:

1. `hypotheses_satisfiable`: for every `d` and `a < b` such a family exists.
2. `conclusion_witnessed`: for every `d ≥ 3`, the theorem then yields actual objects: a potential, an Anderson
   operator for it, a vector, and a spectral measure of that vector with nonzero mass on the energy interval.
-/

open MeasureTheory ProbabilityTheory

namespace AndersonNonVacuity

theorem hypotheses_satisfiable (d : ℕ) {a b : ℝ} (hab : a < b) :
    ∃ (Ω : Type) (inst : MeasureSpace Ω), IsProbabilityMeasure (@volume Ω inst) ∧
      ∃ V : (Fin d → ℤ) → Ω → ℝ, (∀ n, Measurable (V n)) ∧ iIndepFun V (@volume Ω inst) ∧
        ∀ n, pdf.IsUniform (V n) (Set.Icc a b) (@volume Ω inst) volume := by
  have h0 : volume (Set.Icc a b) ≠ 0 := by
    simp [Real.volume_Icc, not_le.mpr hab]
  have h1 : volume (Set.Icc a b) ≠ ⊤ := by simp [Real.volume_Icc]
  have : IsProbabilityMeasure (volume[|Set.Icc a b]) := cond_isProbabilityMeasure_of_finite h0 h1
  obtain ⟨Ω, mΩ, P, X, hX, hlaw, hind, hP⟩ :=
    exists_iid (Fin d → ℤ) (volume[|Set.Icc a b] : Measure ℝ)
  exact ⟨Ω, { toMeasurableSpace := mΩ, volume := P }, hP, X, hX, hind, hlaw⟩

theorem conclusion_witnessed : ∀ d : ℕ, 3 ≤ d → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a < δ →
    ∃ E₁ E₂ : ℝ, E₁ < E₂ ∧
      ∃ (V : (Fin d → ℤ) → ℝ)
        (T : lp (fun _ : Fin d → ℤ => ℂ) 2 →L[ℂ] lp (fun _ : Fin d → ℤ => ℂ) 2)
        (v : lp (fun _ : Fin d → ℤ => ℂ) 2) (μ : Measure ℝ),
        AndersonChallenge.IsAndersonOperator V T ∧ AndersonChallenge.IsSpectralMeasure T v μ ∧
          μ (Set.Ioo E₁ E₂) ≠ 0 := by
  intro d hd
  obtain ⟨δ, hδ, h⟩ := AndersonAC.Blueprint.anderson_challenge d hd
  refine ⟨δ, hδ, fun a b hab hw => ?_⟩
  obtain ⟨E₁, E₂, hE, hall⟩ := h a b hab hw
  obtain ⟨Ω, inst, hP, V, hV, hind, huni⟩ := hypotheses_satisfiable d hab
  let := inst
  have := hP
  obtain ⟨ω, ⟨T, hT⟩, hconc⟩ := (hall Ω V hV hind huni).exists
  obtain ⟨-, -, v, ⟨μ, hμ⟩, hpos⟩ := hconc T hT
  exact ⟨E₁, E₂, hE, fun n => V n ω, T, v, μ, hT, hμ, hpos μ hμ⟩

end AndersonNonVacuity

#print axioms AndersonNonVacuity.hypotheses_satisfiable
#print axioms AndersonNonVacuity.conclusion_witnessed
