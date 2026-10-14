import Mathlib

/-!
Independent restatement of Simon's Problem 1 (Simon 2000, Example 2.1 and Problem 1,
p. 284) in Mathlib vocabulary. The package `challengeBridge` derives it from `AndersonAC.Blueprint.SimonProblem`.

Model (Example 2.1): on ℓ²(ℤ^ν), (h_ω u)(n) = Σ_{|j|=1} u(n+j) + V_ω(n) u(n), with V_ω(n) i.i.d. uniform on [a, b].
Problem 1: for ν ≥ 3 and suitable values of b − a, purely absolutely continuous spectrum in some energy range.
-/

open MeasureTheory ProbabilityTheory

namespace AndersonChallenge

/-- `T` is the Anderson operator with positive nearest-neighbour hopping and potential `V` (Simon, Example 2.1). -/
def IsAndersonOperator {d : ℕ} (V : (Fin d → ℤ) → ℝ) (T : lp (fun _ : Fin d → ℤ => ℂ) 2 →L[ℂ] lp (fun _ : Fin d → ℤ => ℂ) 2) : Prop :=
  ∀ (u : lp (fun _ : Fin d → ℤ => ℂ) 2) (n : Fin d → ℤ),
    T u n = (∑ i : Fin d, (u (n + Pi.single i 1) + u (n - Pi.single i 1))) + (V n : ℂ) * u n

/-- `μ` is the spectral measure of the vector `v` for `T`: a finite Borel measure on ℝ whose moments are
`⟪v, Tⁿ v⟫`. For a bounded self-adjoint `T` such a measure exists and is unique (its moments grow at most
geometrically, so it is determinate). -/
def IsSpectralMeasure {d : ℕ} (T : lp (fun _ : Fin d → ℤ => ℂ) 2 →L[ℂ] lp (fun _ : Fin d → ℤ => ℂ) 2) (v : lp (fun _ : Fin d → ℤ => ℂ) 2)
    (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧ ∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ ∧
    ∫ t, t ^ k ∂μ = (inner ℂ v ((T ^ k) v)).re

/-- Simon's Problem 1, in a strong form that is a consequence of Theorem 1.1 of the OpenAI manuscript: in every dimension
`d ≥ 3` there is a width bound `δ > 0` such that for all `a < b` with `b - a < δ` there is a nonempty open energy
interval `I = (E₁, E₂)` such that almost surely `I ⊆ σ(h_ω)`, every spectral measure of `h_ω` is absolutely
continuous on `I`, and some vector has nonzero spectral weight in `I`. The potentials are any i.i.d. family of
uniform random variables on `[a, b]` on any probability space. The interval may depend on `a` and `b`; the
proof takes Theorem 1.1's fixed interval translated by `(a + b)/2` (`AndersonAC.Blueprint.SimonProblem`). -/
def Statement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a < δ →
    ∃ E₁ E₂ : ℝ, E₁ < E₂ ∧
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
        (V : (Fin d → ℤ) → Ω → ℝ),
        (∀ n, Measurable (V n)) → iIndepFun V volume →
        (∀ n, pdf.IsUniform (V n) (Set.Icc a b) volume volume) →
        ∀ᵐ ω, (∃ T, IsAndersonOperator (fun n => V n ω) T) ∧
          ∀ T, IsAndersonOperator (fun n => V n ω) T →
            (∀ E ∈ Set.Ioo E₁ E₂, (E : ℂ) ∈ spectrum ℂ T) ∧
            (∀ v μ, IsSpectralMeasure T v μ → μ.restrict (Set.Ioo E₁ E₂) ≪ volume) ∧
            (∃ v, (∃ μ, IsSpectralMeasure T v μ) ∧ ∀ μ, IsSpectralMeasure T v μ → μ (Set.Ioo E₁ E₂) ≠ 0)

end AndersonChallenge

