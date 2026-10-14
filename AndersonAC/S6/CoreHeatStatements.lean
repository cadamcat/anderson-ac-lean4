import AndersonAC.S6.Statements

/-! Independent algebra and stopping propositions for Section 6. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

/-- Paper 06-clearing.tex, lines 120–134: the exact core Woodbury factorization. -/
def CoreResolventStatement : Prop :=
  ∀ (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (g : Matrix (B ⊕ R) (B ⊕ R) ℂ) (V : Matrix B B ℂ),
    IsUnit g.det → IsUnit V.det → IsUnit (g⁻¹ + Matrix.fromBlocks V 0 0 0).det →
    IsUnit (1 + V * AndersonAC.S6.coreBlock g).det ∧
    AndersonAC.S6.survivorBlock ((g⁻¹ + Matrix.fromBlocks V 0 0 0)⁻¹) -
      AndersonAC.S6.survivorBlock g =
        -(AndersonAC.S6.crossBlock g * (1 + V * AndersonAC.S6.coreBlock g)⁻¹ * V *
          g.submatrix Sum.inl Sum.inr)

/-- Paper Lemma 6.5, lines 686–747: mean count and conditional restart tail. -/
def HeatCountStatement : Prop :=
  ∀ (Ω : Type*) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (l r : ℝ) (N : ℕ) (stop σ : Ω → ℕ) (Φ : ℕ → Ω → ℝ)
    (hl : 0 < l) (hr : 0 < r)
    (hinput : AndersonAC.S6.StoppedPotentialInput μ F l r N stop Φ)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℕ))),
    AndersonAC.S6.Planned.heat_count μ F l r N stop σ Φ hl hr hinput hσ

end AndersonAC.SolS6
