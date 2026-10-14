import AndersonAC.S78MatrixBounds.Moments

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

/-- Summing a graph-distance exponential over any subset of distinct anchors
costs the same uniform moment bound as summing over the whole torus. -/
theorem injective_anchor_exponential_sum (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : 0 < γ) :
    ∃ M t₀ : ℝ, 0 < M ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (hL : 4 ≤ OAI.Anderson.sideLength m)
        (anchor : Fin k → Torus d m), Function.Injective anchor →
        ∀ (x : Torus d m) (t : ℝ), 0 < t → t < t₀ →
        ∀ F : Finset (Fin k),
          (∑ a ∈ F, Real.exp (-γ * t * physicalDistance d m x (anchor a))) ≤
            M * t ^ (-(d : ℝ)) := by
  obtain ⟨M, t₀, hM, ht₀, hmoment⟩ := graph_exponential_moment d hd γ hγ
  refine ⟨M, t₀, hM, ht₀, ?_⟩
  intro m k hL anchor hinj x t ht ht₀ F
  let f : Torus d m → ℝ := fun z => Real.exp (-γ * t * physicalDistance d m x z)
  have hsumAnchor :
      (∑ a : Fin k, f (anchor a)) ≤ ∑ z : Torus d m, f z := by
    classical
    have hinjOn : Set.InjOn anchor (Finset.univ : Finset (Fin k)) := by
      intro a ha b hb hab
      exact hinj hab
    calc
      (∑ a : Fin k, f (anchor a)) =
          ∑ z ∈ (Finset.univ : Finset (Fin k)).image anchor, f z := by
            rw [← Finset.sum_image hinjOn]
      _ ≤ ∑ z : Torus d m, f z := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro z hz hnot
            exact Real.exp_nonneg _
  have hsub : (∑ a ∈ F, f (anchor a)) ≤ ∑ a : Fin k, f (anchor a) := by
    classical
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    intro a ha hnot
    exact Real.exp_nonneg _
  calc
    (∑ a ∈ F, Real.exp (-γ * t * physicalDistance d m x (anchor a))) =
        ∑ a ∈ F, f (anchor a) := by rfl
    _ ≤ ∑ a : Fin k, f (anchor a) := hsub
    _ ≤ ∑ z : Torus d m, f z := hsumAnchor
    _ ≤ M * t ^ (-(d : ℝ)) := by
      dsimp [f]
      exact hmoment m hL x t ht ht₀

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.injective_anchor_exponential_sum
