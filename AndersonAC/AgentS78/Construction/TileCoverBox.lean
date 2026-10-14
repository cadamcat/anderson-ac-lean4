import AndersonAC.AgentS78.Construction.TileCoverGeneric

/-!
# WP10 construction: the §5 tile covers — boxes in the torus

agent-s78cover (2026-10-14). The Poincaré inequality on an injective image of a grid box whose
grid edges are torus edges (05:285–291), from `GridPoincareStatement`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The grid step `w ↦ w + e_i`, left unchanged at the upper face. -/
def gridStep {K : ℕ} (w : Fin d → Fin K) (i : Fin d) : Fin d → Fin K :=
  Function.update w i (if h : (w i).val + 1 < K then ⟨(w i).val + 1, h⟩ else w i)

theorem poincare_of_box (hGP : GridPoincareStatement) {K : ℕ}
    (β : (Fin d → Fin K) → Torus d m) (hβ : Function.Injective β)
    (hadj : ∀ w (i : Fin d), (w i).val + 1 < K → (nnGraph d m).Adj (β w) (β (gridStep w i)))
    (v : Torus d m → ℝ) :
    ∑ x ∈ Finset.univ.image β, (v x - setAvg (Finset.univ.image β) v) ^ 2 ≤
      (2 * d * (K : ℝ) ^ 2) * setEnergy (Finset.univ.image β) v := by
  classical
  set A := Finset.univ.image β with hA
  let f : (Fin d → Fin K) → ℝ := fun w => v (β w)
  have hsum : ∀ F : Torus d m → ℝ, ∑ x ∈ A, F x = ∑ w, F (β w) := fun F =>
    Finset.sum_image (fun _ _ _ _ h => hβ h)
  have hcard : (A.card : ℝ) = (K : ℝ) ^ d := by
    rw [hA, Finset.card_image_of_injective _ hβ]
    simp [Finset.card_univ, Fintype.card_fin]
  have havg : setAvg A v = (∑ w', f w') / (K : ℝ) ^ d := by
    unfold setAvg; rw [hsum, hcard]
  have hgrid : gridEnergy f ≤ 2 * setEnergy A v := by
    have hw : ∀ w, (∑ i : Fin d, if h : (w i).val + 1 < K then
        (f (Function.update w i ⟨(w i).val + 1, h⟩) - f w) ^ 2 else 0) ≤
        ∑ y ∈ A, if (nnGraph d m).Adj (β w) y then (v (β w) - v y) ^ 2 else 0 := by
      intro w
      let S := Finset.univ.filter fun i : Fin d => (w i).val + 1 < K
      have hstep : ∀ i ∈ S, (if h : (w i).val + 1 < K then
          (f (Function.update w i ⟨(w i).val + 1, h⟩) - f w) ^ 2 else 0) =
          (v (β w) - v (β (gridStep w i))) ^ 2 := by
        intro i hi
        have hi' : (w i).val + 1 < K := (Finset.mem_filter.mp hi).2
        rw [dif_pos hi']
        simp only [f, gridStep, dif_pos hi']
        ring
      have hinj : Set.InjOn (fun i => β (gridStep w i)) S := by
        intro i hi j hj hij
        have hi' : (w i).val + 1 < K := (Finset.mem_filter.mp hi).2
        have h2 := congrFun (hβ hij) i
        by_contra hne
        simp only [gridStep, Function.update_self, dif_pos hi',
          Function.update_of_ne hne] at h2
        have := congrArg Fin.val h2
        simp at this
      calc (∑ i : Fin d, if h : (w i).val + 1 < K then
            (f (Function.update w i ⟨(w i).val + 1, h⟩) - f w) ^ 2 else 0)
          = ∑ i ∈ S, (v (β w) - v (β (gridStep w i))) ^ 2 := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun i : Fin d => (w i).val + 1 < K)]
            rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i : Fin d => ¬ (w i).val + 1 < K)
              (fun i hi => by rw [dif_neg (Finset.mem_filter.mp hi).2]), add_zero]
            exact Finset.sum_congr rfl hstep
        _ = ∑ y ∈ S.image (fun i => β (gridStep w i)), (v (β w) - v y) ^ 2 := by
            rw [Finset.sum_image hinj]
        _ = ∑ y ∈ S.image (fun i => β (gridStep w i)),
            (if (nnGraph d m).Adj (β w) y then (v (β w) - v y) ^ 2 else 0) := by
            refine Finset.sum_congr rfl fun y hy => ?_
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
            rw [if_pos (hadj w i (Finset.mem_filter.mp hi).2)]
        _ ≤ ∑ y ∈ A, if (nnGraph d m).Adj (β w) y then (v (β w) - v y) ^ 2 else 0 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => by
              split_ifs <;> positivity)
            intro y hy
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
            exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    calc gridEnergy f ≤ ∑ w, ∑ y ∈ A, if (nnGraph d m).Adj (β w) y then (v (β w) - v y) ^ 2
          else 0 := Finset.sum_le_sum fun w _ => hw w
      _ = ∑ x ∈ A, ∑ y ∈ A, if (nnGraph d m).Adj x y then (v x - v y) ^ 2 else 0 :=
          (hsum (fun x => ∑ y ∈ A, if (nnGraph d m).Adj x y then (v x - v y) ^ 2 else 0)).symm
      _ = 2 * setEnergy A v := by unfold setEnergy; ring
  have hP := hGP d K f
  rw [hsum, havg]
  have hE0 := setEnergy_nonneg A v
  calc ∑ w, (v (β w) - (∑ w', f w') / (K : ℝ) ^ d) ^ 2 ≤ (d : ℝ) * (K : ℝ) ^ 2 * gridEnergy f := hP
    _ ≤ (d : ℝ) * (K : ℝ) ^ 2 * (2 * setEnergy A v) := by gcongr
    _ = (2 * d * (K : ℝ) ^ 2) * setEnergy A v := by ring

end AndersonAC.AgentS78
