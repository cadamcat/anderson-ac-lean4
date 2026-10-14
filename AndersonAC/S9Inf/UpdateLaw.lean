import OAI.MathematicalPhysics.Anderson.Certificates
import Mathlib.Probability.ProductMeasure

/-! Resampling a single coordinate preserves the Anderson iid law. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9Inf

theorem measurable_updateSite {d : ℕ} (x : Site d) :
    Measurable (fun p : Configuration d × SingleSite => Function.update p.1 x p.2) := by
  classical
  apply measurable_pi_lambda
  intro y
  by_cases hy : y = x
  · subst y
    simpa using (measurable_snd : Measurable (fun p : Configuration d × SingleSite => p.2))
  · simpa [Function.update_of_ne hy, Function.comp_def] using
      (measurable_pi_apply y).comp measurable_fst

theorem updateSite_measurePreserving {d : ℕ} (x : Site d) :
    MeasurePreserving (fun p : Configuration d × SingleSite => Function.update p.1 x p.2)
      ((disorderLaw d).prod uniformSite) (disorderLaw d) := by
  classical
  refine ⟨measurable_updateSite x, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (measurable_updateSite x)
    (MeasurableSet.pi s.countable_toSet (fun y _ => ht y))]
  have he : (fun p : Configuration d × SingleSite => Function.update p.1 x p.2) ⁻¹'
      (s : Set (Site d)).pi t =
      ((s.erase x : Finset (Site d)) : Set (Site d)).pi t ×ˢ
        (if x ∈ s then t x else Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe,
      Finset.mem_erase]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · intro y hy
        simpa [Function.update_of_ne hy.1] using hp y hy.2
      · split_ifs with hx
        · simpa using hp x hx
        · trivial
    · rintro ⟨hp, hs⟩ y hy
      by_cases hxy : y = x
      · subst y
        simpa [hy] using hs
      · simpa [Function.update_of_ne hxy] using hp y ⟨hxy, hy⟩
  rw [he, Measure.prod_prod, disorderLaw,
    Measure.infinitePi_pi _ (fun y _ => ht y)]
  by_cases hx : x ∈ s
  · rw [if_pos hx, ← Finset.prod_erase_mul _ _ hx]
  · simp [hx]

instance uniformSite_nullSingleton : NullSingletonClass uniformSite := by
  constructor
  intro s
  have hs : (fun t : SingleSite => (t : ℝ)) ⁻¹' {(s : ℝ)} = {s} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subtype.val_injective.eq_iff
  rw [← hs, ← Measure.map_apply measurable_subtype_coe (measurableSet_singleton _),
    uniformSite_map_val]
  simp

end AndersonAC.SolS9Inf
