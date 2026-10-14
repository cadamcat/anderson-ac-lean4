import AndersonAC.S9Inf.MismatchProof
import AndersonAC.S9Inf.Ergodic
import AndersonAC.S9Trans.GreenTranslation

/-! The actual fixed-energy all-sites probability join. -/

noncomputable section

open MeasureTheory OAI.Anderson Filter
open scoped Topology

namespace AndersonAC.SolS9Inf

theorem hasBoundary_translation_iff {d : ℕ} (coupling E : ℝ)
    (ω : Configuration d) (a x y : Site d) (g : ℂ) :
    hasBoundary (scalarGreen coupling (fun u => ω (u + a)) x y) E g ↔
      hasBoundary (scalarGreen coupling ω (x + a) (y + a)) E g := by
  have heq : (fun η : ℝ => scalarGreen coupling (fun u => ω (u + a)) x y
      ((E : ℂ) + (η : ℂ) * Complex.I)) =ᶠ[𝓝[>] 0]
      (fun η : ℝ => scalarGreen coupling ω (x + a) (y + a)
        ((E : ℂ) + (η : ℂ) * Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    apply greenTranslation_proof
    simpa using (show 0 < η from hη)
  exact Filter.tendsto_congr' heq

theorem positiveScalarBoundary_translation_iff {d : ℕ} (coupling E : ℝ)
    (ω : Configuration d) (a x : Site d) :
    positiveScalarBoundary coupling E x (fun u => ω (u + a)) ↔
      positiveScalarBoundary coupling E (x + a) ω := by
  simp only [positiveScalarBoundary, hasBoundary_translation_iff]

theorem some_positive_translation_invariant {d : ℕ} (coupling E : ℝ) (a : Site d) :
    AndersonAC.Prob.shiftConfig a ⁻¹' {ω | ∃ x, positiveScalarBoundary coupling E x ω} =
      {ω | ∃ x, positiveScalarBoundary coupling E x ω} := by
  ext ω
  change (∃ x, positiveScalarBoundary coupling E x (fun u => ω (u + a))) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x + a, (positiveScalarBoundary_translation_iff coupling E ω a x).mp hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨y - a, (positiveScalarBoundary_translation_iff coupling E ω a (y - a)).mpr ?_⟩
    simpa only [sub_add_cancel] using hy

theorem all_sites_positive_of_root_probability {d : ℕ} (hd : 0 < d)
    (coupling E : ℝ) (hcoupling : 0 < coupling)
    (hroot : 0 < disorderLaw d {ω | positiveScalarBoundary coupling E 0 ω})
    (hfinite : ∀ᵐ ω ∂disorderLaw d, ∀ x : Site d,
      ∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g)
    (hoff : ∀ᵐ ω ∂disorderLaw d, ∀ x y : Site d, x ≠ y →
      ∃ a : ℂ, hasBoundary (scalarGreen coupling ω x y) E a ∧ a ≠ 0) :
    ∀ᵐ ω ∂disorderLaw d, ∀ x : Site d, positiveScalarBoundary coupling E x ω := by
  have hmeas : MeasurableSet {ω : Configuration d | ∃ x,
      positiveScalarBoundary coupling E x ω} := by
    rw [show {ω : Configuration d | ∃ x, positiveScalarBoundary coupling E x ω} =
        ⋃ x : Site d, {ω | positiveScalarBoundary coupling E x ω} from by ext ω; simp]
    exact MeasurableSet.iUnion fun x =>
      (scalarGreen_boundary_measurable_of_potential potentialStrongContinuity_proof
        coupling E x x).2.1
  apply AndersonAC.SolS9.all_sites_of_positive_probability hd
    (positiveScalarBoundary coupling E) hmeas
    (some_positive_translation_invariant coupling E) hroot
  intro x y
  by_cases hxy : x = y
  · subst y
    simp
  · have hadmissible : ∀ᵐ ω ∂disorderLaw d,
        (∃ g : ℂ, hasBoundary (scalarGreen coupling ω x x) E g) ∧
        (∃ k : ℂ, hasBoundary (scalarGreen coupling ω y y) E k) ∧
        ∃ a : ℂ, hasBoundary (scalarGreen coupling ω x y) E a ∧ a ≠ 0 := by
      filter_upwards [hfinite, hoff] with ω hω hωoff
      exact ⟨hω x, hω y, hωoff x y hxy⟩
    have hmismatch := AndersonAC.SolS9.positivity_mismatch_null_proof
      d coupling E hcoupling x y hxy hadmissible
    have hnot : ∀ᵐ ω ∂disorderLaw d,
        ¬ (positiveScalarBoundary coupling E x ω ∧ zeroScalarBoundary coupling E y ω) := by
      simpa only [ae_iff, not_not] using hmismatch
    suffices h : ∀ᵐ ω ∂disorderLaw d,
        ¬ (positiveScalarBoundary coupling E x ω ∧ ¬ positiveScalarBoundary coupling E y ω) by
      simpa only [ae_iff, not_not] using h
    filter_upwards [hfinite, hnot] with ω hω hωnot
    rintro ⟨hx, hy⟩
    obtain ⟨k, hk⟩ := hω y
    have hkpos : ¬ 0 < k.im := fun h => hy ⟨k, hk, h⟩
    have hkzero : k.im = 0 := le_antisymm (le_of_not_gt hkpos)
      (scalarGreen_boundary_im_nonneg coupling E ω y k hk)
    exact hωnot ⟨hx, k, hk, hkzero⟩

end AndersonAC.SolS9Inf
