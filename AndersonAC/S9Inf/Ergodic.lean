import AndersonAC.Prob.Ergodic

/-! The iid zero-one law and the countable probability join in
`09-spectral.tex:410–458`. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9

/-- The frozen §9 translation action is definitionally `Prob.shiftConfig`.
The inline definition permits checking against the inventory without
importing it into this proof module. -/
theorem iid_translation_zero_one_proof (d : ℕ) (hd : 0 < d)
    (A : Set (Configuration d)) (hA : MeasurableSet A)
    (hinvariant : ∀ a : Site d,
      (fun ω : Configuration d => fun x => ω (x + a)) ⁻¹' A = A) :
    disorderLaw d A = 0 ∨ disorderLaw d A = 1 := by
  exact AndersonAC.Prob.disorderLaw_zero_one hd hA hinvariant

/-- Once every ordered-pair mismatch is null, an invariant positive-site
event of positive probability makes every site positive almost surely. -/
theorem all_sites_of_positive_probability {d : ℕ} (hd : 0 < d)
    (P : Site d → Configuration d → Prop)
    (hmeas : MeasurableSet {ω | ∃ x, P x ω})
    (hinvariant : ∀ a : Site d,
      AndersonAC.Prob.shiftConfig a ⁻¹' {ω | ∃ x, P x ω} = {ω | ∃ x, P x ω})
    (hpositive : 0 < disorderLaw d {ω | P 0 ω})
    (hmismatch : ∀ x y : Site d, disorderLaw d {ω | P x ω ∧ ¬ P y ω} = 0) :
    ∀ᵐ ω ∂disorderLaw d, ∀ x : Site d, P x ω := by
  have hsomepos : 0 < disorderLaw d {ω | ∃ x, P x ω} := by
    apply lt_of_lt_of_le hpositive
    apply measure_mono
    intro ω hω
    exact ⟨0, hω⟩
  have hsome : ∀ᵐ ω ∂disorderLaw d, ∃ x, P x ω :=
    (mem_ae_iff_prob_eq_one hmeas).mpr
      (AndersonAC.Prob.disorderLaw_eq_one_of_pos hd hmeas hinvariant hsomepos.ne')
  have hgood : ∀ᵐ ω ∂disorderLaw d, ∀ x y : Site d, ¬ (P x ω ∧ ¬ P y ω) := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    simpa only [ae_iff, not_not] using hmismatch x y
  filter_upwards [hsome, hgood] with ω hω hgoodω
  obtain ⟨x, hx⟩ := hω
  intro y
  by_contra hy
  exact hgoodω x y ⟨hx, hy⟩

end AndersonAC.SolS9
