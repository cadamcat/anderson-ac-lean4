import AndersonAC.S9.OwnSite

/-! The own-site reconstruction is a measure-preserving reindexing of the
infinite product.  The proof checks finite-coordinate cylinders and uses
uniqueness of the infinite product measure. -/

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal

namespace AndersonAC.SolS9

private abbrev ComplementIndex (d : ℕ) (x : Site d) := {y : Site d // y ≠ x}

private def complementBoxIndices {d : ℕ} (x : Site d) (s : Finset (Site d)) :
    Finset (ComplementIndex d x) := by
  classical
  exact (s.erase x).attach.image fun i =>
    (⟨i.1, (Finset.mem_erase.mp i.2).1⟩ : ComplementIndex d x)

private theorem restoreSite_preimage_pi {d : ℕ} (x : Site d)
    (s : Finset (Site d)) (B : Site d → Set SingleSite) :
    (fun p : ComplementConfiguration d x × SingleSite => restoreSite x p.1 p.2) ⁻¹'
      Set.pi s B =
        Set.pi (complementBoxIndices x s) (fun j => B j.1) ×ˢ
          (if x ∈ s then B x else Set.univ) := by
  classical
  ext p
  rcases p with ⟨ξ, a⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod]
  constructor
  · intro hp
    constructor
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      have hi' : i.1 ∈ s := (Finset.mem_erase.mp i.2).2
      have hix : i.1 ≠ x := (Finset.mem_erase.mp i.2).1
      simpa [restoreSite, hix] using hp i.1 hi'
    · by_cases hx : x ∈ s
      · simp [hx]
        simpa [restoreSite] using hp x hx
      · simp [hx]
  · rintro ⟨hc, ha⟩ i hi
    by_cases hix : i = x
    · subst i
      have hown : x ∈ s → a ∈ B x := by simpa using ha
      have hown' : a ∈ B x := hown hi
      simpa [restoreSite] using hown'
    · have hiErase : i ∈ s.erase x := Finset.mem_erase.mpr ⟨hix, hi⟩
      let j : ComplementIndex d x := ⟨i, hix⟩
      have hj : j ∈ complementBoxIndices x s := by
        apply Finset.mem_image.mpr
        refine ⟨⟨i, hiErase⟩, Finset.mem_attach _ _, ?_⟩
        apply Subtype.ext
        rfl
      have hcoord := hc j hj
      simpa [restoreSite, hix, j] using hcoord

private theorem complement_box_prod {d : ℕ} (x : Site d)
    (s : Finset (Site d)) (B : Site d → Set SingleSite) :
    (∏ j ∈ complementBoxIndices x s, uniformSite (B j.1)) =
      ∏ i ∈ s.erase x, uniformSite (B i) := by
  classical
  unfold complementBoxIndices
  rw [Finset.prod_image (s := (s.erase x).attach)
    (g := fun i => (⟨i.1, (Finset.mem_erase.mp i.2).1⟩ : ComplementIndex d x))]
  · exact Finset.prod_attach (s.erase x) (fun i => uniformSite (B i))
  · intro a ha b hb h
    apply Subtype.ext
    exact congrArg (fun j : ComplementIndex d x => j.1) h

private theorem site_box_prod_split {d : ℕ} (x : Site d)
    (s : Finset (Site d)) (B : Site d → Set SingleSite) :
    (∏ i ∈ s, uniformSite (B i)) =
      (if x ∈ s then uniformSite (B x) else 1) *
        ∏ i ∈ s.erase x, uniformSite (B i) := by
  classical
  by_cases hx : x ∈ s
  · rw [if_pos hx, ← Finset.mul_prod_erase s (fun i => uniformSite (B i)) hx]
  · simp [hx]

private theorem restoreSite_map_disorderLaw (d : ℕ) (x : Site d) :
    ((complementLaw d x).prod uniformSite).map
      (fun p : ComplementConfiguration d x × SingleSite => restoreSite x p.1 p.2) =
      disorderLaw d := by
  classical
  let f : ComplementConfiguration d x × SingleSite → Configuration d :=
    fun p => restoreSite x p.1 p.2
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro y
    by_cases hy : y = x
    · subst y
      change Measurable (fun p : ComplementConfiguration d x × SingleSite =>
        restoreSite x p.1 p.2 x)
      simp only [restoreSite]
      exact measurable_snd
    · change Measurable (fun p : ComplementConfiguration d x × SingleSite =>
        restoreSite x p.1 p.2 y)
      simp only [restoreSite, dif_neg hy]
      fun_prop
  apply Measure.eq_infinitePi
  intro s B hB
  have hbox : MeasurableSet (Set.pi s B) := MeasurableSet.pi s.countable_toSet (by
    intro i hi
    exact hB i)
  rw [Measure.map_apply hf hbox, restoreSite_preimage_pi]
  rw [Measure.prod_prod]
  rw [complementLaw,
    Measure.infinitePi_pi (μ := fun _ : ComplementIndex d x => uniformSite)
      (s := complementBoxIndices x s) (t := fun j => B j.1) (by
        intro j hj
        exact hB j.1)]
  rw [complement_box_prod]
  by_cases hx : x ∈ s
  · simpa [hx, mul_comm] using (site_box_prod_split x s B).symm
  · simp [hx]

/-- Restoring the independent own-site coordinate reconstructs the full
Anderson disorder law. -/
theorem RestoreSiteLawInput_proof :
    ∀ (d : ℕ) (x : Site d),
      MeasurePreserving
        (fun p : ComplementConfiguration d x × SingleSite => restoreSite x p.1 p.2)
        ((complementLaw d x).prod uniformSite) (disorderLaw d) := by
  intro d x
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro y
    by_cases hy : y = x
    · subst y
      change Measurable (fun p : ComplementConfiguration d x × SingleSite =>
        restoreSite x p.1 p.2 x)
      simp only [restoreSite]
      exact measurable_snd
    · change Measurable (fun p : ComplementConfiguration d x × SingleSite =>
        restoreSite x p.1 p.2 y)
      simp only [restoreSite, dif_neg hy]
      fun_prop
  · exact restoreSite_map_disorderLaw d x

end AndersonAC.SolS9
