import AndersonAC.S9Fin.Scalar

noncomputable section
open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev OwnSiteIndex (i : n) := {j : n // j = i}
abbrev OtherSiteIndex (i : n) := {j : n // j ≠ i}

def ownSiteLaw (i : n) : Measure (OwnSiteIndex i → SingleSite) :=
  @Measure.pi (OwnSiteIndex i) (fun _ => SingleSite)
    (Subtype.fintype (fun j : n => j = i)) (fun _ => inferInstance) (fun _ => uniformSite)

def siteSplitEquiv (i : n) :
    (n → SingleSite) ≃ᵐ ((OwnSiteIndex i → SingleSite) × (OtherSiteIndex i → SingleSite)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : n => SingleSite) (fun j => j = i)

@[simp]
lemma siteSplitEquiv_apply_own (i : n) (ω : n → SingleSite) (j : OwnSiteIndex i) :
    (siteSplitEquiv i ω).1 j = ω j := by
  rfl

@[simp]
lemma siteSplitEquiv_apply_other (i : n) (ω : n → SingleSite) (j : OtherSiteIndex i) :
    (siteSplitEquiv i ω).2 j = ω j := by
  rfl

@[simp]
lemma siteSplitEquiv_symm_apply_own (i : n)
    (head : OwnSiteIndex i → SingleSite) (tail : OtherSiteIndex i → SingleSite)
    (j : OwnSiteIndex i) :
    (siteSplitEquiv i).symm (head, tail) j = head j := by
  simp [siteSplitEquiv, Equiv.piEquivPiSubtypeProd, j.property]
  congr 1
  exact Subtype.ext j.property.symm

@[simp]
lemma siteSplitEquiv_symm_apply_other (i : n)
    (head : OwnSiteIndex i → SingleSite) (tail : OtherSiteIndex i → SingleSite)
    (j : OtherSiteIndex i) :
    (siteSplitEquiv i).symm (head, tail) j = tail j := by
  simp [siteSplitEquiv, Equiv.piEquivPiSubtypeProd, j.property]

lemma measurePreserving_siteSplitEquiv (i : n) :
    MeasurePreserving (siteSplitEquiv i) (Measure.pi (fun _ : n => uniformSite))
      ((ownSiteLaw i).prod
        (Measure.pi (fun _ : OtherSiteIndex i => uniformSite))) := by
  exact measurePreserving_piEquivPiSubtypeProd
    (α := fun _ : n => SingleSite) (μ := fun _ : n => uniformSite)
    (p := fun j : n => j = i)

lemma integral_ownSite_eval (i : n) (g : SingleSite → ℝ)
    (hg : AEStronglyMeasurable g uniformSite) :
    (∫ head : OwnSiteIndex i → SingleSite, g (head ⟨i, rfl⟩) ∂ownSiteLaw i) =
      ∫ s : SingleSite, g s ∂uniformSite := by
  letI : Fintype (OwnSiteIndex i) := Subtype.fintype (fun j : n => j = i)
  simpa [ownSiteLaw] using
    (integral_comp_eval (μ := fun _ : OwnSiteIndex i => uniformSite)
      (i := (⟨i, rfl⟩ : OwnSiteIndex i)) hg)

end AndersonAC.SolS9
