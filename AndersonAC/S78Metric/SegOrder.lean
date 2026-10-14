import AndersonAC.S78Metric.Range
import AndersonAC.S78Metric.Count

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {κ : Type} [Fintype κ]

/-- Hit groups of a list. -/
def hitSet (O : κ → Finset ι) (ys : List ι) : Finset κ :=
  Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)

/-- Arbitrary representative index per hit group (via choice). -/
def repIdx (O : κ → Finset ι) (ys : List ι) (a : ↥(hitSet O ys)) : ℕ :=
  Classical.choose (show ∃ i, ∃ h : i < ys.length, ys[i]'h ∈ O (a : κ) from by
    have ha : ∃ x ∈ ys, x ∈ O (a : κ) := (Finset.mem_filter.mp a.prop).2
    obtain ⟨x, hxys, hxa⟩ := ha
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxys
    exact ⟨i, hi, hix ▸ hxa⟩)

theorem repIdx_spec (O : κ → Finset ι) (ys : List ι) (a : ↥(hitSet O ys)) :
    ∃ h : repIdx O ys a < ys.length, ys[repIdx O ys a]'h ∈ O (a : κ) := by
  have H : ∃ i, ∃ h : i < ys.length, ys[i]'h ∈ O (a : κ) := by
    have ha : ∃ x ∈ ys, x ∈ O (a : κ) := (Finset.mem_filter.mp a.prop).2
    obtain ⟨x, hxys, hxa⟩ := ha
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxys
    exact ⟨i, hi, hix ▸ hxa⟩
  exact Classical.choose_spec H

/-- Representative indices are distinct for distinct groups when groups are disjoint. -/
theorem repIdx_injective (O : κ → Finset ι) (ys : List ι)
    (hdisj : ∀ a b : κ, a ≠ b → Disjoint (O a) (O b)) :
    Function.Injective (repIdx O ys) := by
  intro a b hab
  by_contra hne
  have hne' : (a : κ) ≠ (b : κ) := fun h => hne (Subtype.ext h)
  have hdis := hdisj _ _ hne'
  obtain ⟨ha_lt, ha_mem⟩ := repIdx_spec O ys a
  obtain ⟨hb_lt, hb_mem⟩ := repIdx_spec O ys b
  have ha_opt : ys[(repIdx O ys a)]? = some (ys[repIdx O ys a]'ha_lt) :=
    List.getElem?_eq_getElem ha_lt
  have hb_opt : ys[(repIdx O ys b)]? = some (ys[repIdx O ys b]'hb_lt) :=
    List.getElem?_eq_getElem hb_lt
  have hopt_eq : ys[(repIdx O ys a)]? = ys[(repIdx O ys b)]? := by
    rw [hab]
  have hsome_eq : some (ys[repIdx O ys a]'ha_lt) = some (ys[repIdx O ys b]'hb_lt) := by
    calc some (ys[repIdx O ys a]'ha_lt) = ys[(repIdx O ys a)]? := ha_opt.symm
      _ = ys[(repIdx O ys b)]? := hopt_eq
      _ = some (ys[repIdx O ys b]'hb_lt) := hb_opt
  have hval_eq : ys[repIdx O ys a]'ha_lt = ys[repIdx O ys b]'hb_lt :=
    Option.some_inj.mp hsome_eq
  have hmem_b : ys[repIdx O ys a]'ha_lt ∈ O (b : κ) := by
    rw [hval_eq]
    exact hb_mem
  have hmem_inter : ys[repIdx O ys a]'ha_lt ∈ O (a : κ) ∩ O (b : κ) := by
    simp [Finset.mem_inter, ha_mem, hmem_b]
  have hempty : O (a : κ) ∩ O (b : κ) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdis
  rw [hempty] at hmem_inter
  simp at hmem_inter

end AndersonAC.SolS78
