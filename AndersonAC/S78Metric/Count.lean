import AndersonAC.S78Metric.Saving

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι]
variable {κ : Type} [Fintype κ]

/-- Recursive count equals the distinct intersection card for Nodup lists. -/
theorem dcount_eq_inter_card (D : Finset ι) (ys : List ι) (hnd : ys.Nodup) :
    dcount D ys = (ys.toFinset ∩ D).card := by
  induction ys with
  | nil => simp [dcount]
  | cons x ys' ih =>
    have hx : x ∉ ys' := (List.nodup_cons.mp hnd).1
    have hnd' : ys'.Nodup := (List.nodup_cons.mp hnd).2
    have ih' := ih hnd'
    have hdc : dcount D (x :: ys') =
        (if x ∈ D then 1 else 0) + dcount D ys' := rfl
    rw [hdc, ih']
    have hmem : x ∉ ys'.toFinset := by
      simp [List.mem_toFinset, hx]
    have hcons : (x :: ys').toFinset = insert x ys'.toFinset := List.toFinset_cons
    rw [hcons]
    by_cases hDx : x ∈ D
    · have h1 : (insert x ys'.toFinset ∩ D) = insert x (ys'.toFinset ∩ D) := by
        ext z
        simp [Finset.mem_insert, Finset.mem_inter, hDx]
      rw [h1]
      have hnot : x ∉ ys'.toFinset ∩ D := by
        simp [Finset.mem_inter, hmem]
      rw [Finset.card_insert_of_notMem hnot]
      simp [hDx]
      omega
    · have h1 : (insert x ys'.toFinset ∩ D) = (ys'.toFinset ∩ D) := by
        ext z
        simp [Finset.mem_inter, hDx]
      rw [h1]
      simp [hDx]

/-- Distinct new-terminal visits are bounded by hit groups times M. -/
theorem dcount_le_hit_mul (O : κ → Finset ι) (M : ℕ)
    (hsize : ∀ a, (O a).card ≤ M)
    (ys : List ι) (hnd : ys.Nodup) :
    let D := newTerms O
    let S := Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)
    dcount D ys ≤ S.card * M := by
  simp only
  rw [dcount_eq_inter_card _ _ hnd]
  classical
  have hDeq : ys.toFinset ∩ newTerms O =
      (Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)).biUnion
        (fun a => ys.toFinset ∩ O a) := by
    ext z
    simp [Finset.mem_inter, Finset.mem_biUnion, mem_newTerms, List.mem_toFinset]
    constructor
    · rintro ⟨hys, a, ha⟩
      exact ⟨a, ⟨z, hys, ha⟩, hys, ha⟩
    · rintro ⟨a, ⟨x, hx, _⟩, hys, ha⟩
      exact ⟨hys, a, ha⟩
  rw [hDeq]
  calc ((Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)).biUnion
        (fun a => ys.toFinset ∩ O a)).card
      ≤ ∑ a ∈ Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a),
        (ys.toFinset ∩ O a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a), M := by
        apply Finset.sum_le_sum
        intro a _
        calc (ys.toFinset ∩ O a).card ≤ (O a).card :=
              Finset.card_le_card Finset.inter_subset_right
          _ ≤ M := hsize a
    _ = (Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)).card * M := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

end AndersonAC.SolS78
