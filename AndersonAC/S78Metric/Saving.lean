import AndersonAC.S78Metric.Cycle

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι]
variable {κ : Type} [Fintype κ]

/-- New terminals. -/
def newTerms (O : κ → Finset ι) : Finset ι :=
  Finset.univ.biUnion O

theorem mem_newTerms {O : κ → Finset ι} {x : ι} :
    x ∈ newTerms O ↔ ∃ a, x ∈ O a := by
  simp [newTerms]

/-- Number of new-terminal visits (with multiplicity), by recursion to avoid
`List.filter` Bool/Prop friction. -/
def dcount (D : Finset ι) : List ι → ℕ
  | [] => 0
  | x :: ys => (if x ∈ D then 1 else 0) + dcount D ys

def headDisc (D : Finset ι) : List ι → ℕ
  | [] => 0
  | x :: _ => if x ∈ D then 1 else 0

theorem dcount_cons (D : Finset ι) (x : ι) (ys : List ι) :
    dcount D (x :: ys) = (if x ∈ D then 1 else 0) + dcount D ys := rfl

theorem edgeCost_mono_of_subset {T T' : Finset ι} (hsub : T ⊆ T')
    (x y : ι) : edgeCost T' x y ≤ edgeCost T x y := by
  unfold edgeCost
  by_cases hx : x ∈ T ∨ y ∈ T
  · have h' : x ∈ T' ∨ y ∈ T' := by
      rcases hx with hmem | hmem
      · exact Or.inl (hsub hmem)
      · exact Or.inr (hsub hmem)
    simp [hx, h']
  · simp only [hx, ↓reduceIte]
    by_cases h' : x ∈ T' ∨ y ∈ T' <;> simp [h']

theorem edgeCost_eq_of_not_mem {T D : Finset ι}
    {x y : ι} (hx : x ∉ D) (hy : y ∉ D) :
    edgeCost (T ∪ D) x y = edgeCost T x y := by
  unfold edgeCost
  simp [Finset.mem_union, hx, hy]

/-- Head-discount saving invariant, by structural induction. -/
theorem saving_invariant (T D : Finset ι) (ys : List ι) :
    pathCost T ys + headDisc D ys ≤ pathCost (T ∪ D) ys + 2 * dcount D ys := by
  induction ys with
  | nil => simp [pathCost_nil, headDisc, dcount]
  | cons x tail ih =>
    cases tail with
    | nil =>
      simp [pathCost_nil, pathCost_singleton, headDisc, dcount]
      by_cases h : x ∈ D <;> simp [h]
    | cons y ys' =>
      have hpcT : pathCost T (x :: y :: ys') =
          edgeCost T x y + pathCost T (y :: ys') :=
        pathCost_cons_cons T x y ys'
      have hpcT' : pathCost (T ∪ D) (x :: y :: ys') =
          edgeCost (T ∪ D) x y + pathCost (T ∪ D) (y :: ys') :=
        pathCost_cons_cons (T ∪ D) x y ys'
      have hdc : dcount D (x :: y :: ys') =
          (if x ∈ D then 1 else 0) + dcount D (y :: ys') := rfl
      have hhd : headDisc D (x :: y :: ys') = (if x ∈ D then 1 else 0) := rfl
      have hhd_tail : headDisc D (y :: ys') = (if y ∈ D then 1 else 0) := rfl
      have hmono : edgeCost (T ∪ D) x y ≤ edgeCost T x y :=
        edgeCost_mono_of_subset Finset.subset_union_left x y
      have hsave : edgeCost T x y ≤ edgeCost (T ∪ D) x y +
          (if x ∈ D ∨ y ∈ D then 1 else 0) := by
        by_cases hd : x ∈ D ∨ y ∈ D
        · simp [hd]
          have := edgeCost_le_one T x y
          omega
        · push Not at hd
          have heq : edgeCost (T ∪ D) x y = edgeCost T x y :=
            edgeCost_eq_of_not_mem hd.1 hd.2
          simp [hd, heq]
      rw [hpcT, hpcT', hdc, hhd]
      have htail := ih
      rw [hhd_tail] at htail
      by_cases hx : x ∈ D <;> by_cases hy : y ∈ D <;> simp [hx, hy] at hsave htail ⊢ <;> omega

theorem saving_le (T D : Finset ι) (ys : List ι) :
    pathCost T ys ≤ pathCost (T ∪ D) ys + 2 * dcount D ys := by
  have h := saving_invariant T D ys
  have hnn : 0 ≤ headDisc D ys := Nat.zero_le _
  omega

end AndersonAC.SolS78
