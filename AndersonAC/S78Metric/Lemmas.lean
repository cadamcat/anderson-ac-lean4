import AndersonAC.S78Metric.Defs

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι]

/-- Edge cost: 0 if either endpoint is terminal, else 1. -/
def edgeCost (T : Finset ι) (x y : ι) : ℕ :=
  if x ∈ T ∨ y ∈ T then 0 else 1

theorem edgeCost_nonneg (T : Finset ι) (x y : ι) : 0 ≤ edgeCost T x y := Nat.zero_le _

theorem pathCost_nil (T : Finset ι) : pathCost T ([] : List ι) = 0 := by
  unfold pathCost; simp

theorem pathCost_singleton (T : Finset ι) (x : ι) : pathCost T [x] = 0 := by
  unfold pathCost; simp

theorem pathCost_cons_cons (T : Finset ι) (x y : ι) (ys : List ι) :
    pathCost T (x :: y :: ys) = edgeCost T x y + pathCost T (y :: ys) := by
  unfold pathCost edgeCost
  simp only [List.tail_cons, List.zip_cons_cons]
  simp [List.sum_cons]

theorem edgeCost_le_one (T : Finset ι) (x y : ι) : edgeCost T x y ≤ 1 := by
  unfold edgeCost
  by_cases h : x ∈ T ∨ y ∈ T <;> simp [h]

/-- Bridge cost between two lists: the edge joining them, or 0 if either is empty. -/
def bridgeCost (T : Finset ι) (l₁ l₂ : List ι) : ℕ :=
  match l₁.getLast?, l₂.head? with
  | some a, some b => edgeCost T a b
  | _, _ => 0

theorem bridgeCost_of_nil_left (T : Finset ι) (l₂ : List ι) :
    bridgeCost T [] l₂ = 0 := by simp [bridgeCost]

theorem bridgeCost_of_nil_right (T : Finset ι) (l₁ : List ι) :
    bridgeCost T l₁ [] = 0 := by
  simp [bridgeCost]

theorem pathCost_append (T : Finset ι) (l₁ l₂ : List ι) :
    pathCost T (l₁ ++ l₂) = pathCost T l₁ + bridgeCost T l₁ l₂ + pathCost T l₂ := by
  induction l₁ with
  | nil => simp [pathCost_nil, bridgeCost_of_nil_left]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases l₂ with
      | nil => simp [pathCost_nil, pathCost_singleton, bridgeCost]
      | cons y ys =>
        have h1 : pathCost T ([x] ++ y :: ys) = pathCost T (x :: y :: ys) := rfl
        rw [h1, pathCost_cons_cons, pathCost_singleton]
        simp [bridgeCost]
    | cons y ys =>
      have hcons : (x :: y :: ys) ++ l₂ = x :: y :: (ys ++ l₂) := by simp
      rw [hcons, pathCost_cons_cons, pathCost_cons_cons]
      have ih' : pathCost T (y :: (ys ++ l₂)) =
          pathCost T (y :: ys) + bridgeCost T (y :: ys) l₂ + pathCost T l₂ := by
        have := ih
        simp only [List.cons_append] at this
        exact this
      rw [ih']
      -- bridgeCost (x::y::ys) l₂ = bridgeCost (y::ys) l₂ (same last)
      have hbridge : bridgeCost T (x :: y :: ys) l₂ = bridgeCost T (y :: ys) l₂ := by
        unfold bridgeCost
        simp [List.getLast?_cons_cons]
      rw [hbridge]
      omega

end AndersonAC.SolS78
