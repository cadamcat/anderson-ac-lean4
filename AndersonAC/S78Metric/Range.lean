import AndersonAC.S78Metric.Segments

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι]

/-- Edge at position `i` (0 if out of bounds). -/
def edgeAt (T : Finset ι) (ys : List ι) (i : ℕ) : ℕ :=
  if h : i + 1 < ys.length then
    edgeCost T (ys[i]'(by omega)) (ys[i + 1]'h)
  else 0

def edgeSum (T : Finset ι) (ys : List ι) : ℕ :=
  ∑ i ∈ Finset.range (ys.length - 1), edgeAt T ys i

theorem edgeAt_zero (T : Finset ι) (x y : ι) (ys : List ι) :
    edgeAt T (x :: y :: ys) 0 = edgeCost T x y := by
  unfold edgeAt
  simp [List.getElem_cons_zero]

theorem edgeAt_succ (T : Finset ι) (x : ι) (ys : List ι) (i : ℕ) :
    edgeAt T (x :: ys) (i + 1) = edgeAt T ys i := by
  have hlen : (x :: ys).length = ys.length + 1 := rfl
  unfold edgeAt
  by_cases h1 : i + 1 + 1 < (x :: ys).length
  · have h2 : i + 1 < ys.length := by omega
    have h1a : i + 1 < (x :: ys).length := by omega
    simp only [h1, h2, dite_true]
    have e1 : ((x :: ys)[i + 1]'h1a = ys[i]'(by omega)) :=
      List.getElem_cons_succ x ys i h1a
    have e2 : ((x :: ys)[i + 1 + 1]'h1 = ys[i + 1]'h2) :=
      List.getElem_cons_succ x ys (i + 1) h1
    rw [e1, e2]
  · have h2 : ¬ i + 1 < ys.length := by omega
    simp [h2]

theorem pathCost_eq_edgeSum (T : Finset ι) (ys : List ι) :
    pathCost T ys = edgeSum T ys := by
  induction ys with
  | nil => simp [pathCost_nil, edgeSum, edgeAt]
  | cons x tail ih =>
    cases tail with
    | nil =>
      simp [pathCost_singleton, edgeSum, edgeAt]
    | cons y ys' =>
      have hpc : pathCost T (x :: y :: ys') =
          edgeCost T x y + pathCost T (y :: ys') :=
        pathCost_cons_cons T x y ys'
      have hlen1 : (x :: y :: ys').length - 1 = (y :: ys').length := by simp
      have hlen2 : (y :: ys').length - 1 = ys'.length := by simp
      have hes : edgeSum T (x :: y :: ys') =
          (∑ i ∈ Finset.range ys'.length,
            edgeAt T (x :: y :: ys') (i + 1)) + edgeAt T (x :: y :: ys') 0 := by
        unfold edgeSum
        rw [hlen1]
        have h1 : (y :: ys').length = ys'.length + 1 := by simp
        rw [h1, Finset.sum_range_succ']
      rw [hes, edgeAt_zero]
      have hshift : ∀ i ∈ Finset.range ys'.length,
          edgeAt T (x :: y :: ys') (i + 1) = edgeAt T (y :: ys') i := by
        intro i _
        exact edgeAt_succ T x (y :: ys') i
      rw [Finset.sum_congr rfl hshift]
      have heTail : edgeSum T (y :: ys') =
          ∑ i ∈ Finset.range ys'.length, edgeAt T (y :: ys') i := by
        unfold edgeSum
        rw [hlen2]
      rw [hpc, ih, heTail]
      ac_rfl

/-- Monotone prefix bound from successive strict increases. -/
theorem mono_prefix_le {p : ℕ → ℕ} {n : ℕ} (h : ∀ j, j < n → p j < p (j + 1)) :
    ∀ m, m ≤ n → p 0 ≤ p m := by
  intro m
  induction m with
  | zero => intro _; exact le_rfl
  | succ m ih =>
    intro hm
    have hm1 : m ≤ n := by omega
    exact le_trans (ih hm1) (le_of_lt (h m (by omega)))

/-- Telescoping sum over consecutive Ico intervals. -/
theorem sum_Ico_chain (f : ℕ → ℕ) (p : ℕ → ℕ) (n : ℕ)
    (h : ∀ j, j < n → p j < p (j + 1)) :
    ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (p j) (p (j + 1)), f i
      = ∑ i ∈ Finset.Ico (p 0) (p n), f i := by
  have key : ∀ n, (∀ j, j < n → p j < p (j + 1)) →
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (p j) (p (j + 1)), f i
        = ∑ i ∈ Finset.Ico (p 0) (p n), f i := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      have h' : ∀ j, j < n → p j < p (j + 1) := fun j hj => h j (by omega)
      have h01 : p 0 ≤ p n := mono_prefix_le h' n le_rfl
      have h12 : p n ≤ p (n + 1) := le_of_lt (h n (Nat.lt_succ_self n))
      rw [Finset.sum_range_succ, ih h']
      exact Finset.sum_Ico_consecutive f h01 h12
  exact key n h

/-- Edge-sum of a contiguous sublist equals the sum over its index interval. -/
theorem edgeSum_sublist (T : Finset ι) (l : List ι) (p q : ℕ)
    (hle : p ≤ q) (hlt : q < l.length) :
    edgeSum T ((l.drop p).take (q - p + 1)) = ∑ i ∈ Finset.Ico p q, edgeAt T l i := by
  have hplen : p < l.length := lt_of_le_of_lt hle hlt
  have hSlen : ((l.drop p).take (q - p + 1)).length = q - p + 1 := by
    have hlen_drop : (l.drop p).length = l.length - p := List.length_drop
    have hle2 : q - p + 1 ≤ l.length - p := by omega
    simp [List.length_take, hlen_drop, min_eq_left hle2]
  have hsub : q - p + 1 - 1 = q - p := Nat.add_sub_cancel _ _
  have hIco : ∑ i ∈ Finset.Ico p q, edgeAt T l i
      = ∑ i ∈ Finset.range (q - p), edgeAt T l (p + i) := by
    rw [Finset.sum_Ico_eq_sum_range]
  rw [hIco]
  unfold edgeSum
  rw [hSlen, hsub]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < q - p := Finset.mem_range.mp hi
  have hiS : i + 1 < ((l.drop p).take (q - p + 1)).length := by omega
  have hli : p + i + 1 < l.length := by omega
  unfold edgeAt
  simp only [hiS, hli, dite_true]
  simp only [List.getElem_take, List.getElem_drop, Nat.add_assoc]

end AndersonAC.SolS78
