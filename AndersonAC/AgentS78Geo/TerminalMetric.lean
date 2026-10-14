import AndersonAC.S78.Definitions
import AndersonAC.S78Metric.Chain
import AndersonAC.S78Metric.Saving
import AndersonAC.S6.Definitions

/-!
# The collapsed (terminal) pseudometric `d_T`

06-clearing.tex:50–54, 07-assembly.tex:50–56: nearest-neighbour edges touching `T` cost zero,
the others one; `d_T` is the shortest-path pseudometric. On a connected graph we prove the
pseudometric axioms, the unit bound on edges, the zero cost of an edge into `T`, and
antitonicity in `T`.
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Geo

open AndersonAC.S78

variable {ι : Type} [DecidableEq ι]

theorem pathCost_eq_sol (T : Finset ι) (xs : List ι) :
    pathCost T xs = AndersonAC.SolS78.pathCost T xs := rfl

theorem pathCost_cons_cons' (T : Finset ι) (x y : ι) (ys : List ι) :
    pathCost T (x :: y :: ys) = AndersonAC.SolS78.edgeCost T x y + pathCost T (y :: ys) :=
  AndersonAC.SolS78.pathCost_cons_cons T x y ys

theorem pathCost_singleton' (T : Finset ι) (x : ι) : pathCost T [x] = 0 :=
  AndersonAC.SolS78.pathCost_singleton T x

theorem pathCost_mono {T T' : Finset ι} (h : T ⊆ T') :
    ∀ xs : List ι, pathCost T' xs ≤ pathCost T xs
  | [] => by simp [pathCost_eq_sol, AndersonAC.SolS78.pathCost_nil]
  | [x] => by simp [pathCost_singleton']
  | x :: y :: ys => by
    rw [pathCost_cons_cons', pathCost_cons_cons']
    have h1 := AndersonAC.SolS78.edgeCost_mono_of_subset h x y
    have h2 := pathCost_mono h (y :: ys)
    omega

theorem edgeCost_comm (T : Finset ι) (x y : ι) :
    AndersonAC.SolS78.edgeCost T x y = AndersonAC.SolS78.edgeCost T y x := by
  unfold AndersonAC.SolS78.edgeCost
  by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy]

/-- Cost of `xs ++ ys` when `xs` ends where `ys` starts, with the junction counted once. -/
theorem pathCost_join (T : Finset ι) (v : ι) :
    ∀ (xs ys : List ι), pathCost T (xs ++ [v]) + pathCost T (v :: ys) =
      pathCost T (xs ++ v :: ys)
  | [], ys => by simp [pathCost_singleton']
  | [x], ys => by
    simp only [List.cons_append, List.nil_append]
    rw [pathCost_cons_cons', pathCost_cons_cons', pathCost_singleton']
    omega
  | x :: y :: xs, ys => by
    simp only [List.cons_append]
    rw [pathCost_cons_cons', pathCost_cons_cons']
    have := pathCost_join T v (y :: xs) ys
    simp only [List.cons_append] at this
    omega

theorem pathCost_reverse (T : Finset ι) : ∀ xs : List ι, pathCost T xs.reverse = pathCost T xs
  | [] => rfl
  | [x] => rfl
  | x :: y :: ys => by
    have hrev : (x :: y :: ys).reverse = (y :: ys).reverse ++ [x] := by simp
    rw [hrev, pathCost_cons_cons']
    have ih := pathCost_reverse T (y :: ys)
    -- (y :: ys).reverse = ys.reverse ++ [y]
    have h2 : (y :: ys).reverse = ys.reverse ++ [y] := by simp
    rw [h2] at ih ⊢
    have hj := pathCost_join T y ys.reverse [x]
    rw [List.append_assoc] at *
    simp only [List.singleton_append] at *
    rw [← hj, ih, pathCost_cons_cons', pathCost_singleton', edgeCost_comm]
    omega

/-- The set of path costs from `u` to `v`. -/
def costSet (G : SimpleGraph ι) (T : Finset ι) (u v : ι) : Set ℕ :=
  {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧
    xs.getLast? = some v ∧ pathCost T xs = n}

theorem terminalDistance_eq (G : SimpleGraph ι) (T : Finset ι) (u v : ι) :
    terminalDistance G T u v = ((sInf (costSet G T u v) : ℕ) : ℝ) := rfl

theorem costSet_nonempty {G : SimpleGraph ι} (hG : G.Connected) (T : Finset ι) (u v : ι) :
    (costSet G T u v).Nonempty := by
  obtain ⟨xs, h1, h2, h3⟩ := AndersonAC.SolS78.exists_chain_of_connected hG u v
  exact ⟨_, xs, h1, h2, h3, rfl⟩

theorem terminalDistance_nonneg (G : SimpleGraph ι) (T : Finset ι) (u v : ι) :
    0 ≤ terminalDistance G T u v := by
  rw [terminalDistance_eq]; positivity

theorem terminalDistance_le_of_chain (G : SimpleGraph ι) (T : Finset ι) {u v : ι}
    (xs : List ι) (h1 : xs.IsChain G.Adj) (h2 : xs.head? = some u) (h3 : xs.getLast? = some v) :
    terminalDistance G T u v ≤ pathCost T xs := by
  rw [terminalDistance_eq]
  have hmem : pathCost T xs ∈ costSet G T u v := ⟨xs, h1, h2, h3, rfl⟩
  exact_mod_cast Nat.sInf_le hmem

theorem exists_optimal_chain {G : SimpleGraph ι} (hG : G.Connected) (T : Finset ι) (u v : ι) :
    ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧ xs.getLast? = some v ∧
      (pathCost T xs : ℝ) = terminalDistance G T u v := by
  have hm := Nat.sInf_mem (costSet_nonempty hG T u v)
  obtain ⟨xs, h1, h2, h3, h4⟩ := hm
  exact ⟨xs, h1, h2, h3, by rw [terminalDistance_eq, h4]⟩

theorem terminalDistance_self (G : SimpleGraph ι) (T : Finset ι) (u : ι) :
    terminalDistance G T u u = 0 := by
  apply le_antisymm _ (terminalDistance_nonneg G T u u)
  have := terminalDistance_le_of_chain G T [u] (List.isChain_singleton u) rfl rfl
  simpa [pathCost_singleton'] using this

theorem terminalDistance_adj_le_one (G : SimpleGraph ι) (T : Finset ι) {u v : ι}
    (h : G.Adj u v) : terminalDistance G T u v ≤ 1 := by
  have := terminalDistance_le_of_chain G T [u, v] (List.isChain_pair.mpr h) rfl rfl
  refine this.trans ?_
  rw [pathCost_cons_cons', pathCost_singleton']
  exact_mod_cast (by have := AndersonAC.SolS78.edgeCost_le_one T u v; omega)

theorem terminalDistance_adj_terminal (G : SimpleGraph ι) (T : Finset ι) {u v : ι}
    (h : G.Adj u v) (hv : u ∈ T ∨ v ∈ T) : terminalDistance G T u v = 0 := by
  apply le_antisymm _ (terminalDistance_nonneg G T u v)
  have := terminalDistance_le_of_chain G T [u, v] (List.isChain_pair.mpr h) rfl rfl
  refine this.trans (le_of_eq ?_)
  rw [pathCost_cons_cons', pathCost_singleton']
  simp [AndersonAC.SolS78.edgeCost, hv]

theorem terminalDistance_antitone {G : SimpleGraph ι} (hG : G.Connected) {T T' : Finset ι}
    (h : T ⊆ T') (u v : ι) : terminalDistance G T' u v ≤ terminalDistance G T u v := by
  obtain ⟨xs, h1, h2, h3, h4⟩ := exists_optimal_chain hG T u v
  rw [← h4]
  exact (terminalDistance_le_of_chain G T' xs h1 h2 h3).trans (by exact_mod_cast pathCost_mono h xs)

theorem terminalDistance_symm {G : SimpleGraph ι} (hG : G.Connected) (T : Finset ι) (u v : ι) :
    terminalDistance G T u v = terminalDistance G T v u := by
  have key : ∀ a b, terminalDistance G T b a ≤ terminalDistance G T a b := by
    intro a b
    obtain ⟨xs, h1, h2, h3, h4⟩ := exists_optimal_chain hG T a b
    rw [← h4, ← pathCost_reverse T xs]
    apply terminalDistance_le_of_chain
    · rw [List.isChain_reverse]
      exact List.IsChain.imp (fun x y hxy => G.adj_symm hxy) h1
    · rw [List.head?_reverse]; exact h3
    · rw [List.getLast?_reverse]; exact h2
  exact le_antisymm (key v u) (key u v)

theorem terminalDistance_triangle {G : SimpleGraph ι} (hG : G.Connected) (T : Finset ι)
    (u v w : ι) :
    terminalDistance G T u w ≤ terminalDistance G T u v + terminalDistance G T v w := by
  obtain ⟨xs, h1, h2, h3, h4⟩ := exists_optimal_chain hG T u v
  obtain ⟨ys, k1, k2, k3, k4⟩ := exists_optimal_chain hG T v w
  rw [← h4, ← k4]
  -- write xs = xs' ++ [v], ys = v :: ys'
  obtain ⟨xs', rfl⟩ : ∃ xs', xs = xs' ++ [v] := by
    have hne : xs ≠ [] := by rintro rfl; simp at h2
    refine ⟨xs.dropLast, ?_⟩
    have := List.dropLast_append_getLast hne
    rw [List.getLast?_eq_some_getLast hne] at h3
    simp only [Option.some.injEq] at h3
    rw [h3] at this
    exact this.symm
  obtain ⟨ys', rfl⟩ : ∃ ys', ys = v :: ys' := by
    cases ys with
    | nil => simp at k2
    | cons a ys' => simp only [List.head?_cons, Option.some.injEq] at k2; exact ⟨ys', by rw [k2]⟩
  have hcost := pathCost_join T v xs' ys'
  have hle := terminalDistance_le_of_chain G T (u := u) (v := w) (xs' ++ v :: ys') ?_ ?_ ?_
  · calc terminalDistance G T u w ≤ (pathCost T (xs' ++ v :: ys') : ℝ) := hle
      _ = _ := by rw [← hcost]; push_cast; ring
  · have hx : (xs' ++ [v] ++ ys').IsChain G.Adj := by
      rw [List.isChain_append]
      refine ⟨h1, (List.isChain_cons.mp k1).2, ?_⟩
      intro a ha b hb
      simp at ha
      subst ha
      exact (List.isChain_cons.mp k1).1 b hb
    simpa using hx
  · cases xs' with
    | nil => simpa using h2
    | cons a l => simpa using h2
  · cases ys' with
    | nil => simpa using k3
    | cons a l =>
      rw [List.getLast?_append_of_ne_nil _ (by simp)]
      exact k3

theorem distanceToCore_lipschitz {α : Type} (dist : α → α → ℝ)
    (hnn : ∀ a b, 0 ≤ dist a b)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c) (core : Finset α) (i j : α) :
    AndersonAC.S6.distanceToCore dist core i ≤
      dist i j + AndersonAC.S6.distanceToCore dist core j := by
  unfold AndersonAC.S6.distanceToCore
  split_ifs with h
  · obtain ⟨b, hb, hbj⟩ := Finset.exists_mem_eq_inf' h (dist j)
    rw [hbj]
    exact (Finset.inf'_le _ hb).trans (htri i j b)
  · simpa using hnn i j

end AndersonAC.AgentS78Geo
