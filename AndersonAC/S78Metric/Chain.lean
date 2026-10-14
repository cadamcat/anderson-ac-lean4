import AndersonAC.S78Metric.Lemmas

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι]

/-- Any membership yields a split `ys = pre ++ [x] ++ suf`. Pure list fact. -/
theorem exists_pre_suf_of_mem {x : ι} {ys : List ι} (h : x ∈ ys) :
    ∃ pre suf : List ι, ys = pre ++ [x] ++ suf := by
  induction ys with
  | nil => simp at h
  | cons y ys' ih =>
    simp at h
    rcases Classical.em (x = y) with rfl | hne
    · exact ⟨[], ys', rfl⟩
    · obtain ⟨pre, suf, rfl⟩ := ih (h.resolve_left hne)
      exact ⟨y :: pre, suf, by simp⟩

/-- Existence of a list chain between any two vertices in a connected graph. -/
theorem exists_chain_of_connected {G : SimpleGraph ι} (hconn : G.Connected)
    (u v : ι) : ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧
      xs.getLast? = some v := by
  obtain ⟨p⟩ := hconn u v
  refine ⟨p.support, p.isChain_adj_support, ?_, ?_⟩
  · have hne : p.support ≠ [] := p.support_ne_nil
    rw [List.head?_eq_some_head hne, p.head_support]
  · have hne : p.support ≠ [] := p.support_ne_nil
    rw [List.getLast?_eq_some_getLast hne, p.getLast_support]

/-- Any chain's old cost upper-bounds the old terminal distance hypothesis. -/
theorem oldCost_ge_of_hold {G : SimpleGraph ι} (T : Finset ι)
    (c μ : ℝ) (hold : ∀ u v, c * (G.dist u v : ℝ) - μ ≤ terminalDistance G T u v)
    {u v : ι} {xs : List ι} (hchain : xs.IsChain G.Adj)
    (hhead : xs.head? = some u) (hlast : xs.getLast? = some v) :
    c * (G.dist u v : ℝ) - μ ≤ ((pathCost T xs : ℕ) : ℝ) := by
  have hmem : pathCost T xs ∈ {n : ℕ | ∃ ys : List ι, ys.IsChain G.Adj ∧
      ys.head? = some u ∧ ys.getLast? = some v ∧ pathCost T ys = n} :=
    ⟨xs, hchain, hhead, hlast, rfl⟩
  have h1 := hold u v
  unfold terminalDistance at h1
  have h2 : ((sInf {n : ℕ | ∃ ys : List ι, ys.IsChain G.Adj ∧ ys.head? = some u ∧
      ys.getLast? = some v ∧ pathCost T ys = n} : ℕ) : ℝ) ≤
      ((pathCost T xs : ℕ) : ℝ) := by
    apply Nat.cast_le.mpr
    exact Nat.sInf_le hmem
  linarith

end AndersonAC.SolS78
