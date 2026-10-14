import Mathlib

/-!
# WP10 construction, C5c helper: a bounded piece of a huge component

08-history.tex:119–125. A pending site that survives a clearing stage without a new label
lies in a huge snapshot component (more than `t_j^{-ν}` sites). The dichotomy of
`PendingHistory` needs a set `S ∋ x` of more than `t_j^{-ν}` pending sites *within
distance* `C 4^{(8+ν)j}` of `x`. A huge component may have large diameter; this lemma takes
a connected piece of exactly `K+1` sites around `x`, each joined to `x` by a walk of length
at most `K` (so, with `R_j`-edges, at physical distance at most `K R_j`).
-/

set_option autoImplicit false

namespace AndersonAC.AgentS78

/-- In a finite graph, if more than `K` vertices are reachable from `x`, some `K+1` of them,
including `x`, are joined to `x` by walks of length at most `K`. -/
theorem exists_bounded_piece {V : Type} [Fintype V] (G : SimpleGraph V) (x : V)
    [DecidablePred (G.Reachable x)] (K : ℕ)
    (hbig : K < (Finset.univ.filter (G.Reachable x)).card) :
    ∃ S : Finset V, x ∈ S ∧ S.card = K + 1 ∧
      ∀ y ∈ S, ∃ w : G.Walk x y, w.length ≤ K := by
  classical
  -- grow the piece one vertex at a time
  have key : ∀ k ≤ K, ∃ S : Finset V, x ∈ S ∧ S.card = k + 1 ∧
      ∀ y ∈ S, ∃ w : G.Walk x y, w.length ≤ k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨{x}, Finset.mem_singleton_self x, by simp, fun y hy => by
        rw [Finset.mem_singleton.mp hy]; exact ⟨SimpleGraph.Walk.nil, le_refl _⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨S, hxS, hcard, hwalk⟩ := ih (Nat.le_of_succ_le hk)
      -- a reachable vertex outside S
      have hlt : S.card < (Finset.univ.filter (G.Reachable x)).card := by omega
      have hsub : ¬ (Finset.univ.filter (G.Reachable x)) ⊆ S := by
        intro h; exact absurd (Finset.card_le_card h) (not_le.mpr hlt)
      obtain ⟨z, hz, hzS⟩ := Finset.not_subset.mp hsub
      have hzr : G.Reachable x z := (Finset.mem_filter.mp hz).2
      obtain ⟨p⟩ := hzr
      obtain ⟨dt, -, hd1, hd2⟩ := p.exists_boundary_dart (↑S : Set V) hxS hzS
      obtain ⟨w, hw⟩ := hwalk dt.fst hd1
      refine ⟨insert dt.snd S, Finset.mem_insert_of_mem hxS, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hd2, hcard]
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · refine ⟨w.concat dt.adj, ?_⟩
          rw [SimpleGraph.Walk.length_concat]; omega
        · obtain ⟨w', hw'⟩ := hwalk y hy
          exact ⟨w', by omega⟩
  exact key K le_rfl

end AndersonAC.AgentS78
