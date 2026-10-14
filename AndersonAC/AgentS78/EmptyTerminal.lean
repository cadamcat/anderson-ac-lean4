import AndersonAC.S78.Definitions
import AndersonAC.S78Metric.Chain

/-! With no terminal sites the terminal distance dominates the graph distance. -/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem dist_le_pathCost_empty {ι : Type} [DecidableEq ι] (G : SimpleGraph ι)
    (hconn : G.Connected) :
    ∀ (xs : List ι) (u v : ι), xs.IsChain G.Adj → xs.head? = some u → xs.getLast? = some v →
      G.dist u v ≤ pathCost (∅ : Finset ι) xs := by
  intro xs
  induction xs with
  | nil => intro u v _ h; simp at h
  | cons x ys ih =>
    intro u v hchain hhead hlast
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases ys with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp
    | cons y zs =>
      rw [List.isChain_cons_cons] at hchain
      have hlast' : (y :: zs).getLast? = some v := by
        rw [List.getLast?_cons_cons] at hlast; exact hlast
      have h1 := ih y v hchain.2 rfl hlast'
      have hcost : pathCost (∅ : Finset ι) (x :: y :: zs) = 1 + pathCost ∅ (y :: zs) := by
        show AndersonAC.SolS78.pathCost (∅ : Finset ι) (x :: y :: zs) =
          1 + AndersonAC.SolS78.pathCost ∅ (y :: zs)
        rw [AndersonAC.SolS78.pathCost_cons_cons]
        simp [AndersonAC.SolS78.edgeCost]
      rw [hcost]
      have hxy : G.dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hchain.1
      calc G.dist x v ≤ G.dist x y + G.dist y v := hconn.dist_triangle
        _ ≤ 1 + pathCost ∅ (y :: zs) := by omega

/-- Lower bound on the terminal distance with an empty terminal set. -/
theorem dist_le_terminalDistance_empty {ι : Type} [DecidableEq ι] (G : SimpleGraph ι)
    (hconn : G.Connected) (u v : ι) :
    (G.dist u v : ℝ) ≤ terminalDistance G (∅ : Finset ι) u v := by
  unfold terminalDistance
  set S := {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧
    xs.getLast? = some v ∧ pathCost (∅ : Finset ι) xs = n} with hS
  have hne : S.Nonempty := by
    obtain ⟨xs, hc, hh, hl⟩ := AndersonAC.SolS78.exists_chain_of_connected hconn u v
    exact ⟨_, xs, hc, hh, hl, rfl⟩
  obtain ⟨xs, hc, hh, hl, hcost⟩ := Nat.sInf_mem hne
  exact_mod_cast hcost ▸ dist_le_pathCost_empty G hconn xs u v hc hh hl

end AndersonAC.AgentS78
