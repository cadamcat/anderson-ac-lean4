import AndersonAC.AgentS78.Construction.TileCoverParts

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78

open AndersonAC.S78

private lemma torus_step_adj {d m : ℕ} (hm : 0 < m) (x : Torus d m) (i : Fin d) :
    (nnGraph d m).Adj x (x + OAI.Anderson.torusBasisVector i) := by
  have hlen : 2 ≤ OAI.Anderson.sideLength m := by
    rw [OAI.Anderson.sideLength]
    have hexp : 0 < 20 * m := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hexp.ne'
    rw [hn, pow_succ]
    have hpow : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by omega)
    omega
  letI : Fact (1 < OAI.Anderson.sideLength m) := ⟨by omega⟩
  rw [nnGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro hxy
    have hcoord := congrArg (fun z : Torus d m => z i) hxy
    have hsum : x i + 1 = x i + 0 := by
      simpa [OAI.Anderson.torusBasisVector] using hcoord.symm
    have h10 : (1 : ZMod (OAI.Anderson.sideLength m)) = 0 := add_left_cancel hsum
    exact one_ne_zero h10
  · exact Or.inl ⟨i, Or.inl rfl⟩

private lemma torus_plus_walk {d m : ℕ} (hm : 0 < m) (i : Fin d) :
    ∀ (x : Torus d m) (n : ℕ),
      ∃ p : (nnGraph d m).Walk x (x + n • OAI.Anderson.torusBasisVector i), p.length = n := by
  intro x n
  induction n generalizing x with
  | zero =>
      have hx : x = x + 0 • OAI.Anderson.torusBasisVector i := by simp
      let p := (SimpleGraph.Walk.nil : (nnGraph d m).Walk x x).copy rfl hx
      exact ⟨p, by simp [p, SimpleGraph.Walk.length_copy]⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih (x + OAI.Anderson.torusBasisVector i)
      have hend : x + OAI.Anderson.torusBasisVector i +
          n • OAI.Anderson.torusBasisVector i =
          x + (n + 1) • OAI.Anderson.torusBasisVector i := by
        simp only [succ_nsmul]
        abel
      let p' := (SimpleGraph.Walk.cons (torus_step_adj hm x i) p).copy rfl hend
      exact ⟨p', by simp [p', SimpleGraph.Walk.length_copy, hp]⟩

private lemma torus_step_sub_adj {d m : ℕ} (hm : 0 < m) (x : Torus d m) (i : Fin d) :
    (nnGraph d m).Adj x (x - OAI.Anderson.torusBasisVector i) := by
  have h := torus_step_adj hm (x - OAI.Anderson.torusBasisVector i) i
  have h' : (nnGraph d m).Adj (x - OAI.Anderson.torusBasisVector i) x := by
    simpa [sub_add_cancel] using h
  exact h'.symm

private lemma torus_minus_walk {d m : ℕ} (hm : 0 < m) (i : Fin d) :
    ∀ (x : Torus d m) (n : ℕ),
      ∃ p : (nnGraph d m).Walk x (x - n • OAI.Anderson.torusBasisVector i), p.length = n := by
  intro x n
  induction n generalizing x with
  | zero =>
      have hx : x = x - 0 • OAI.Anderson.torusBasisVector i := by simp
      let p := (SimpleGraph.Walk.nil : (nnGraph d m).Walk x x).copy rfl hx
      exact ⟨p, by simp [p, SimpleGraph.Walk.length_copy]⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih (x - OAI.Anderson.torusBasisVector i)
      have hend : x - OAI.Anderson.torusBasisVector i -
          n • OAI.Anderson.torusBasisVector i =
          x - (n + 1) • OAI.Anderson.torusBasisVector i := by
        simp only [succ_nsmul]
        abel
      let p' := (SimpleGraph.Walk.cons (torus_step_sub_adj hm x i) p).copy rfl hend
      exact ⟨p', by simp [p', SimpleGraph.Walk.length_copy, hp]⟩

private lemma torus_coord_walk {d m : ℕ} (hm : 0 < m) (x y : Torus d m) (i : Fin d) :
    ∃ p : (nnGraph d m).Walk x (Function.update x i (y i)),
      p.length = (y i - x i).valMinAbs.natAbs := by
  let z : ZMod (OAI.Anderson.sideLength m) := y i - x i
  by_cases hnonneg : 0 ≤ z.valMinAbs
  · let n := z.valMinAbs.toNat
    have hnZ : (n : ℤ) = z.valMinAbs := Int.toNat_of_nonneg hnonneg
    have hcast : (n : ZMod (OAI.Anderson.sideLength m)) = z := by
      calc
        (n : ZMod (OAI.Anderson.sideLength m)) = ((n : ℤ) : ZMod (OAI.Anderson.sideLength m)) := by norm_cast
        _ = (z.valMinAbs : ZMod (OAI.Anderson.sideLength m)) := by rw [hnZ]
        _ = z := ZMod.coe_valMinAbs z
    have hcoord : x i + (n : ZMod (OAI.Anderson.sideLength m)) = y i := by
      dsimp [z] at hcast
      rw [hcast]
      abel
    have hend : x + n • OAI.Anderson.torusBasisVector i = Function.update x i (y i) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [OAI.Anderson.torusBasisVector, hcoord]
      · simp [OAI.Anderson.torusBasisVector, hk]
    obtain ⟨p, hp⟩ := torus_plus_walk hm i x n
    let p' := p.copy rfl hend
    have hp' : p'.length = n := by simpa [p'] using hp
    have hnabs : n = z.valMinAbs.natAbs := by
      exact_mod_cast hnZ.trans (Int.natAbs_of_nonneg hnonneg).symm
    exact ⟨p', by rw [hp', hnabs]⟩
  · have hneg : z.valMinAbs < 0 := lt_of_not_ge hnonneg
    let n := (-z.valMinAbs).toNat
    have hnZ : (n : ℤ) = -z.valMinAbs := Int.toNat_of_nonneg (by omega)
    have hcast : (n : ZMod (OAI.Anderson.sideLength m)) = -z := by
      calc
        (n : ZMod (OAI.Anderson.sideLength m)) = ((n : ℤ) : ZMod (OAI.Anderson.sideLength m)) := by norm_cast
        _ = (-z.valMinAbs : ℤ) := by rw [hnZ]
        _ = -(z.valMinAbs : ZMod (OAI.Anderson.sideLength m)) := by norm_cast
        _ = -z := by rw [ZMod.coe_valMinAbs]
    have hcoord : x i - (n : ZMod (OAI.Anderson.sideLength m)) = y i := by
      dsimp [z] at hcast
      rw [hcast]
      abel
    have hend : x - n • OAI.Anderson.torusBasisVector i = Function.update x i (y i) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [OAI.Anderson.torusBasisVector, hcoord]
      · simp [OAI.Anderson.torusBasisVector, hk]
    obtain ⟨p, hp⟩ := torus_minus_walk hm i x n
    let p' := p.copy rfl hend
    have hp' : p'.length = n := by simpa [p'] using hp
    have hnabs : n = z.valMinAbs.natAbs := by
      have hnonpos : z.valMinAbs ≤ 0 := le_of_lt hneg
      exact_mod_cast hnZ.trans (Int.ofNat_natAbs_of_nonpos hnonpos).symm
    exact ⟨p', by rw [hp', hnabs]⟩

private lemma torus_coord_dist_le {d m : ℕ} (hm : 0 < m) (x y : Torus d m) (i : Fin d) :
    (nnGraph d m).dist x (Function.update x i (y i)) ≤
      (y i - x i).valMinAbs.natAbs := by
  obtain ⟨p, hp⟩ := torus_coord_walk hm x y i
  calc
    (nnGraph d m).dist x (Function.update x i (y i)) ≤ p.length := SimpleGraph.dist_le p
    _ = (y i - x i).valMinAbs.natAbs := hp

private def updateOn {d m : ℕ} (x y : Torus d m) (s : Finset (Fin d)) : Torus d m :=
  fun i => if i ∈ s then y i else x i

private lemma torus_update_walk {d m : ℕ} (hm : 0 < m) :
    ∀ (s : Finset (Fin d)) (x y : Torus d m),
      ∃ p : (nnGraph d m).Walk x (updateOn x y s), True := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
      intro x y
      have hxy : x = updateOn x y ∅ := by
        funext i
        simp [updateOn]
      exact ⟨(SimpleGraph.Walk.nil : (nnGraph d m).Walk x x).copy rfl hxy, trivial⟩
  | @insert i s hi ih =>
      intro x y
      let x' : Torus d m := Function.update x i (y i)
      obtain ⟨p₁, _⟩ := torus_coord_walk hm x y i
      obtain ⟨p₂, _⟩ := ih x' y
      have htarget : updateOn x' y s = updateOn x y (insert i s) := by
        funext k
        by_cases hki : k = i
        · subst k
          simp [updateOn, x', hi]
        · simp [updateOn, x', hki]
      let p₂' := p₂.copy rfl htarget
      exact ⟨p₁.append p₂', trivial⟩

private lemma nnGraph_connected_of_pos {d m : ℕ} (hm : 0 < m) :
    (nnGraph d m).Connected := by
  refine { preconnected := ?_, nonempty := ⟨(0 : Torus d m)⟩ }
  intro x y
  obtain ⟨p, _⟩ := torus_update_walk hm Finset.univ x y
  have hxy : updateOn x y Finset.univ = y := by
    funext i
    simp [updateOn]
  exact (p.copy rfl hxy).reachable

private lemma torus_dist_le_coordinate_sum {d m : ℕ} (hm : 0 < m) (x y : Torus d m) :
    (nnGraph d m).dist x y ≤ ∑ i : Fin d, (y i - x i).valMinAbs.natAbs := by
  classical
  let w : Fin d → ℕ := fun i => (y i - x i).valMinAbs.natAbs
  have hconn := nnGraph_connected_of_pos (d := d) hm
  have haux : ∀ s : Finset (Fin d),
      (nnGraph d m).dist x (updateOn x y s) ≤ ∑ i ∈ s, w i := by
    intro s
    induction s using Finset.induction with
    | empty =>
        have hxx : updateOn x y ∅ = x := by
          funext i
          simp [updateOn]
        simp [hxx]
    | @insert i s hi ih =>
        let x' : Torus d m := updateOn x y s
        have hxi : x' i = x i := by simp [x', updateOn, hi]
        have htarget : Function.update x' i (y i) = updateOn x y (insert i s) := by
          funext k
          by_cases hki : k = i
          · subst k
            simp [x', updateOn, hi]
          · simp [x', updateOn, hki]
        have hcoord0 := torus_coord_dist_le hm x' y i
        have hcoord : (nnGraph d m).dist x' (updateOn x y (insert i s)) ≤ w i := by
          simpa [htarget, hxi, w] using hcoord0
        calc
          (nnGraph d m).dist x (updateOn x y (insert i s)) ≤
              (nnGraph d m).dist x x' + (nnGraph d m).dist x' (updateOn x y (insert i s)) :=
            hconn.dist_triangle
          _ ≤ (∑ k ∈ s, w k) + w i := add_le_add ih hcoord
          _ = ∑ k ∈ insert i s, w k := by rw [Finset.sum_insert hi]; simp [add_comm]
  have hxy : updateOn x y Finset.univ = y := by
    funext i
    simp [updateOn]
  calc
    (nnGraph d m).dist x y = (nnGraph d m).dist x (updateOn x y Finset.univ) := by rw [hxy]
    _ ≤ ∑ i ∈ Finset.univ, w i := haux Finset.univ
    _ = ∑ i : Fin d, (y i - x i).valMinAbs.natAbs := by simp [w]

private lemma circDist_eq_natAbs {m : ℕ} (a : ZMod (OAI.Anderson.sideLength m)) :
    circDist m a = a.valMinAbs.natAbs := by
  unfold circDist
  exact (ZMod.valMinAbs_natAbs_eq_min a).symm

private lemma circDist_zero (m : ℕ) : circDist m (0 : ZMod (OAI.Anderson.sideLength m)) = 0 := by
  simp [circDist]

private lemma circDist_neg {m : ℕ} (a : ZMod (OAI.Anderson.sideLength m)) :
    circDist m (-a) = circDist m a := by
  rw [circDist_eq_natAbs, circDist_eq_natAbs]
  exact ZMod.natAbs_valMinAbs_neg a

private lemma circDist_add_le {m : ℕ} (a b : ZMod (OAI.Anderson.sideLength m)) :
    circDist m (a + b) ≤ circDist m a + circDist m b := by
  rw [circDist_eq_natAbs, circDist_eq_natAbs, circDist_eq_natAbs]
  calc
    (a + b).valMinAbs.natAbs ≤ (a.valMinAbs + b.valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le a b
    _ ≤ a.valMinAbs.natAbs + b.valMinAbs.natAbs := Int.natAbs_add_le _ _

private lemma l1Dist_triangle {d m : ℕ} (x y z : Torus d m) :
    l1Dist x z ≤ l1Dist x y + l1Dist y z := by
  have hcoord (i : Fin d) :
      circDist m (z i - x i) ≤ circDist m (y i - x i) + circDist m (z i - y i) := by
    have heq : z i - x i = (z i - y i) + (y i - x i) := by abel
    rw [heq]
    simpa [add_comm] using circDist_add_le (z i - y i) (y i - x i)
  calc
    l1Dist x z ≤ ∑ i, (circDist m (y i - x i) + circDist m (z i - y i)) :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = l1Dist x y + l1Dist y z := by simp [l1Dist, Finset.sum_add_distrib, add_comm]

private lemma circDist_one_le (m : ℕ) : circDist m (1 : ZMod (OAI.Anderson.sideLength m)) ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    simp [circDist, OAI.Anderson.sideLength]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hlen : 2 ≤ OAI.Anderson.sideLength m := by
      rw [OAI.Anderson.sideLength]
      have hexp : 0 < 20 * m := by omega
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hexp.ne'
      rw [hn, pow_succ]
      have hpow : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by omega)
      omega
    letI : Fact (1 < OAI.Anderson.sideLength m) := ⟨by omega⟩
    unfold circDist
    rw [ZMod.val_one]
    exact Nat.min_le_left 1 _

private lemma l1Dist_symm {d m : ℕ} (x y : Torus d m) : l1Dist x y = l1Dist y x := by
  simp only [l1Dist]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show x i - y i = -(y i - x i) by abel, circDist_neg]

private lemma l1Dist_neighbor_le_one {d m : ℕ} {x y : Torus d m} (i : Fin d)
    (hxy : y = x + OAI.Anderson.torusBasisVector i ∨
      y = x - OAI.Anderson.torusBasisVector i) : l1Dist x y ≤ 1 := by
  rcases hxy with hxy | hxy
  · have hcoord (k : Fin d) :
        circDist m (y k - x k) ≤ if k = i then 1 else 0 := by
      by_cases hk : k = i
      · subst k
        simpa [hxy, OAI.Anderson.torusBasisVector] using circDist_one_le m
      · simp [hxy, OAI.Anderson.torusBasisVector, hk, circDist_zero]
    calc
      l1Dist x y ≤ ∑ k, (if k = i then 1 else 0) :=
        Finset.sum_le_sum fun k _ => hcoord k
      _ = 1 := by simp
  · have hcoord (k : Fin d) :
        circDist m (y k - x k) ≤ if k = i then 1 else 0 := by
      by_cases hk : k = i
      · subst k
        have hneg : circDist m (-1 : ZMod (OAI.Anderson.sideLength m)) =
            circDist m (1 : ZMod (OAI.Anderson.sideLength m)) :=
          circDist_neg (1 : ZMod (OAI.Anderson.sideLength m))
        simpa [hxy, OAI.Anderson.torusBasisVector, hneg] using circDist_one_le m
      · simp [hxy, OAI.Anderson.torusBasisVector, hk, circDist_zero]
    calc
      l1Dist x y ≤ ∑ k, (if k = i then 1 else 0) :=
        Finset.sum_le_sum fun k _ => hcoord k
      _ = 1 := by simp

private lemma l1Dist_adj_le_one {d m : ℕ} {x y : Torus d m}
    (hxy : (nnGraph d m).Adj x y) : l1Dist x y ≤ 1 := by
  rw [nnGraph, SimpleGraph.fromRel_adj] at hxy
  rcases hxy with ⟨_, hxy | hyx⟩
  · obtain ⟨i, hxy | hxy⟩ := hxy
    · exact l1Dist_neighbor_le_one i (Or.inl hxy)
    · exact l1Dist_neighbor_le_one i (Or.inr hxy)
  · obtain ⟨i, hyx | hyx⟩ := hyx
    · have hxy : y = x - OAI.Anderson.torusBasisVector i := by
        rw [hyx]
        abel
      exact l1Dist_neighbor_le_one i (Or.inr hxy)
    · have hxy : y = x + OAI.Anderson.torusBasisVector i := by
        rw [hyx]
        abel
      exact l1Dist_neighbor_le_one i (Or.inl hxy)

private lemma l1Dist_le_walk {d m : ℕ} {x y : Torus d m} :
    ∀ p : (nnGraph d m).Walk x y, l1Dist x y ≤ p.length := by
  intro p
  induction p with
  | nil => simp [l1Dist, circDist_zero]
  | @cons a b c hab p ih =>
      calc
        l1Dist a c ≤ l1Dist a b + l1Dist b c := l1Dist_triangle a b c
        _ ≤ 1 + p.length := add_le_add (l1Dist_adj_le_one hab) ih
        _ = (SimpleGraph.Walk.cons hab p).length := by simp [Nat.add_comm]

private lemma l1Dist_le_dist {d m : ℕ} (hconn : (nnGraph d m).Connected)
    (x y : Torus d m) : l1Dist x y ≤ (nnGraph d m).dist x y := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  simpa [hp] using l1Dist_le_walk p

theorem torusConnected_proof : TorusConnectedStatement := by
  intro d m
  by_cases hm : m = 0
  · subst m
    have hcard : Fintype.card (Torus d 0) = 1 := by
      rw [OAI.Anderson.torus_card]
      simp [OAI.Anderson.sideLength]
    obtain ⟨x₀, hx₀⟩ := Fintype.card_eq_one_iff.mp hcard
    refine { preconnected := ?_, nonempty := ⟨x₀⟩ }
    intro x y
    have hx : x = x₀ := hx₀ x
    have hy : y = x₀ := hx₀ y
    subst y
    subst x
    exact (SimpleGraph.Walk.nil : (nnGraph d 0).Walk x₀ x₀).reachable
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    exact nnGraph_connected_of_pos hmpos

theorem torusMetric_proof : TorusMetricStatement := by
  intro d m x y
  by_cases hm : m = 0
  · subst m
    have hcard : Fintype.card (Torus d 0) = 1 := by
      rw [OAI.Anderson.torus_card]
      simp [OAI.Anderson.sideLength]
    obtain ⟨x₀, hx₀⟩ := Fintype.card_eq_one_iff.mp hcard
    have hxy : x = y := (hx₀ x).trans (hx₀ y).symm
    subst y
    simp [physicalDistance, l1Dist, circDist_zero]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hconn := nnGraph_connected_of_pos (d := d) hmpos
    have hupper : (nnGraph d m).dist x y ≤ l1Dist x y := by
      have h := torus_dist_le_coordinate_sum hmpos x y
      have hsum : (∑ i : Fin d, (y i - x i).valMinAbs.natAbs) = l1Dist x y := by
        simp [l1Dist, circDist_eq_natAbs]
      rw [hsum] at h
      exact h
    have hlower := l1Dist_le_dist hconn x y
    unfold physicalDistance
    exact_mod_cast Nat.le_antisymm hupper hlower

end AndersonAC.AgentS78
