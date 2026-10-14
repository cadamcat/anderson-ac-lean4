import AndersonAC.S78.Definitions
import AndersonAC.S78Moment.Geometry

open scoped BigOperators

namespace AndersonAC.SolS78

open AndersonAC.S78

private theorem list_sum_square_bound (l : List ℝ) :
    l.sum ^ 2 ≤ (l.length : ℝ) * (l.map fun a => a ^ 2).sum := by
  have h := Multiset.sq_sum_le_card_mul_sum_sq (Multiset.ofList l)
  simpa using h

private theorem list_map_square_bound {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum ^ 2 ≤ (l.length : ℝ) * (l.map fun a => (f a) ^ 2).sum := by
  have h := list_sum_square_bound (l.map f)
  have hmap : (l.map f).map (fun a => a ^ 2) = l.map (fun a => (f a) ^ 2) := by
    simp
  simpa [List.length_map, hmap] using h

private theorem list_sum_bound {α : Type*} (l : List α) (f : α → ℝ) (B : ℝ)
    (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ (l.length : ℝ) * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ha := h a (by simp)
      have ht := ih (by intro b hb; exact h b (by simp [hb]))
      push_cast
      linarith

private theorem finset_list_sum_comm {α β : Type*} [Fintype α] (s : Finset α)
    (l : List β) (f : α → β → ℝ) :
    (∑ a ∈ s, (l.map fun b => f a b).sum) =
      (l.map fun b => ∑ a ∈ s, f a b).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [ih]

private theorem walk_shift_sum {d m : ℕ} {x y : Torus d m}
    (p : (nnGraph d m).Walk x y) (v : Torus d m → ℝ) (s : Torus d m) :
    (p.darts.map fun e => v (s + e.snd) - v (s + e.fst)).sum =
      v (s + y) - v (s + x) := by
  induction p with
  | nil => simp
  | @cons x z y h p ih =>
      simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

private abbrev torusBasis {d m : ℕ} (i : Fin d) : Torus d m :=
  OAI.Anderson.torusBasisVector i

private theorem zmod_one_ne_neg_one {N : ℕ} [NeZero N] (hN : 2 < N) :
    (1 : ZMod N) ≠ -1 := by
  intro h
  have hsum : (1 : ZMod N) + 1 = 0 := by
    calc
      (1 : ZMod N) + 1 = 1 - (-1) := by ring
      _ = 1 - 1 := by rw [← h]
      _ = 0 := by ring
  have htwo : (2 : ZMod N) = 0 := by
    have hcast : (1 : ZMod N) + 1 = 2 := by norm_num
    exact hcast.symm.trans hsum
  have hval0 : (2 : ZMod N).val = 0 := (ZMod.val_eq_zero _).2 htwo
  have hval : (2 : ZMod N).val = 2 := ZMod.val_cast_of_lt hN
  omega

private theorem torusBasis_ne_neg {d m : ℕ} (hm : 0 < m) (i : Fin d) :
    torusBasis (d := d) (m := m) i ≠ -torusBasis (d := d) (m := m) i := by
  intro h
  have hi := congrFun h i
  have h1 : (1 : ZMod (OAI.Anderson.sideLength m)) = -1 := by
    simpa [torusBasis, OAI.Anderson.torusBasisVector, Pi.single_apply] using hi
  exact zmod_one_ne_neg_one (AndersonAC.SolS78.sideLength_gt_two hm) h1

private theorem adjacent_difference_ne_neg {d m : ℕ} {a b : Torus d m}
    (h : (nnGraph d m).Adj a b) : b - a ≠ -(b - a) := by
  have hne : a ≠ b := (AndersonAC.SolS78.nnGraph_adj_iff_proof a b).mp h |>.1
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    subst m
    letI : Subsingleton (Torus d 0) := by
      dsimp [Torus, OAI.Anderson.Torus, OAI.Anderson.sideLength]
      infer_instance
    exact hne (Subsingleton.elim a b)
  rcases (AndersonAC.SolS78.nnGraph_adj_iff_proof a b).mp h with
      ⟨_, i, h₁ | h₂ | h₃ | h₄⟩
  · have hd : b - a = torusBasis i := by rw [h₁]; abel
    intro heq
    exact torusBasis_ne_neg hm i (by simpa [hd] using heq)
  · have hd : b - a = -torusBasis (d := d) (m := m) i := by rw [h₂]; abel
    intro heq
    have heq' : -torusBasis (d := d) (m := m) i = torusBasis (d := d) (m := m) i := by
      simpa [hd] using heq
    exact torusBasis_ne_neg hm i heq'.symm
  · have hd : b - a = -torusBasis (d := d) (m := m) i := by rw [h₃]; abel
    intro heq
    have heq' : -torusBasis (d := d) (m := m) i = torusBasis (d := d) (m := m) i := by
      simpa [hd] using heq
    exact torusBasis_ne_neg hm i heq'.symm
  · have hd : b - a = torusBasis i := by rw [h₄]; abel
    intro heq
    exact torusBasis_ne_neg hm i (by simpa [hd] using heq)

private theorem edge_orbit_sum_le {d m : ℕ} (a b : Torus d m)
    (h : (nnGraph d m).Adj a b) (v : Torus d m → ℝ) :
    (∑ i : Torus d m, (v (i + a) - v (i + b)) ^ 2) ≤
      gradientEnergy (nnGraph d m) v := by
  classical
  let forward : Torus d m → Torus d m × Torus d m := fun i => (i + a, i + b)
  let backward : Torus d m → Torus d m × Torus d m := fun i => (i + b, i + a)
  let P : Finset (Torus d m × Torus d m) := Finset.univ.image forward
  let Q : Finset (Torus d m × Torus d m) := Finset.univ.image backward
  let U : Finset (Torus d m × Torus d m) := Finset.univ.product Finset.univ
  let E : Finset (Torus d m × Torus d m) := U.filter fun z => (nnGraph d m).Adj z.1 z.2
  let F : Torus d m × Torus d m → ℝ := fun z => (v z.1 - v z.2) ^ 2
  have hforward : Function.Injective forward := by
    intro i j hij
    exact add_right_cancel (congrArg Prod.fst hij)
  have hbackward : Function.Injective backward := by
    intro i j hij
    exact add_right_cancel (congrArg Prod.fst hij)
  have hdisjoint : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro z hzP hzQ
    rcases Finset.mem_image.mp hzP with ⟨i, -, rfl⟩
    rcases Finset.mem_image.mp hzQ with ⟨j, -, hEq⟩
    have hfst := congrArg Prod.fst hEq
    have hsnd := congrArg Prod.snd hEq
    change j + b = i + a at hfst
    change j + a = i + b at hsnd
    have hdelta : b - a = a - b := by
      calc
        b - a = (j + b) - (j + a) := by abel
        _ = (i + a) - (i + b) := by rw [hfst, hsnd]
        _ = a - b := by abel
    have hturn : b - a = -(b - a) := by simpa using hdelta
    exact (adjacent_difference_ne_neg h) hturn
  have hPadj (i : Torus d m) : (nnGraph d m).Adj (i + a) (i + b) := by
    have hh := (AndersonAC.SolS78.nnGraph_shiftHom i).map_rel' h
    have hh' : (nnGraph d m).Adj (a + i) (b + i) := by
      change (nnGraph d m).Adj (a + i) (b + i) at hh
      exact hh
    simpa [add_comm] using hh'
  have hsubset : P ∪ Q ⊆ E := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_image.mp hz with ⟨i, -, rfl⟩
      simp only [E, Finset.mem_filter]
      constructor
      · simp [U, forward]
      · simpa [forward] using hPadj i
    · rcases Finset.mem_image.mp hz with ⟨i, -, rfl⟩
      simp only [E, Finset.mem_filter]
      constructor
      · simp [U, backward]
      · simpa [backward] using (hPadj i).symm
  have hPsum : (∑ z ∈ P, F z) = ∑ i : Torus d m, (v (i + a) - v (i + b)) ^ 2 := by
    change (∑ z ∈ Finset.univ.image forward, F z) =
      ∑ i ∈ Finset.univ, F (forward i)
    exact Finset.sum_image (f := F) (fun i _ j _ hij => hforward hij)
  have hQsum : (∑ z ∈ Q, F z) = ∑ i : Torus d m, (v (i + a) - v (i + b)) ^ 2 := by
    calc
      (∑ z ∈ Q, F z) = ∑ i ∈ Finset.univ, F (backward i) := by
        change (∑ z ∈ Finset.univ.image backward, F z) =
          ∑ i ∈ Finset.univ, F (backward i)
        exact Finset.sum_image (f := F) (fun i _ j _ hij => hbackward hij)
      _ = ∑ i : Torus d m, (v (i + b) - v (i + a)) ^ 2 := by
        simp [F, backward]
      _ = ∑ i : Torus d m, (v (i + a) - v (i + b)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hUnionsum : (∑ z ∈ P ∪ Q, F z) =
      2 * ∑ i : Torus d m, (v (i + a) - v (i + b)) ^ 2 := by
    rw [Finset.sum_union hdisjoint, hPsum, hQsum]
    ring
  have hEnergy : (∑ z ∈ E, F z) = 2 * gradientEnergy (nnGraph d m) v := by
    calc
      _ = ∑ z ∈ U, if (nnGraph d m).Adj z.1 z.2 then F z else 0 := by
        simp [E, U, Finset.sum_filter]
      _ = ∑ i, ∑ j, if (nnGraph d m).Adj i j then (v i - v j) ^ 2 else 0 := by
        change (∑ z ∈ Finset.univ ×ˢ Finset.univ,
          if (nnGraph d m).Adj z.1 z.2 then (v z.1 - v z.2) ^ 2 else 0) = _
        rw [Finset.sum_product]
      _ = 2 * gradientEnergy (nnGraph d m) v := by
        rw [gradientEnergy]
        ring
  have hsumSubset : (∑ z ∈ P ∪ Q, F z) ≤ ∑ z ∈ E, F z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro z hz
    intro hnot
    exact sq_nonneg _
  rw [hUnionsum, hEnergy] at hsumSubset
  nlinarith

theorem translation_energy_proof (d m : ℕ) (v : Torus d m → ℝ) (u : Torus d m) :
    (∑ i, (v (i + u) - v i) ^ 2) ≤
      physicalDistance d m 0 u ^ 2 * gradientEnergy (nnGraph d m) v := by
  classical
  obtain ⟨p, hp⟩ := AndersonAC.SolS78.nnGraph_connected_proof.exists_walk_length_eq_dist
    (0 : Torus d m) u
  have hcs (i : Torus d m) :
      (v (i + u) - v i) ^ 2 ≤ (p.length : ℝ) *
        (p.darts.map fun e => (v (i + e.snd) - v (i + e.fst)) ^ 2).sum := by
    have hlist := list_map_square_bound p.darts
      (fun e => v (i + e.snd) - v (i + e.fst))
    simpa [walk_shift_sum, SimpleGraph.Walk.length_darts] using hlist
  have hsumCS :
      (∑ i, (v (i + u) - v i) ^ 2) ≤ (p.length : ℝ) *
        (p.darts.map fun e => ∑ i, (v (i + e.snd) - v (i + e.fst)) ^ 2).sum := by
    calc
      _ ≤ ∑ i, (p.length : ℝ) *
          (p.darts.map fun e => (v (i + e.snd) - v (i + e.fst)) ^ 2).sum :=
            Finset.sum_le_sum fun i _ => hcs i
      _ = (p.length : ℝ) *
          (∑ i, (p.darts.map fun e => (v (i + e.snd) - v (i + e.fst)) ^ 2).sum) := by
            rw [Finset.mul_sum]
      _ = (p.length : ℝ) *
          (p.darts.map fun e => ∑ i, (v (i + e.snd) - v (i + e.fst)) ^ 2).sum := by
            congr 1
            simpa using finset_list_sum_comm Finset.univ p.darts
              (fun i e => (v (i + e.snd) - v (i + e.fst)) ^ 2)
  let E := gradientEnergy (nnGraph d m) v
  have hlist :
      (p.darts.map fun e => ∑ i, (v (i + e.snd) - v (i + e.fst)) ^ 2).sum ≤
        (p.darts.length : ℝ) * E := by
    apply list_sum_bound p.darts (fun e => ∑ i, (v (i + e.snd) - v (i + e.fst)) ^ 2) E
    intro e he
    exact edge_orbit_sum_le e.snd e.fst e.adj.symm v
  have hbound :
      (∑ i, (v (i + u) - v i) ^ 2) ≤
        (p.length : ℝ) * ((p.length : ℝ) * E) := by
    calc
      _ ≤ (p.length : ℝ) *
          (p.darts.map fun e => ∑ i, (v (i + e.snd) - v (i + e.fst)) ^ 2).sum := hsumCS
      _ ≤ (p.length : ℝ) * ((p.darts.length : ℝ) * E) :=
            mul_le_mul_of_nonneg_left hlist (Nat.cast_nonneg _)
      _ = _ := by simp [SimpleGraph.Walk.length_darts]
  have hdist : physicalDistance d m 0 u = (p.length : ℝ) := by
    unfold physicalDistance
    exact_mod_cast hp.symm
  calc
    (∑ i, (v (i + u) - v i) ^ 2) ≤ (p.length : ℝ) ^ 2 * gradientEnergy (nnGraph d m) v := by
      calc
        _ ≤ (p.length : ℝ) * ((p.length : ℝ) * E) := hbound
        _ = (p.length : ℝ) ^ 2 * gradientEnergy (nnGraph d m) v := by
          dsimp [E]
          rw [pow_two]
          ring
    _ = physicalDistance d m 0 u ^ 2 * gradientEnergy (nnGraph d m) v := by rw [← hdist]

end AndersonAC.SolS78
