import AndersonAC.S78.Definitions
import AndersonAC.S78Moment.Geometry

/-!
# Lattice counts for the physical distance

The graph distance of the torus is the ℓ¹ distance of the centred (`valMinAbs`) coordinate
differences. Hence the sphere of radius `n` has at most `2^d (1+n)^{d-1}` points and the ball of
radius `L` at most `2^d (1+L)^d` (the `shells`/`volume` fields of `S6.TrialLocalInput`).

The walk constructions below (upper bound) are copied from the private lemmas of
`AndersonAC/S78Geom/Geometry.lean` (same project).
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Geo

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
    exact (one_ne_zero h10)
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

private lemma torus_dist_le_minus {d m : ℕ} (hm : 0 < m) (i : Fin d)
    (x : Torus d m) (n : ℕ) :
    (nnGraph d m).dist x (x - n • OAI.Anderson.torusBasisVector i) ≤ n := by
  obtain ⟨p, hp⟩ := torus_minus_walk hm i x n
  calc
    (nnGraph d m).dist x (x - n • OAI.Anderson.torusBasisVector i) ≤ p.length :=
      SimpleGraph.dist_le p
    _ = n := hp

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

private lemma nnGraph_connected {d m : ℕ} (hm : 0 < m) :
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
  have hconn := nnGraph_connected (d := d) hm
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

private abbrev IntBox (r : ℕ) := {z : ℤ // z ∈ Set.Icc (-(r : ℤ)) (r : ℤ)}

private lemma intBox_card (r : ℕ) : Fintype.card (IntBox r) = 2 * r + 1 := by
  have hcZ : (Fintype.card (IntBox r) : ℤ) = ((2 * r + 1 : ℕ) : ℤ) := by
    calc
      (Fintype.card (IntBox r) : ℤ) =
          (Fintype.card (Set.Icc (-(r : ℤ)) (r : ℤ)) : ℤ) := rfl
      _ = (r : ℤ) + 1 - (-(r : ℤ)) :=
        Int.card_fintype_Icc_of_le (a := -(r : ℤ)) (b := (r : ℤ)) (by omega)
      _ = ((2 * r + 1 : ℕ) : ℤ) := by push_cast; ring
  exact_mod_cast hcZ

/-- Centred coordinate distance. -/
def cyc {d m : ℕ} (x y : Torus d m) (i : Fin d) : ℕ := (y i - x i).valMinAbs.natAbs

theorem cyc_triangle {d m : ℕ} (x y z : Torus d m) (i : Fin d) :
    cyc x z i ≤ cyc x y i + cyc y z i := by
  have hsub : z i - x i = (z i - y i) + (y i - x i) := by abel
  rw [cyc, hsub]
  calc ((z i - y i + (y i - x i)).valMinAbs).natAbs
        ≤ ((z i - y i).valMinAbs + (y i - x i).valMinAbs).natAbs :=
          ZMod.natAbs_valMinAbs_add_le _ _
    _ ≤ (z i - y i).valMinAbs.natAbs + (y i - x i).valMinAbs.natAbs := Int.natAbs_add_le _ _
    _ = cyc x y i + cyc y z i := by simp [cyc, Nat.add_comm]

theorem zmod_one_natAbs_le {N : ℕ} [NeZero N] : ((1 : ZMod N).valMinAbs).natAbs ≤ 1 := by
  by_cases hN : 1 < N
  · have hh : 1 ≤ N / 2 := by omega
    have hv : (1 : ZMod N).valMinAbs = (1 : ℤ) := by
      simpa using ZMod.valMinAbs_natCast_of_le_half (n := N) (a := (1 : ℕ)) hh
    rw [hv]; norm_num
  · have hN1 : N = 1 := by have := NeZero.pos N; omega
    subst N
    have hz : (1 : ZMod 1) = 0 := Subsingleton.elim _ _
    rw [hz]; simp

theorem sum_basis_natAbs_le {d m : ℕ} (j : Fin d) (s : ZMod (OAI.Anderson.sideLength m))
    (hs : s = 1 ∨ s = -1) :
    ∑ i : Fin d, (((Pi.single j s : Torus d m) i).valMinAbs).natAbs ≤ 1 := by
  rw [Finset.sum_eq_single j]
  · rcases hs with rfl | rfl
    · simpa using zmod_one_natAbs_le (N := OAI.Anderson.sideLength m)
    · simpa [ZMod.natAbs_valMinAbs_neg] using zmod_one_natAbs_le (N := OAI.Anderson.sideLength m)
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem sum_cyc_adj_le_one {d m : ℕ} {x z : Torus d m} (h : (nnGraph d m).Adj x z) :
    ∑ i, cyc x z i ≤ 1 := by
  rcases (AndersonAC.SolS78.nnGraph_adj_iff_proof x z).mp h with ⟨_, j, hz | hz | hz | hz⟩
  · have : ∀ i, z i - x i = (Pi.single j (1 : ZMod _) : Torus d m) i := by
      intro i; rw [hz]; simp [OAI.Anderson.torusBasisVector]
    simpa [cyc, this] using sum_basis_natAbs_le (m := m) j 1 (Or.inl rfl)
  · have : ∀ i, z i - x i = (Pi.single j (-1 : ZMod _) : Torus d m) i := by
      intro i; rw [hz]; simp [OAI.Anderson.torusBasisVector, Pi.single_neg]
    simpa [cyc, this] using sum_basis_natAbs_le (m := m) j (-1) (Or.inr rfl)
  · have : ∀ i, z i - x i = (Pi.single j (-1 : ZMod _) : Torus d m) i := by
      intro i; rw [hz]; simp [OAI.Anderson.torusBasisVector, Pi.single_neg]
    simpa [cyc, this] using sum_basis_natAbs_le (m := m) j (-1) (Or.inr rfl)
  · have : ∀ i, z i - x i = (Pi.single j (1 : ZMod _) : Torus d m) i := by
      intro i; rw [hz]; simp [OAI.Anderson.torusBasisVector]
    simpa [cyc, this] using sum_basis_natAbs_le (m := m) j 1 (Or.inl rfl)

theorem sum_cyc_le_walk {d m : ℕ} {x y : Torus d m} (p : (nnGraph d m).Walk x y) :
    ∑ i, cyc x y i ≤ p.length := by
  induction p with
  | nil => simp [cyc]
  | @cons x z y hadj p ih =>
    rw [SimpleGraph.Walk.length_cons]
    calc ∑ i, cyc x y i ≤ ∑ i, (cyc x z i + cyc z y i) :=
          Finset.sum_le_sum fun i _ => cyc_triangle x z y i
      _ = ∑ i, cyc x z i + ∑ i, cyc z y i := Finset.sum_add_distrib
      _ ≤ 1 + p.length := add_le_add (sum_cyc_adj_le_one hadj) ih
      _ = p.length + 1 := by ring

theorem torus_dist_eq_sum {d m : ℕ} (hm : 0 < m) (x y : Torus d m) :
    (nnGraph d m).dist x y = ∑ i, cyc x y i := by
  apply le_antisymm (torus_dist_le_coordinate_sum hm x y)
  obtain ⟨p, hp⟩ := (nnGraph_connected hm).exists_walk_length_eq_dist x y
  rw [← hp]
  exact sum_cyc_le_walk p

theorem cyc_eq_iff {d m : ℕ} (x y y' : Torus d m) (i : Fin d)
    (h : (y i - x i).valMinAbs = (y' i - x i).valMinAbs) : y i = y' i := by
  have h' : y i - x i = y' i - x i := by
    rw [← ZMod.coe_valMinAbs (y i - x i), ← ZMod.coe_valMinAbs (y' i - x i), h]
  simpa using h'

/-- Sphere count: `|{y : dist(x,y) = n}| ≤ 2 (2n+1)^{d-1}`. -/
theorem shell_card_nat {d m : ℕ} (hm : 0 < m) (hd : 1 ≤ d) (x : Torus d m) (n : ℕ) :
    (Finset.univ.filter fun y : Torus d m => (nnGraph d m).dist x y = n).card ≤
      2 * (2 * n + 1) ^ (d - 1) := by
  classical
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  let v : Torus (d' + 1) m → Fin (d' + 1) → ℤ := fun y i => (y i - x i).valMinAbs
  have hsum : ∀ y, (nnGraph (d' + 1) m).dist x y = ∑ i, (v y i).natAbs := by
    intro y; rw [torus_dist_eq_sum hm]; rfl
  let S := {y : Torus (d' + 1) m // (nnGraph (d' + 1) m).dist x y = n}
  have hcoord : ∀ y : S, ∀ k : Fin d', v y.1 k.castSucc ∈ Set.Icc (-(n : ℤ)) (n : ℤ) := by
    intro y k
    have h1 : (v y.1 k.castSucc).natAbs ≤ n := by
      have e := y.2
      rw [hsum] at e
      have := Finset.single_le_sum (f := fun i => (v y.1 i).natAbs) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ k.castSucc)
      omega
    constructor <;> omega
  let f : S → (Fin d' → IntBox n) × Bool := fun y =>
    (fun k => ⟨v y.1 k.castSucc, hcoord y k⟩, decide (0 ≤ v y.1 (Fin.last d')))
  have hf : Function.Injective f := by
    intro y y' hyy
    simp only [f, Prod.mk.injEq, funext_iff, Subtype.mk.injEq, decide_eq_decide] at hyy
    obtain ⟨hk, hs⟩ := hyy
    have hlast : (v y.1 (Fin.last d')).natAbs = (v y'.1 (Fin.last d')).natAbs := by
      have e1 := y.2
      have e2 := y'.2
      rw [hsum, Fin.sum_univ_castSucc] at e1 e2
      have : ∑ i : Fin d', (v y.1 i.castSucc).natAbs = ∑ i : Fin d', (v y'.1 i.castSucc).natAbs :=
        Finset.sum_congr rfl fun k _ => by rw [hk k]
      omega
    have hl : v y.1 (Fin.last d') = v y'.1 (Fin.last d') := by
      rcases Int.natAbs_eq (v y.1 (Fin.last d')) with h1 | h1 <;>
      rcases Int.natAbs_eq (v y'.1 (Fin.last d')) with h2 | h2 <;> omega
    apply Subtype.ext
    funext i
    apply cyc_eq_iff x
    refine Fin.lastCases ?_ (fun k => ?_) i
    · exact hl
    · exact hk k
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, intBox_card, Fintype.card_fin]
    at hcard
  calc _ = Fintype.card S := by
          symm; apply Fintype.card_of_subtype; intro y; simp
    _ ≤ _ := hcard
    _ = _ := by ring

theorem shell_card {d m : ℕ} (hm : 0 < m) (hd : 1 ≤ d) (x : Torus d m) (n : ℕ) :
    ((Finset.univ.filter fun y : Torus d m =>
      (n : ℝ) ≤ physicalDistance d m x y ∧ physicalDistance d m x y < n + 1).card : ℝ) ≤
      2 ^ d * (1 + (n : ℝ)) ^ (d - 1) := by
  have hset : (Finset.univ.filter fun y : Torus d m =>
      (n : ℝ) ≤ physicalDistance d m x y ∧ physicalDistance d m x y < n + 1) =
      Finset.univ.filter fun y : Torus d m => (nnGraph d m).dist x y = n := by
    apply Finset.filter_congr
    intro y _
    unfold physicalDistance
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : n ≤ (nnGraph d m).dist x y := by exact_mod_cast h1
      have h2' : (nnGraph d m).dist x y < n + 1 := by exact_mod_cast h2
      omega
    · intro h; rw [h]; constructor <;> push_cast <;> linarith
  rw [hset]
  have h := shell_card_nat hm hd x n
  have h' : ((Finset.univ.filter fun y : Torus d m => (nnGraph d m).dist x y = n).card : ℝ) ≤
      2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by exact_mod_cast h
  refine h'.trans ?_
  have hd' : d = (d - 1) + 1 := by omega
  calc 2 * (2 * (n : ℝ) + 1) ^ (d - 1) ≤ 2 * (2 * (1 + (n : ℝ))) ^ (d - 1) := by
        gcongr; linarith
    _ = 2 ^ ((d - 1) + 1) * (1 + (n : ℝ)) ^ (d - 1) := by rw [mul_pow, pow_succ]; ring
    _ = 2 ^ d * (1 + (n : ℝ)) ^ (d - 1) := by rw [← hd']

theorem ball_card {d m : ℕ} (x : Torus d m) (L : ℝ) (hL : 0 ≤ L) :
    ((Finset.univ.filter fun y : Torus d m => physicalDistance d m x y ≤ L).card : ℝ) ≤
      2 ^ d * (1 + L) ^ d := by
  have hset : (Finset.univ.filter fun y : Torus d m => physicalDistance d m x y ≤ L) =
      Finset.univ.filter fun y : Torus d m => (nnGraph d m).dist x y ≤ ⌊L⌋₊ := by
    apply Finset.filter_congr
    intro y _
    unfold physicalDistance
    exact (Nat.le_floor_iff hL).symm
  rw [hset]
  have h := AndersonAC.SolS78.graphBall_card_le x ⌊L⌋₊
  have h' : ((Finset.univ.filter fun y : Torus d m => (nnGraph d m).dist x y ≤ ⌊L⌋₊).card : ℝ) ≤
      (2 * (⌊L⌋₊ : ℝ) + 1) ^ d := by exact_mod_cast h
  refine h'.trans ?_
  have hfl : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL
  calc (2 * (⌊L⌋₊ : ℝ) + 1) ^ d ≤ (2 * (1 + L)) ^ d := by gcongr; linarith
    _ = 2 ^ d * (1 + L) ^ d := mul_pow _ _ _

end AndersonAC.AgentS78Geo
