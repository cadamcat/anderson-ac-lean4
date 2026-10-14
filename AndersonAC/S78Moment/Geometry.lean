import AndersonAC.S78.Definitions
import Mathlib.Data.ZMod.ValMinAbs

open scoped BigOperators

namespace AndersonAC.SolS78

open AndersonAC.S78

private abbrev basis {d m : ℕ} (i : Fin d) : Torus d m :=
  OAI.Anderson.torusBasisVector i

private theorem nnGraph_adj_iff {d m : ℕ} (x y : Torus d m) :
    (nnGraph d m).Adj x y ↔
      x ≠ y ∧ ∃ i : Fin d,
        y = x + basis i ∨ y = x - basis i ∨ x = y + basis i ∨ x = y - basis i := by
  rw [nnGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨i, h | h⟩
      · exact ⟨hne, i, Or.inl h⟩
      · exact ⟨hne, i, Or.inr (Or.inl h)⟩
    · rcases h with ⟨i, h | h⟩
      · exact ⟨hne, i, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨hne, i, Or.inr (Or.inr (Or.inr h))⟩
  · rintro ⟨hne, i, h | h | h | h⟩
    · exact ⟨hne, Or.inl ⟨i, Or.inl h⟩⟩
    · exact ⟨hne, Or.inl ⟨i, Or.inr h⟩⟩
    · exact ⟨hne, Or.inr ⟨i, Or.inl h⟩⟩
    · exact ⟨hne, Or.inr ⟨i, Or.inr h⟩⟩

private def shiftHom {d m : ℕ} (a : Torus d m) :
    nnGraph d m →g nnGraph d m where
  toFun x := x + a
  map_rel' := by
    intro x y h
    rcases (nnGraph_adj_iff x y).mp h with ⟨hne, i, h | h | h | h⟩
    · apply (nnGraph_adj_iff _ _).mpr
      refine ⟨?_, i, Or.inl ?_⟩
      · intro he
        exact hne (add_right_cancel he)
      · rw [h]
        abel
    · apply (nnGraph_adj_iff _ _).mpr
      refine ⟨?_, i, Or.inr (Or.inl ?_)⟩
      · intro he
        exact hne (add_right_cancel he)
      · rw [h]
        abel
    · apply (nnGraph_adj_iff _ _).mpr
      refine ⟨?_, i, Or.inr (Or.inr (Or.inl ?_))⟩
      · intro he
        exact hne (add_right_cancel he)
      · rw [h]
        abel
    · apply (nnGraph_adj_iff _ _).mpr
      refine ⟨?_, i, Or.inr (Or.inr (Or.inr ?_))⟩
      · intro he
        exact hne (add_right_cancel he)
      · rw [h]
        abel

private theorem reachable_shift {d m : ℕ} {x y : Torus d m} (a : Torus d m)
    (h : (nnGraph d m).Reachable x y) :
    (nnGraph d m).Reachable (x + a) (y + a) :=
  SimpleGraph.Reachable.map (shiftHom a) h

private theorem sideLength_gt_one {m : ℕ} (hm : 0 < m) :
    1 < OAI.Anderson.sideLength m := by
  rw [OAI.Anderson.sideLength]
  apply Nat.one_lt_pow
  · omega
  · decide

private theorem basis_ne_zero {d m : ℕ} (hm : 0 < m) (i : Fin d) :
    basis (d := d) (m := m) i ≠ (0 : Torus d m) := by
  intro h
  have hi := congrFun h i
  have hN := sideLength_gt_one hm
  have h1 : (1 : ZMod (OAI.Anderson.sideLength m)) ≠ 0 := by
    intro h
    have hv : (1 : ZMod (OAI.Anderson.sideLength m)).val = 0 :=
      (ZMod.val_eq_zero _).2 h
    have hv' : (1 : ZMod (OAI.Anderson.sideLength m)).val = 1 := by
      simp [ZMod.val_eq_one hN]
    omega
  apply h1
  simpa [basis, OAI.Anderson.torusBasisVector] using hi

private theorem basis_adj {d m : ℕ} (hm : 0 < m) (x : Torus d m) (i : Fin d) :
    (nnGraph d m).Adj x (x + basis i) := by
  apply (nnGraph_adj_iff _ _).mpr
  refine ⟨?_, i, Or.inl rfl⟩
  intro h
  have hb : basis (d := d) (m := m) i = (0 : Torus d m) := by
    have h' : x + basis (d := d) (m := m) i = x + 0 := by simpa using h.symm
    exact add_left_cancel h'
  exact basis_ne_zero hm i hb

private theorem basis_reachable {d m : ℕ} (hm : 0 < m) (i : Fin d) (n : ℕ) :
    (nnGraph d m).Reachable 0 (n • basis i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := reachable_shift (n • basis i)
        ((basis_adj hm (0 : Torus d m) i).reachable)
      have hs' : (nnGraph d m).Reachable (n • basis i)
          ((n • basis i) + basis i) := by simpa [add_comm] using hs
      have hsum := ih.trans hs'
      rw [succ_nsmul]
      simpa [add_comm] using hsum

private theorem torus_sum_basis {d m : ℕ} (x : Torus d m) :
    x = ∑ i : Fin d, (x i).val • basis i := by
  ext j
  simp [basis, OAI.Anderson.torusBasisVector, Finset.sum_apply, Pi.single_apply]
  change x j = (@ZMod.cast (Torus d m) _ (OAI.Anderson.sideLength m) (x j)) j
  rw [ZMod.cast_eq_val]
  change x j = ((x j).val : ZMod (OAI.Anderson.sideLength m))
  exact (ZMod.natCast_zmod_val (x j)).symm

private theorem zero_reachable {d m : ℕ} (hm : 0 < m) (x : Torus d m) :
    (nnGraph d m).Reachable 0 x := by
  rw [torus_sum_basis (d := d) (m := m) x]
  have hsum : ∀ s : Finset (Fin d),
      (nnGraph d m).Reachable 0 (∑ i ∈ s, (x i).val • basis i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his]
        exact reachable_add (basis_reachable hm i (x i).val) ih
  simpa using hsum Finset.univ
where
  reachable_add {d m : ℕ} {x y : Torus d m}
      (hx : (nnGraph d m).Reachable 0 x) (hy : (nnGraph d m).Reachable 0 y) :
      (nnGraph d m).Reachable 0 (x + y) := by
    have hshift := reachable_shift x hy
    have hshift' : (nnGraph d m).Reachable x (x + y) := by
      simpa [add_comm] using hshift
    exact hx.trans hshift'

private theorem nnGraph_connected {d m : ℕ} : (nnGraph d m).Connected := by
  by_cases hm : 0 < m
  · letI : Nonempty (Torus d m) := ⟨0⟩
    refine ⟨?_⟩
    intro x y
    have h := zero_reachable hm (y - x)
    have hs := reachable_shift x h
    have hs' : (nnGraph d m).Reachable x y := by
      have hx : (y - x) + x = y := by abel
      simpa [hx] using hs
    exact hs'
  · have hm0 : m = 0 := by omega
    subst m
    letI : Subsingleton (Torus d 0) := by
      dsimp [Torus, OAI.Anderson.Torus, OAI.Anderson.sideLength]
      infer_instance
    letI : Nonempty (Torus d 0) := ⟨0⟩
    refine ⟨?_⟩
    intro x y
    exact SimpleGraph.Reachable.of_subsingleton

private def cyclicCoordDistance {d m : ℕ} (x y : Torus d m) (i : Fin d) : ℕ :=
  ((y i - x i).valMinAbs).natAbs

private theorem cyclicCoordDistance_triangle {d m : ℕ} (x y z : Torus d m)
    (i : Fin d) :
    cyclicCoordDistance x z i ≤ cyclicCoordDistance x y i + cyclicCoordDistance y z i := by
  have hsub : z i - x i = (z i - y i) + (y i - x i) := by abel
  rw [cyclicCoordDistance, hsub]
  calc
    ((z i - y i + (y i - x i)).valMinAbs).natAbs ≤
        ((z i - y i).valMinAbs + (y i - x i).valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le _ _
    _ ≤ (z i - y i).valMinAbs.natAbs + (y i - x i).valMinAbs.natAbs :=
      Int.natAbs_add_le _ _
    _ = cyclicCoordDistance x y i + cyclicCoordDistance y z i := by
      simp [cyclicCoordDistance, Nat.add_comm]

private theorem zmod_one_cyclic_le_one {N : ℕ} [NeZero N] :
    ((1 : ZMod N).valMinAbs).natAbs ≤ 1 := by
  by_cases hN : 1 < N
  · have hh : 1 ≤ N / 2 := by omega
    have hv : (1 : ZMod N).valMinAbs = (1 : ℤ) := by
      simpa using ZMod.valMinAbs_natCast_of_le_half (n := N) (a := (1 : ℕ)) hh
    rw [hv]
    norm_num
  · have hN1 : N = 1 := by have := NeZero.pos N; omega
    subst N
    have hz : (1 : ZMod 1) = 0 := Subsingleton.elim _ _
    rw [hz]
    simp

private theorem coord_cyclic_plus {d m : ℕ} {x y : Torus d m}
    (j i : Fin d) (h : y = x + basis j) :
    cyclicCoordDistance x y i ≤ 1 := by
  by_cases hij : i = j
  · subst i
    simpa [cyclicCoordDistance, h, basis, OAI.Anderson.torusBasisVector,
      Pi.single_apply] using zmod_one_cyclic_le_one (N := OAI.Anderson.sideLength m)
  · simp [cyclicCoordDistance, h, basis, OAI.Anderson.torusBasisVector, hij]

private theorem coord_cyclic_minus {d m : ℕ} {x y : Torus d m}
    (j i : Fin d) (h : y = x - basis j) :
    cyclicCoordDistance x y i ≤ 1 := by
  by_cases hij : i = j
  · subst i
    simpa [cyclicCoordDistance, h, basis, OAI.Anderson.torusBasisVector,
      Pi.single_apply, ZMod.natAbs_valMinAbs_neg] using
      zmod_one_cyclic_le_one (N := OAI.Anderson.sideLength m)
  · simp [cyclicCoordDistance, h, basis, OAI.Anderson.torusBasisVector, hij]

private theorem adj_coord_cyclic_le_one {d m : ℕ} {x y : Torus d m}
    (h : (nnGraph d m).Adj x y) (i : Fin d) :
    cyclicCoordDistance x y i ≤ 1 := by
  rcases (nnGraph_adj_iff x y).mp h with ⟨_, j, hy | hy | hy | hy⟩
  · exact coord_cyclic_plus j i hy
  · exact coord_cyclic_minus j i hy
  · have hy' : y = x - basis j := by rw [hy]; abel
    exact coord_cyclic_minus j i hy'
  · have hy' : y = x + basis j := by rw [hy]; abel
    exact coord_cyclic_plus j i hy'

private theorem walk_coord_cyclic_le {d m : ℕ} {x y : Torus d m}
    (p : (nnGraph d m).Walk x y) (i : Fin d) :
    cyclicCoordDistance x y i ≤ p.length := by
  induction p with
  | nil => simp [cyclicCoordDistance]
  | @cons x z y hadj p ih =>
      have ht := cyclicCoordDistance_triangle x z y i
      have hs := adj_coord_cyclic_le_one hadj i
      rw [SimpleGraph.Walk.length_cons]
      omega

private theorem cyclicCoordDistance_le_dist {d m : ℕ}
    (x y : Torus d m) (i : Fin d) :
    cyclicCoordDistance x y i ≤ (nnGraph d m).dist x y := by
  obtain ⟨p, hp⟩ := (nnGraph_connected).exists_walk_length_eq_dist x y
  simpa [hp] using walk_coord_cyclic_le p i

theorem graphBall_card_le {d m : ℕ} (x : Torus d m) (r : ℕ) :
    (Finset.univ.filter fun y : Torus d m => (nnGraph d m).dist x y ≤ r).card ≤
      (2 * r + 1) ^ d := by
  classical
  let I := Set.Icc (-(r : ℤ)) (r : ℤ)
  let f : {y : Torus d m // (nnGraph d m).dist x y ≤ r} → (Fin d → I) := fun y i => by
    refine ⟨(y.1 i - x i).valMinAbs, ?_⟩
    have hc := cyclicCoordDistance_le_dist x y.1 i
    have hnat : ((y.1 i - x i).valMinAbs).natAbs ≤ r := by
      exact hc.trans y.2
    have hsq : ((y.1 i - x i).valMinAbs) ^ 2 ≤ (r : ℤ) ^ 2 := by
      have hnat' : ((y.1 i - x i).valMinAbs).natAbs ≤ (r : ℤ).natAbs := by
        exact_mod_cast hnat
      have hsq' := (Int.natAbs_le_iff_sq_le).mp hnat'
      simpa using hsq'
    constructor
    · nlinarith [sq_nonneg ((y.1 i - x i).valMinAbs + (r : ℤ))]
    · nlinarith [sq_nonneg ((y.1 i - x i).valMinAbs - (r : ℤ))]
  have hf : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    apply funext
    intro i
    have hi := congrArg (fun g : Fin d → I => ((g i : ℤ) : ZMod (OAI.Anderson.sideLength m))) h
    have hi' : y.1 i - x i = z.1 i - x i := by
      simpa [f, I, ZMod.coe_valMinAbs] using hi
    have hi'' := congrArg (fun a : ZMod (OAI.Anderson.sideLength m) => a + x i) hi'
    simpa using hi''
  have hcardI : Fintype.card I = 2 * r + 1 := by
    have hcardI' : (Fintype.card I : ℤ) = 2 * (r : ℤ) + 1 := by
      convert Int.card_fintype_Icc_of_le (a := -(r : ℤ)) (b := (r : ℤ)) (by omega) using 1 <;> ring
    exact_mod_cast hcardI'
  calc
    _ = Fintype.card {y : Torus d m // (nnGraph d m).dist x y ≤ r} := by
      symm
      apply Fintype.card_of_subtype
      intro y
      simp
    _ ≤ Fintype.card (Fin d → I) := Fintype.card_le_of_injective f hf
    _ = (2 * r + 1) ^ d := by rw [Fintype.card_pi]; simp [hcardI]

theorem nnGraph_connected_proof {d m : ℕ} : (nnGraph d m).Connected :=
  nnGraph_connected

theorem nnGraph_adj_iff_proof {d m : ℕ} (x y : Torus d m) :
    (nnGraph d m).Adj x y ↔
      x ≠ y ∧ ∃ i : Fin d,
        y = x + OAI.Anderson.torusBasisVector i ∨
        y = x - OAI.Anderson.torusBasisVector i ∨
        x = y + OAI.Anderson.torusBasisVector i ∨
        x = y - OAI.Anderson.torusBasisVector i := by
  simpa [basis] using nnGraph_adj_iff x y

def nnGraph_shiftHom {d m : ℕ} (a : Torus d m) :
    nnGraph d m →g nnGraph d m := shiftHom a

theorem sideLength_gt_two {m : ℕ} (hm : 0 < m) :
    2 < OAI.Anderson.sideLength m := by
  rw [OAI.Anderson.sideLength]
  have hpow : ∀ n : ℕ, 0 < n → 2 < 4 ^ n := by
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
        have hbase : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by norm_num)
        rw [pow_succ]
        nlinarith
  apply hpow
  omega

end AndersonAC.SolS78
