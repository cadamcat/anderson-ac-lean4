import AndersonAC.S78.Definitions
import AndersonAC.S78Metric.Metric

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

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

private lemma cube_coord_bound {d m : ℕ} (x z : Torus d m) (R : ℝ)
    (hx : x ∈ cube d m z R) (i : Fin d) :
    ((x i - z i).valMinAbs.natAbs : ℝ) ≤ R := by
  have hbox : ∀ i : Fin d,
      ((min ((x i - z i).val) (OAI.Anderson.sideLength m - (x i - z i).val) : ℕ) : ℝ) ≤ R := by
    simpa [cube] using hx
  calc
    ((x i - z i).valMinAbs.natAbs : ℝ) =
        ((min ((x i - z i).val) (OAI.Anderson.sideLength m - (x i - z i).val) : ℕ) : ℝ) := by
          rw [ZMod.valMinAbs_natAbs_eq_min]
    _ ≤ R := hbox i

private lemma cube_mem_symm {d m : ℕ} (x z : Torus d m) (R : ℝ)
    (hx : x ∈ cube d m z R) : z ∈ cube d m x R := by
  have hcoord (i : Fin d) :
      ((z i - x i).valMinAbs.natAbs : ℝ) ≤ R := by
    have hneg : (z i - x i).valMinAbs.natAbs = (x i - z i).valMinAbs.natAbs := by
      rw [show z i - x i = -(x i - z i) by abel]
      exact ZMod.natAbs_valMinAbs_neg _
    calc
      ((z i - x i).valMinAbs.natAbs : ℝ) = (x i - z i).valMinAbs.natAbs := by exact_mod_cast hneg
      _ ≤ R := cube_coord_bound x z R hx i
  have hbox : ∀ i : Fin d,
      ((min ((z i - x i).val) (OAI.Anderson.sideLength m - (z i - x i).val) : ℕ) : ℝ) ≤ R := by
    intro i
    rw [← ZMod.valMinAbs_natAbs_eq_min]
    exact hcoord i
  simpa [cube] using hbox

private lemma cube_card_upper {d m : ℕ} (z : Torus d m) (R : ℝ) :
    (cube d m z R).card ≤ (2 * ⌊R⌋₊ + 1) ^ d := by
  classical
  let r : ℕ := ⌊R⌋₊
  let f : {x : Torus d m // x ∈ cube d m z R} → (Fin d → IntBox r) := fun x i => by
    have hR := cube_coord_bound x.val z R x.property i
    have hnat : (x.val i - z i).valMinAbs.natAbs ≤ r := by
      exact Nat.le_floor hR
    have hreal : |((x.val i - z i).valMinAbs : ℝ)| ≤ (r : ℝ) := by
      have hcast : ((x.val i - z i).valMinAbs.natAbs : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast hnat
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact hcast
    have hmem : (x.val i - z i).valMinAbs ∈ Set.Icc (-(r : ℤ)) (r : ℤ) := by
      rw [Set.mem_Icc]
      constructor
      · exact_mod_cast (abs_le.mp hreal).1
      · exact_mod_cast (abs_le.mp hreal).2
    exact ⟨(x.val i - z i).valMinAbs, hmem⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    have hi : (a.val i - z i).valMinAbs = (b.val i - z i).valMinAbs := by
      have hv := congrArg Subtype.val (congrFun hab i)
      exact hv
    have hsub : a.val i - z i = b.val i - z i := ZMod.valMinAbs_inj.mp hi
    have hsum := congrArg (fun w : ZMod (OAI.Anderson.sideLength m) => w + z i) hsub
    simpa using hsum
  calc
    (cube d m z R).card = Fintype.card {x : Torus d m // x ∈ cube d m z R} := by simp
    _ ≤ Fintype.card (Fin d → IntBox r) := Fintype.card_le_of_injective f hf
    _ = ∏ i : Fin d, Fintype.card (IntBox r) := by rw [Fintype.card_pi]
    _ = ∏ i : Fin d, (2 * r + 1) := by simp only [intBox_card]
    _ = (2 * r + 1) ^ d := by simp
    _ = (2 * ⌊R⌋₊ + 1) ^ d := by rfl

private lemma physicalDistance_triangle {d m : ℕ} (hm : 0 < m)
    (x y z : Torus d m) :
    physicalDistance d m x z ≤ physicalDistance d m x y + physicalDistance d m y z := by
  unfold physicalDistance
  exact_mod_cast (nnGraph_connected (d := d) hm).dist_triangle

private lemma cube_mem_enlarged {d m : ℕ} (x a z : Torus d m) (R Q : ℝ)
    (ha : a ∈ cube d m z R) (hx : x ∈ cube d m a Q) :
    x ∈ cube d m z (R + Q) := by
  have hcoord (i : Fin d) :
      ((x i - z i).valMinAbs.natAbs : ℝ) ≤ R + Q := by
    have hnat : (x i - z i).valMinAbs.natAbs ≤
        (x i - a i).valMinAbs.natAbs + (a i - z i).valMinAbs.natAbs := by
      calc
        (x i - z i).valMinAbs.natAbs = ((x i - a i) + (a i - z i)).valMinAbs.natAbs := by
          congr 1
          abel
        _ ≤ ((x i - a i).valMinAbs + (a i - z i).valMinAbs).natAbs :=
          ZMod.natAbs_valMinAbs_add_le _ _
        _ ≤ (x i - a i).valMinAbs.natAbs + (a i - z i).valMinAbs.natAbs :=
          Int.natAbs_add_le _ _
    calc
      ((x i - z i).valMinAbs.natAbs : ℝ) ≤
          (x i - a i).valMinAbs.natAbs + (a i - z i).valMinAbs.natAbs := by exact_mod_cast hnat
      _ ≤ Q + R := add_le_add (cube_coord_bound x a Q hx i) (cube_coord_bound a z R ha i)
      _ = R + Q := by ring
  have hbox : ∀ i : Fin d,
      ((min ((x i - z i).val) (OAI.Anderson.sideLength m - (x i - z i).val) : ℕ) : ℝ) ≤ R + Q := by
    intro i
    rw [← ZMod.valMinAbs_natAbs_eq_min]
    exact hcoord i
  simpa [cube] using hbox

private lemma cube_card_lower {d m : ℕ} (hm : 0 < m) (z : Torus d m) (r : ℕ)
    (hr : r ≤ OAI.Anderson.sideLength m / 2) :
    (r + 1) ^ d ≤ (cube d m z (r : ℝ)).card := by
  classical
  let g : (Fin d → Fin (r + 1)) → Torus d m := fun v i =>
    z i + (v i : ℕ)
  have hmem (v : Fin d → Fin (r + 1)) : g v ∈ cube d m z (r : ℝ) := by
    have hcoord : ∀ i : Fin d,
        (g v i - z i).valMinAbs.natAbs = (v i).val := by
      intro i
      have hdiff : g v i - z i = (v i : ℕ) := by
        dsimp [g]
        abel
      rw [hdiff, ZMod.valMinAbs_natCast_of_le_half]
      · simp
      · exact le_trans (Nat.le_of_lt_succ (v i).isLt) hr
    simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [← ZMod.valMinAbs_natAbs_eq_min (g v i - z i)]
    rw [hcoord]
    have hle : (v i).val ≤ r := by omega
    exact_mod_cast hle
  have hS : 2 ≤ OAI.Anderson.sideLength m := by
    rw [OAI.Anderson.sideLength]
    have hexp : 0 < 20 * m := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hexp.ne'
    rw [hn, pow_succ]
    have hpow : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by omega)
    omega
  have hg : Function.Injective g := by
    intro v w hvw
    funext i
    have hcoord : (v i : ZMod (OAI.Anderson.sideLength m)) = (w i : ZMod (OAI.Anderson.sideLength m)) := by
      have h := congrFun hvw i
      dsimp [g] at h
      exact add_left_cancel h
    have hvlt : (v i).val < OAI.Anderson.sideLength m := by
      have hlt := (v i).isLt
      omega
    have hwlt : (w i).val < OAI.Anderson.sideLength m := by
      have hlt := (w i).isLt
      omega
    have hval := congrArg ZMod.val hcoord
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hvlt, Nat.mod_eq_of_lt hwlt] at hval
    exact Fin.ext hval
  let g' : (Fin d → Fin (r + 1)) → {x : Torus d m // x ∈ cube d m z (r : ℝ)} :=
    fun v => ⟨g v, hmem v⟩
  have hg' : Function.Injective g' := fun _ _ h => hg (congrArg Subtype.val h)
  calc
    (r + 1) ^ d = Fintype.card (Fin d → Fin (r + 1)) := by simp
    _ ≤ Fintype.card {x : Torus d m // x ∈ cube d m z (r : ℝ)} :=
      Fintype.card_le_of_injective g' hg'
    _ = (cube d m z (r : ℝ)).card := by simp

private lemma torus_dist_le_of_mem_cube {d m : ℕ} (hm : 0 < m)
    (x y z : Torus d m) (R : ℝ) (hx : x ∈ cube d m z R) (hy : y ∈ cube d m z R) :
    ((nnGraph d m).dist x y : ℝ) ≤ (d : ℝ) * (2 * R) := by
  have hcoord (i : Fin d) :
      ((y i - x i).valMinAbs.natAbs : ℝ) ≤ 2 * R := by
    have hnat : (y i - x i).valMinAbs.natAbs ≤
        (y i - z i).valMinAbs.natAbs + (z i - x i).valMinAbs.natAbs := by
      calc
        (y i - x i).valMinAbs.natAbs = ((y i - z i) + (z i - x i)).valMinAbs.natAbs := by
          congr 1
          abel
        _ ≤ (y i - z i).valMinAbs.natAbs + (z i - x i).valMinAbs.natAbs := by
          calc
            ((y i - z i) + (z i - x i)).valMinAbs.natAbs ≤
                ((y i - z i).valMinAbs + (z i - x i).valMinAbs).natAbs :=
              ZMod.natAbs_valMinAbs_add_le _ _
            _ ≤ (y i - z i).valMinAbs.natAbs + (z i - x i).valMinAbs.natAbs :=
              Int.natAbs_add_le _ _
    have hneg : (z i - x i).valMinAbs.natAbs = (x i - z i).valMinAbs.natAbs := by
      rw [show z i - x i = -(x i - z i) by abel]
      exact ZMod.natAbs_valMinAbs_neg _
    calc
      ((y i - x i).valMinAbs.natAbs : ℝ) ≤
          (y i - z i).valMinAbs.natAbs + (z i - x i).valMinAbs.natAbs := by exact_mod_cast hnat
      _ ≤ R + R := add_le_add (cube_coord_bound y z R hy i) (by simpa [hneg] using cube_coord_bound x z R hx i)
      _ = 2 * R := by ring
  have hdist : ((nnGraph d m).dist x y : ℝ) ≤
      ∑ i : Fin d, ((y i - x i).valMinAbs.natAbs : ℝ) := by
    exact_mod_cast torus_dist_le_coordinate_sum hm x y
  calc
    ((nnGraph d m).dist x y : ℝ) ≤
        ∑ i : Fin d, ((y i - x i).valMinAbs.natAbs : ℝ) := hdist
    _ ≤ ∑ i : Fin d, (2 * R) := Finset.sum_le_sum fun i hi => hcoord i
    _ = (d : ℝ) * (2 * R) := by simp

private lemma packing_bound {d m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hm : 0 < m) (A : Finset κ) (center : κ → Torus d m) (z : Torus d m)
    (H R : ℝ) (q : ℕ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → R < physicalDistance d m (center a) (center b))
    (hcenter : ∀ a ∈ A, center a ∈ cube d m z H)
    (hq : 4 * (d : ℝ) * (q : ℝ) ≤ R)
    (hqtorus : q ≤ OAI.Anderson.sideLength m / 2) :
    (A.card : ℝ) * ((q + 1 : ℕ) : ℝ) ^ d ≤
      ((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ^ d := by
  classical
  let cubes : κ → Finset (Torus d m) := fun a => cube d m (center a) (q : ℝ)
  have hpair : (A : Set κ).PairwiseDisjoint cubes := by
    intro a ha b hb hab
    change Disjoint (cubes a) (cubes b)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hselfa : center a ∈ cube d m (center a) (q : ℝ) := by
      simp [cube]
    have hselfb : center b ∈ cube d m (center b) (q : ℝ) := by
      simp [cube]
    have hdist₁ := torus_dist_le_of_mem_cube hm (center a) x (center a) (q : ℝ) hselfa hxa
    have hdist₂ := torus_dist_le_of_mem_cube hm x (center b) (center b) (q : ℝ) hxb hselfb
    have htri := physicalDistance_triangle hm (center a) x (center b)
    have hle : physicalDistance d m (center a) (center b) ≤ R := by
      calc
        physicalDistance d m (center a) (center b) ≤
            physicalDistance d m (center a) x + physicalDistance d m x (center b) := htri
        _ ≤ (d : ℝ) * (2 * (q : ℝ)) + (d : ℝ) * (2 * (q : ℝ)) := add_le_add hdist₁ hdist₂
        _ = 4 * (d : ℝ) * (q : ℝ) := by ring
        _ ≤ R := hq
    exact (not_lt_of_ge hle) (hsep a ha b hb hab)
  let U : Finset (Torus d m) := A.biUnion cubes
  have hcardU : U.card = ∑ a ∈ A, (cubes a).card := by
    exact Finset.card_biUnion hpair
  have hsum : A.card * (q + 1) ^ d ≤ ∑ a ∈ A, (cubes a).card := by
    calc
      A.card * (q + 1) ^ d = ∑ a ∈ A, (q + 1) ^ d := by simp
      _ ≤ ∑ a ∈ A, (cubes a).card := Finset.sum_le_sum fun a ha =>
        cube_card_lower hm (center a) q hqtorus
  have hU : U ⊆ cube d m z (H + (q : ℝ)) := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
    exact cube_mem_enlarged x (center a) z H (q : ℝ) (hcenter a ha) hxa
  have hnat : A.card * (q + 1) ^ d ≤ (cube d m z (H + (q : ℝ))).card := by
    calc
      A.card * (q + 1) ^ d ≤ U.card := by simpa [hcardU] using hsum
      _ ≤ (cube d m z (H + (q : ℝ))).card := Finset.card_le_card hU
  have hupper := cube_card_upper z (H + (q : ℝ))
  exact_mod_cast (hnat.trans hupper)

private lemma torus_dist_le_plus {d m : ℕ} (hm : 0 < m) (i : Fin d)
    (x : Torus d m) (n : ℕ) :
    (nnGraph d m).dist x (x + n • OAI.Anderson.torusBasisVector i) ≤ n := by
  obtain ⟨p, hp⟩ := torus_plus_walk hm i x n
  calc
    (nnGraph d m).dist x (x + n • OAI.Anderson.torusBasisVector i) ≤ p.length :=
      SimpleGraph.dist_le p
    _ = n := hp

private lemma pathCost_empty_eq_length_sub_one {ι : Type} (xs : List ι) :
    AndersonAC.S78.pathCost (∅ : Finset ι) xs = xs.length - 1 := by
  classical
  simp [AndersonAC.S78.pathCost, List.length_zip]

private theorem halo_overlap_bound {d m n₀ j l : ℕ} (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C)
    (hm : 0 < m) (u : ℝ) (hj : 1 ≤ j) (hjm : 2 * j ≤ m)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (T : ClearingGeometry d m n₀ j l u C)
    (htpos : 0 < stageScale u j m) (htle : stageScale u j m ≤ 1) :
    ∀ x, ((Finset.univ.filter fun a => T.index a = j ∧
      x ∈ cube d m (T.anchor a)
        (200 * C * stageScale u j m ^ (-nu d) * separationRadius j)).card : ℝ) ≤
      (8 * (d : ℝ) * (400 * C + 3)) ^ d * stageScale u j m ^ (-(d : ℝ) * nu d) := by
  classical
  intro x
  let Rnat : ℕ := 4 ^ (8 * j)
  let R : ℝ := Rnat
  let t : ℝ := stageScale u j m
  let H : ℝ := 200 * C * t ^ (-nu d) * R
  let q : ℕ := ⌊R / (8 * (d : ℝ))⌋₊
  let A : Finset (Fin l) := Finset.univ.filter fun a =>
    T.index a = j ∧ x ∈ cube d m (T.anchor a) H
  have ht : t = stageScale u j m := rfl
  have hRpos : 0 < R := by positivity [R, Rnat]
  have hRone : 1 ≤ R := by
    dsimp [R, Rnat]
    norm_cast
    exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4)
  have hRnatSide : 2 * Rnat ≤ OAI.Anderson.sideLength m := by
    have hexp : 8 * j + 1 ≤ 20 * m := by omega
    have hpow : (4 : ℕ) ^ (8 * j + 1) ≤ 4 ^ (20 * m) :=
      Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) hexp
    have hpow' : 4 ^ (8 * j) * 4 ≤ 4 ^ (20 * m) := by simpa [pow_succ] using hpow
    dsimp [Rnat, OAI.Anderson.sideLength]
    omega
  have hqReal : (q : ℝ) ≤ R / (8 * (d : ℝ)) := by
    dsimp [q]
    exact Nat.floor_le (by positivity)
  have hden : 1 ≤ 8 * (d : ℝ) := by
    have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hqLeR : (q : ℝ) ≤ R :=
    hqReal.trans (div_le_self (le_of_lt hRpos) hden)
  have hqNatR : q ≤ Rnat := by
    have hqReal' : (q : ℝ) ≤ (Rnat : ℝ) := by simpa [R] using hqLeR
    exact_mod_cast hqReal'
  have hqtorus : q ≤ OAI.Anderson.sideLength m / 2 := by
    omega
  have hqsep : 4 * (d : ℝ) * (q : ℝ) ≤ R := by
    have hmul : (q : ℝ) * (8 * (d : ℝ)) ≤ R :=
      (le_div_iff₀ (by positivity : 0 < 8 * (d : ℝ))).mp hqReal
    nlinarith
  have hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      R < physicalDistance d m (T.anchor a) (T.anchor b) := by
    intro a ha b hb hab
    have hidxa := (Finset.mem_filter.mp ha).2.1
    have hidxb := (Finset.mem_filter.mp hb).2.1
    have hEq : T.index a = T.index b := hidxa.trans hidxb.symm
    have hsep0 := T.separated a b hab hEq (T.anchor a) (T.anchorMem a) (T.anchor b) (T.anchorMem b)
    simpa [R, Rnat, separationRadius, hidxa] using hsep0
  have hcenter : ∀ a ∈ A, T.anchor a ∈ cube d m x H := by
    intro a ha
    exact cube_mem_symm x (T.anchor a) H (Finset.mem_filter.mp ha).2.2
  have hpack : (A.card : ℝ) * ((q + 1 : ℕ) : ℝ) ^ d ≤
      ((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ^ d :=
    packing_bound hm A T.anchor x H R q hsep hcenter hqsep hqtorus
  have hfloor : ((⌊H + (q : ℝ)⌋₊ : ℕ) : ℝ) ≤ H + q := by
    exact Nat.floor_le (by positivity [H, C, t, R])
  have hnum : ((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤
      (400 * C * t ^ (-nu d) + 3) * R := by
    push_cast
    dsimp [H]
    have hqBound : (q : ℝ) ≤ R := hqLeR
    nlinarith [hfloor, hqBound, hRone]
  have hdenFloor : R ≤ 8 * (d : ℝ) * ((q : ℝ) + 1) := by
    have hfloorLt : R / (8 * (d : ℝ)) < (q : ℝ) + 1 := by
      dsimp [q]
      exact Nat.lt_floor_add_one _
    have hmul := mul_lt_mul_of_pos_left hfloorLt (by positivity : 0 < 8 * (d : ℝ))
    have hmul' : (R / (8 * (d : ℝ))) * (8 * (d : ℝ)) <
        ((q : ℝ) + 1) * (8 * (d : ℝ)) := by nlinarith [hmul]
    have hRlt : R < 8 * (d : ℝ) * ((q : ℝ) + 1) := by
      calc
        R = (R / (8 * (d : ℝ))) * (8 * (d : ℝ)) := by field_simp
        _ < ((q : ℝ) + 1) * (8 * (d : ℝ)) := hmul'
        _ = 8 * (d : ℝ) * ((q : ℝ) + 1) := by ring
    exact le_of_lt hRlt
  have hqpos : 0 < (q : ℝ) + 1 := by positivity
  have hratio :
      ((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ((q : ℝ) + 1) ≤
        8 * (d : ℝ) * (400 * C * t ^ (-nu d) + 3) := by
    apply (div_le_iff₀ hqpos).2
    calc
      ((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤
          (400 * C * t ^ (-nu d) + 3) * R := hnum
      _ ≤ (400 * C * t ^ (-nu d) + 3) * (8 * (d : ℝ) * ((q : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hdenFloor (by positivity)
      _ = (8 * (d : ℝ) * (400 * C * t ^ (-nu d) + 3)) * ((q : ℝ) + 1) := by ring
  have hpackCast : (A.card : ℝ) * ((q : ℝ) + 1) ^ d ≤
      ((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ^ d := by
    simpa only [Nat.cast_add, Nat.cast_one] using hpack
  have hcard : (A.card : ℝ) ≤
      (((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ((q : ℝ) + 1)) ^ d := by
    rw [div_pow]
    exact (le_div_iff₀ (pow_pos hqpos d)).2 hpackCast
  have hpow :
      (((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ((q : ℝ) + 1)) ^ d ≤
        (8 * (d : ℝ) * (400 * C * t ^ (-nu d) + 3)) ^ d :=
    pow_le_pow_left₀ (by positivity) hratio d
  have hnuPos : 0 < nu d := by
    unfold nu delta
    positivity
  have hX : 1 ≤ t ^ (-nu d) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos htpos htle (by linarith)
  have hconst : 400 * C * t ^ (-nu d) + 3 ≤ (400 * C + 3) * t ^ (-nu d) := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ 400 * C) (sub_nonneg.mpr hX)]
  have hbound : (A.card : ℝ) ≤
      (8 * (d : ℝ) * (400 * C + 3)) ^ d * (t ^ (-nu d)) ^ d := by
    calc
      (A.card : ℝ) ≤
          (((2 * ⌊H + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ((q : ℝ) + 1)) ^ d := hcard
      _ ≤ (8 * (d : ℝ) * (400 * C * t ^ (-nu d) + 3)) ^ d := hpow
      _ ≤ (8 * (d : ℝ) * (400 * C + 3) * t ^ (-nu d)) ^ d := by
        have hbase : 8 * (d : ℝ) * (400 * C * t ^ (-nu d) + 3) ≤
            8 * (d : ℝ) * (400 * C + 3) * t ^ (-nu d) := by
          calc
            8 * (d : ℝ) * (400 * C * t ^ (-nu d) + 3) ≤
                8 * (d : ℝ) * ((400 * C + 3) * t ^ (-nu d)) :=
              mul_le_mul_of_nonneg_left hconst (by positivity)
            _ = 8 * (d : ℝ) * (400 * C + 3) * t ^ (-nu d) := by ring
        exact pow_le_pow_left₀ (by positivity) hbase d
      _ = (8 * (d : ℝ) * (400 * C + 3)) ^ d * (t ^ (-nu d)) ^ d := by rw [mul_pow]
  have hpowx : (t ^ (-nu d)) ^ d = t ^ (-(d : ℝ) * nu d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt htpos)]
    congr 1
    ring
  have hfinal : (A.card : ℝ) ≤
      (8 * (d : ℝ) * (400 * C + 3)) ^ d * t ^ (-(d : ℝ) * nu d) := by
    simpa [hpowx] using hbound
  have hAeq : A = Finset.univ.filter (fun a : Fin l => T.index a = j ∧
      x ∈ cube d m (T.anchor a)
        (200 * C * stageScale u j m ^ (-nu d) * separationRadius j)) := by
    ext a
    dsimp [A]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [H, R, Rnat, t, separationRadius]
  rw [hAeq] at hfinal
  exact hfinal

private theorem stage_anchor_count_bound {d m n₀ j s l : ℕ} (hd : 3 ≤ d) (u C : ℝ)
    (hm : 0 < m) (hsm : 2 * s ≤ m)
    (T : ClearingGeometry d m n₀ j l u C) :
    ((Fintype.card {a : Fin l // T.index a = s} : ℕ) : ℝ) ≤
      (40 * (d : ℝ)) ^ d * (OAI.Anderson.sideLength m : ℝ) ^ d /
        (4 : ℝ) ^ (8 * d * s) := by
  classical
  let κ : Type := {a : Fin l // T.index a = s}
  let Rnat : ℕ := 4 ^ (8 * s)
  let R : ℝ := Rnat
  let S : ℝ := OAI.Anderson.sideLength m
  let q : ℕ := ⌊R / (8 * (d : ℝ))⌋₊
  have hRpos : 0 < R := by positivity [R,Rnat]
  have hRone : 1 ≤ R := by
    dsimp [R,Rnat]
    norm_cast
    exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4)
  have hRnatSide : 2 * Rnat ≤ OAI.Anderson.sideLength m := by
    have hexp : 8 * s + 1 ≤ 20 * m := by omega
    have hpow : (4 : ℕ) ^ (8 * s + 1) ≤ 4 ^ (20 * m) :=
      Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) hexp
    have hpow' : 4 ^ (8 * s) * 4 ≤ 4 ^ (20 * m) := by simpa [pow_succ] using hpow
    dsimp [Rnat, OAI.Anderson.sideLength]
    omega
  have hqReal : (q : ℝ) ≤ R / (8 * (d : ℝ)) := by
    dsimp [q]
    exact Nat.floor_le (by positivity)
  have hden : 1 ≤ 8 * (d : ℝ) := by
    have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hqLeR : (q : ℝ) ≤ R := hqReal.trans (div_le_self (le_of_lt hRpos) hden)
  have hqNatR : q ≤ Rnat := by
    have hqReal' : (q : ℝ) ≤ (Rnat : ℝ) := by simpa [R] using hqLeR
    exact_mod_cast hqReal'
  have hqtorus : q ≤ OAI.Anderson.sideLength m / 2 := by omega
  have hqsep : 4 * (d : ℝ) * (q : ℝ) ≤ R := by
    have hmul : (q : ℝ) * (8 * (d : ℝ)) ≤ R :=
      (le_div_iff₀ (by positivity : 0 < 8 * (d : ℝ))).mp hqReal
    nlinarith
  let A : Finset κ := Finset.univ
  let center : κ → Torus d m := fun a => T.anchor a.val
  let z : Torus d m := 0
  have hcenter : ∀ a ∈ A, center a ∈ cube d m z S := by
    intro a ha
    have hbox : ∀ i : Fin d,
        ((min ((center a i - z i).val) (OAI.Anderson.sideLength m - (center a i - z i).val) : ℕ) : ℝ) ≤ S := by
      intro i
      have hval := (center a i - z i).val_lt
      have hmin : min ((center a i - z i).val) (OAI.Anderson.sideLength m - (center a i - z i).val) ≤
          OAI.Anderson.sideLength m := le_trans (Nat.min_le_left _ _) hval.le
      have hminR : ((min ((center a i - z i).val)
          (OAI.Anderson.sideLength m - (center a i - z i).val) : ℕ) : ℝ) ≤
          (OAI.Anderson.sideLength m : ℝ) := by exact_mod_cast hmin
      simpa [S] using hminR
    simpa [cube, z, S] using hbox
  have hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → R < physicalDistance d m (center a) (center b) := by
    intro a ha b hb hab
    have habval : a.val ≠ b.val := by
      intro heq
      exact hab (Subtype.ext heq)
    have hja : T.index a.val = s := a.property
    have hjb : T.index b.val = s := b.property
    have hEq : T.index a.val = T.index b.val := hja.trans hjb.symm
    have hsep0 := T.separated a.val b.val habval hEq (T.anchor a.val) (T.anchorMem a.val)
      (T.anchor b.val) (T.anchorMem b.val)
    simpa [R, Rnat, separationRadius, hja] using hsep0
  have hpack := packing_bound hm A center z S R q hsep hcenter hqsep hqtorus
  have hfloor : ((⌊S + (q : ℝ)⌋₊ : ℕ) : ℝ) ≤ S + q := Nat.floor_le (by positivity [S,q])
  have hSlarge : 2 * R ≤ S := by
    change (2 * (Rnat : ℝ)) ≤ (OAI.Anderson.sideLength m : ℝ)
    exact_mod_cast hRnatSide
  have hSone : 1 ≤ S := by nlinarith [hSlarge, hRone]
  have hnum : ((2 * ⌊S + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * S := by
    push_cast
    have hqBound : (q : ℝ) ≤ S := by
      dsimp [S]
      exact_mod_cast hqNatR.trans (by omega : Rnat ≤ OAI.Anderson.sideLength m)
    dsimp [S] at hfloor hqBound hSone ⊢
    nlinarith [hfloor, hqBound, hSone]
  have hdenFloor : R ≤ 8 * (d : ℝ) * ((q : ℝ) + 1) := by
    have hfloorLt : R / (8 * (d : ℝ)) < (q : ℝ) + 1 := by
      dsimp [q]
      exact Nat.lt_floor_add_one _
    have hmul := mul_lt_mul_of_pos_left hfloorLt (by positivity : 0 < 8 * (d : ℝ))
    have hmul' : (R / (8 * (d : ℝ))) * (8 * (d : ℝ)) < ((q : ℝ) + 1) * (8 * (d : ℝ)) := by
      nlinarith [hmul]
    have hRlt : R < 8 * (d : ℝ) * ((q : ℝ) + 1) := by
      calc
        R = (R / (8 * (d : ℝ))) * (8 * (d : ℝ)) := by field_simp
        _ < ((q : ℝ) + 1) * (8 * (d : ℝ)) := hmul'
        _ = 8 * (d : ℝ) * ((q : ℝ) + 1) := by ring
    exact le_of_lt hRlt
  have hqpos : 0 < (q : ℝ) + 1 := by positivity
  have hRatio : ((2 * ⌊S + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ((q : ℝ) + 1) ≤
      40 * (d : ℝ) * S / R := by
    apply (div_le_iff₀ hqpos).2
    calc
      ((2 * ⌊S + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * S := hnum
      _ ≤ (40 * (d : ℝ) * S / R) * ((q : ℝ) + 1) := by
        have hfac : 5 * R ≤ 40 * (d : ℝ) * ((q : ℝ) + 1) := by nlinarith [hdenFloor]
        have hdiv : 5 ≤ (40 * (d : ℝ) * ((q : ℝ) + 1)) / R :=
          (le_div_iff₀ hRpos).2 hfac
        calc
          5 * S = S * 5 := by ring
          _ ≤ S * ((40 * (d : ℝ) * ((q : ℝ) + 1)) / R) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
          _ = (40 * (d : ℝ) * S / R) * ((q : ℝ) + 1) := by field_simp <;> ring
  have hpackCast : (Fintype.card κ : ℝ) * ((q : ℝ) + 1) ^ d ≤
      ((2 * ⌊S + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) ^ d := by
    simpa [A, Nat.cast_add, Nat.cast_one] using hpack
  have hcard : (Fintype.card κ : ℝ) ≤
      (((2 * ⌊S + (q : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ((q : ℝ) + 1)) ^ d := by
    rw [div_pow]
    exact (le_div_iff₀ (pow_pos hqpos d)).2 hpackCast
  have hcard' : (Fintype.card κ : ℝ) ≤ (40 * (d : ℝ) * S / R) ^ d :=
    hcard.trans (pow_le_pow_left₀ (by positivity) hRatio d)
  have hcard'' : (Fintype.card κ : ℝ) ≤
      (40 * (d : ℝ)) ^ d * S ^ d / R ^ d := by
    simpa [div_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm] using hcard'
  have hRpowNat : (4 ^ (8 * s)) ^ d = 4 ^ (8 * d * s) := by
    have hbase : 4 ^ (8 * s) = (4 ^ 8) ^ s := by rw [← pow_mul]
    calc
      (4 ^ (8 * s)) ^ d = ((4 ^ 8) ^ s) ^ d := by rw [hbase]
      _ = (4 ^ 8) ^ (s * d) := by rw [← pow_mul]
      _ = 4 ^ (8 * d * s) := by
        have he : 8 * d * s = 8 * (s * d) := by ring
        rw [he, ← pow_mul]
  have hRpow : R ^ d = (4 : ℝ) ^ (8 * d * s) := by
    dsimp [R, Rnat]
    calc
      ((4 ^ (8 * s) : ℕ) : ℝ) ^ d = (((4 ^ (8 * s)) ^ d : ℕ) : ℝ) := by norm_cast
      _ = ((4 ^ (8 * d * s) : ℕ) : ℝ) := by exact_mod_cast hRpowNat
      _ = (4 : ℝ) ^ (8 * d * s) := by norm_cast
  have hcardFinal : (Fintype.card κ : ℝ) ≤
      (40 * (d : ℝ)) ^ d * S ^ d / (4 : ℝ) ^ (8 * d * s) := by
    calc
      (Fintype.card κ : ℝ) ≤ (40 * (d : ℝ)) ^ d * S ^ d / R ^ d := hcard''
      _ = (40 * (d : ℝ)) ^ d * S ^ d / (4 : ℝ) ^ (8 * d * s) := by rw [hRpow]
  simpa [κ, S] using hcardFinal

private theorem terminalDistance_empty_eq_dist {ι : Type} [DecidableEq ι]
    (G : SimpleGraph ι) (hconn : G.Connected) (u v : ι) :
    AndersonAC.S78.terminalDistance G (∅ : Finset ι) u v = (G.dist u v : ℝ) := by
  classical
  unfold AndersonAC.S78.terminalDistance
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
    let ys := p.support
    have hne : ys ≠ [] := p.support_ne_nil
    have hchain : ys.IsChain G.Adj := p.isChain_adj_support
    have hhead : ys.head? = some u := by
      have hh : ys.head hne = u := by simpa [ys] using p.head_support
      exact (List.head_eq_iff_head?_eq_some hne).1 hh
    have hlast : ys.getLast? = some v := by
      have hh : ys.getLast hne = v := by simpa [ys] using p.getLast_support
      exact (List.getLast_eq_iff_getLast?_eq_some hne).1 hh
    have hlen : ys.length - 1 = p.length := by
      dsimp [ys]
      rw [p.length_support]
      simp
    have hcost : AndersonAC.S78.pathCost (∅ : Finset ι) ys = G.dist u v := by
      rw [pathCost_empty_eq_length_sub_one]
      rw [hlen, hp]
    have hmem : G.dist u v ∈ {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧
        xs.head? = some u ∧ xs.getLast? = some v ∧
        AndersonAC.S78.pathCost (∅ : Finset ι) xs = n} :=
      ⟨ys, hchain, hhead, hlast, hcost⟩
    have hle : (sInf {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧
        xs.head? = some u ∧ xs.getLast? = some v ∧
        AndersonAC.S78.pathCost (∅ : Finset ι) xs = n} : ℕ) ≤ G.dist u v := Nat.sInf_le hmem
    exact_mod_cast hle
  · have hS : {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧
        xs.getLast? = some v ∧ AndersonAC.S78.pathCost (∅ : Finset ι) xs = n}.Nonempty := by
      obtain ⟨ys, hchain, hhead, hlast⟩ := AndersonAC.SolS78.exists_chain_of_connected hconn u v
      exact ⟨AndersonAC.S78.pathCost (∅ : Finset ι) ys, ys, hchain, hhead, hlast, rfl⟩
    have hwalk : ∀ n ∈ {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧
        xs.head? = some u ∧ xs.getLast? = some v ∧
        AndersonAC.S78.pathCost (∅ : Finset ι) xs = n}, G.dist u v ≤ n := by
      intro n hn
      rcases hn with ⟨ys, hchain, hhead, hlast, hcost⟩
      have hne : ys ≠ [] := by
        intro h
        simp [h] at hhead
      have hstart : ys.head hne = u := (List.head_eq_iff_head?_eq_some hne).2 hhead
      have hend : ys.getLast hne = v := (List.getLast_eq_iff_getLast?_eq_some hne).2 hlast
      let p := (SimpleGraph.Walk.ofSupport ys hne hchain).copy hstart hend
      have hdist : G.dist u v ≤ p.length := SimpleGraph.dist_le p
      have hlen : p.length = ys.length - 1 := by
        simp [p, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_ofSupport]
      have hcost' : ys.length - 1 = n := by
        simpa [pathCost_empty_eq_length_sub_one] using hcost
      calc
        G.dist u v ≤ p.length := hdist
        _ = ys.length - 1 := hlen
        _ = n := hcost'
    exact_mod_cast (le_csInf hS hwalk)

private theorem stage_scale_bounds (u : ℝ) (j m : ℕ)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j ≤ m) :
    (1 / 4 : ℝ) / (4 : ℝ) ^ j < stageScale u j m ∧
    stageScale u j m ≤ 2 / (4 : ℝ) ^ j := by
  have huLower : (1 / 4 : ℝ) < u := hu.1
  have huUpper : u ≤ 1 := hu.2
  have huPos : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) huLower
  have hpj : 0 < (4 : ℝ) ^ j := by positivity
  have hpm : 0 < (4 : ℝ) ^ m := by positivity
  have hpowers : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hjm
  have hrecip : 1 / (4 : ℝ) ^ m ≤ 1 / (4 : ℝ) ^ j :=
    one_div_le_one_div_of_le hpj hpowers
  have hfirstLower : (1 / 4 : ℝ) / (4 : ℝ) ^ j < u / (4 : ℝ) ^ j :=
    (div_lt_div_iff_of_pos_right hpj).2 huLower
  have hfirstUpper : u / (4 : ℝ) ^ j ≤ 1 / (4 : ℝ) ^ j :=
    (div_le_div_iff_of_pos_right hpj).2 huUpper
  have hsecondUpper : u / (4 : ℝ) ^ m ≤ 1 / (4 : ℝ) ^ j :=
    ((div_le_div_iff_of_pos_right hpm).2 huUpper).trans hrecip
  constructor
  · unfold stageScale
    linarith [hfirstLower, div_pos huPos hpm]
  · unfold stageScale
    calc
      u / (4 : ℝ) ^ j + u / (4 : ℝ) ^ m ≤
          1 / (4 : ℝ) ^ j + 1 / (4 : ℝ) ^ j := add_le_add hfirstUpper hsecondUpper
      _ = 2 / (4 : ℝ) ^ j := by ring

private lemma stage_heat_bound {m k : ℕ} (u : ℝ)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hk : 1 ≤ k) (hkm : k ≤ m) :
    (heatLimit (stageScale u k m) : ℝ) ≤ (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ)) := by
  have hs := stage_scale_bounds u k m hu hkm
  have htpos : 0 < stageScale u k m := lt_trans (by positivity) hs.1
  have hpow4 : (4 : ℝ) ≤ (4 : ℝ) ^ k := by
    have hk' : 1 ≤ k := hk
    calc
      (4 : ℝ) = (4 : ℝ) ^ 1 := by norm_num
      _ ≤ (4 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hk'
  have htle : stageScale u k m ≤ 1 := by
    have hfrac : 2 / (4 : ℝ) ^ k ≤ 1 := by
      rw [div_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ k)]
      linarith
    exact hs.2.trans hfrac
  have hheat : (heatLimit (stageScale u k m) : ℝ) ≤
      stageScale u k m ^ (-1 - heatExponent) := by
    unfold heatLimit
    exact Nat.floor_le (Real.rpow_nonneg htpos.le _)
  have he : heatExponent ≤ (0.01 : ℝ) := by norm_num [heatExponent, delta]
  have hpowExp : -(1.01 : ℝ) ≤ -1 - heatExponent := by linarith
  have hcompare : stageScale u k m ^ (-1 - heatExponent) ≤ stageScale u k m ^ (-1.01 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge htpos htle hpowExp
  let b : ℝ := (1 / 4 : ℝ) / (4 : ℝ) ^ k
  have hbpos : 0 < b := by positivity [b]
  have htb : b ≤ stageScale u k m := le_of_lt hs.1
  have hbpow : b ^ (-1.01 : ℝ) =
      (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ)) := by
    have hk1 : k + 1 = Nat.succ k := by omega
    have hbEq : b = ((4 : ℝ) ^ (k + 1))⁻¹ := by
      dsimp [b]
      rw [hk1, pow_succ]
      field_simp
    have hbInv : b⁻¹ = (4 : ℝ) ^ (k + 1) := by
      rw [hbEq, inv_inv]
    calc
      b ^ (-1.01 : ℝ) = b⁻¹ ^ (1.01 : ℝ) := by rw [Real.rpow_neg_eq_inv_rpow]
      _ = ((4 : ℝ) ^ (k + 1)) ^ (1.01 : ℝ) := by rw [hbInv]
      _ = (4 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * (1.01 : ℝ)) := by
        symm
        exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (4 : ℝ)) (k + 1) (1.01 : ℝ)
      _ = (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ)) := by congr 1 <;> ring
  calc
    (heatLimit (stageScale u k m) : ℝ) ≤ stageScale u k m ^ (-1 - heatExponent) := hheat
    _ ≤ stageScale u k m ^ (-1.01 : ℝ) := hcompare
    _ ≤ b ^ (-1.01 : ℝ) := Real.rpow_le_rpow_of_nonpos hbpos htb (by norm_num)
    _ = (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ)) := hbpow

private def stageBudget (C : ℝ) (k : ℕ) : ℕ :=
  ⌈C * (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ))⌉₊

private lemma stageBudget_upper (C : ℝ) (hC : 1 ≤ C) (k : ℕ) :
    ((stageBudget C k : ℕ) : ℝ) ≤ (C + 1) * (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ)) := by
  let P : ℝ := (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ))
  have hP : 1 ≤ P := by
    dsimp [P]
    apply Real.one_le_rpow (by norm_num)
    positivity
  have hceil : (stageBudget C k : ℝ) < C * P + 1 := by
    dsimp [stageBudget, P]
    exact Nat.ceil_lt_add_one (by positivity)
  calc
    (stageBudget C k : ℝ) ≤ C * P + 1 := le_of_lt hceil
    _ ≤ C * P + P := by linarith [hP]
    _ = (C + 1) * P := by ring
private lemma stageBudget_quadratic (C : ℝ) (hC : 1 ≤ C) (k : ℕ) :
    (stageBudget C k : ℝ) ≤ 16 * (C + 1) * (4 : ℝ) ^ (2 * k : ℕ) := by
  have hupper := stageBudget_upper C hC k
  have hexp : 1.01 * ((k + 1 : ℕ) : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) := by
    push_cast
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    nlinarith [hk0]
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (4 : ℝ)) hexp
  have hpowEq : (4 : ℝ) ^ (2 * (k + 1) : ℕ) =
      16 * (4 : ℝ) ^ (2 * k : ℕ) := by
    have heq : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [heq, pow_add]
    norm_num
    ring
  calc
    (stageBudget C k : ℝ) ≤ (C + 1) * (4 : ℝ) ^ (1.01 * ((k + 1 : ℕ) : ℝ)) := hupper
    _ ≤ (C + 1) * (4 : ℝ) ^ ((2 * (k + 1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (C + 1) * (4 : ℝ) ^ (2 * (k + 1) : ℕ) := by rw [Real.rpow_natCast]
    _ = 16 * (C + 1) * (4 : ℝ) ^ (2 * k : ℕ) := by rw [hpowEq]; ring

private lemma four_ratio_le_half_pow {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) :
    (4 : ℝ) ^ (2 * k : ℕ) / (4 : ℝ) ^ (8 * d * k : ℕ) ≤ (1 / 2 : ℝ) ^ k := by
  have hdk : 3 * k ≤ d * k := Nat.mul_le_mul_right k hd
  have hexp : (2 : ℕ) * k + 22 * k ≤ 8 * d * k := by nlinarith [hdk]
  have hdiff : 8 * d * k = 2 * k + (8 * d * k - 2 * k) := by omega
  have hpowNat : (4 : ℝ) ^ (8 * d * k : ℕ) =
      (4 : ℝ) ^ (2 * k : ℕ) * (4 : ℝ) ^ ((8 * d * k - 2 * k) : ℕ) := by
    rw [← pow_add]
    congr 1
  have hpowNat' : (4 : ℝ) ^ (22 * k : ℕ) ≤
      (4 : ℝ) ^ ((8 * d * k - 2 * k) : ℕ) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)
  have hpow : (2 : ℝ) ^ k ≤ (4 : ℝ) ^ (22 * k : ℕ) := by
    calc
      (2 : ℝ) ^ k ≤ ((4 : ℝ) ^ 22) ^ k :=
        pow_le_pow_left₀ (by positivity) (by norm_num : (2 : ℝ) ≤ 4 ^ 22) k
      _ = (4 : ℝ) ^ (22 * k : ℕ) := by rw [pow_mul]
  have hden : (2 : ℝ) ^ k ≤ (4 : ℝ) ^ ((8 * d * k - 2 * k) : ℕ) := hpow.trans hpowNat'
  have hquotNat : (4 : ℝ) ^ (2 * k : ℕ) / (4 : ℝ) ^ (8 * d * k : ℕ) =
      1 / (4 : ℝ) ^ ((8 * d * k - 2 * k) : ℕ) := by
    rw [hpowNat]
    field_simp
  rw [hquotNat]
  have hdiv : 1 / (4 : ℝ) ^ ((8 * d * k - 2 * k) : ℕ) ≤ 1 / (2 : ℝ) ^ k :=
    one_div_le_one_div_of_le (by positivity) hden
  simpa [div_pow] using hdiv

private lemma stage_edit_card_le_budget {d m n₀ j l : ℕ} (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C)
    (u : ℝ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (T : ClearingGeometry d m n₀ j l u C)
    (a : Fin l) (hidx : 1 ≤ T.index a) (hjm : T.index a ≤ m) :
    (T.edits a).card ≤ stageBudget C (T.index a) := by
  have ht := stage_heat_bound (m := m) (k := T.index a) u hu hidx hjm
  have hC0 : 0 ≤ C := by linarith
  have hsize := T.groupSize a
  have hcard : ((T.edits a).card : ℝ) ≤ C *
      (4 : ℝ) ^ (1.01 * ((T.index a + 1 : ℕ) : ℝ)) :=
    hsize.trans (mul_le_mul_of_nonneg_left ht hC0)
  have hceil : C * (4 : ℝ) ^ (1.01 * ((T.index a + 1 : ℕ) : ℝ)) ≤
      (stageBudget C (T.index a) : ℝ) := Nat.le_ceil _
  exact Nat.cast_le.mp (hcard.trans hceil)

private lemma stage_removed_fraction_bound {d m n₀ j l : ℕ} (hd : 3 ≤ d) (u C : ℝ) (hC : 1 ≤ C)
    (hm : 0 < m) (k : ℕ) (hk : 1 ≤ k) (hkm : 2 * k ≤ m)
    (T : ClearingGeometry d m n₀ j l u C) :
    ((Finset.univ.filter fun a : Fin l => T.index a = k).card : ℝ) *
        (stageBudget C k : ℝ) ≤
      (40 * (d : ℝ)) ^ d * 16 * (C + 1) *
        (OAI.Anderson.sideLength m : ℝ) ^ d * (1 / 2 : ℝ) ^ k := by
  let F : Finset (Fin l) := Finset.univ.filter fun a => T.index a = k
  let Den : ℝ := (4 : ℝ) ^ (8 * d * k : ℕ)
  let S : ℝ := OAI.Anderson.sideLength m
  have hFcard : F.card = Fintype.card {a : Fin l // T.index a = k} := by
    simpa [F] using (Fintype.card_subtype (fun a : Fin l => T.index a = k)).symm
  have hCount0 := stage_anchor_count_bound (d := d) (m := m) (n₀ := n₀) (j := j)
    (s := k) (l := l) hd u C hm hkm T
  have hCount : (F.card : ℝ) ≤ (40 * (d : ℝ)) ^ d * S ^ d / Den := by
    rw [← hFcard] at hCount0
    simpa [S, Den] using hCount0
  have hBudget := stageBudget_quadratic C hC k
  have hRatio := four_ratio_le_half_pow hd hk
  have hBudgetDiv : (stageBudget C k : ℝ) / Den ≤
      16 * (C + 1) * (1 / 2 : ℝ) ^ k := by
    calc
      (stageBudget C k : ℝ) / Den ≤
          (16 * (C + 1) * (4 : ℝ) ^ (2 * k : ℕ)) / Den :=
        div_le_div_of_nonneg_right hBudget (by positivity)
      _ = 16 * (C + 1) * ((4 : ℝ) ^ (2 * k : ℕ) / Den) := by ring
      _ ≤ 16 * (C + 1) * (1 / 2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left (by simpa [Den] using hRatio) (by positivity)
  calc
    (F.card : ℝ) * (stageBudget C k : ℝ) ≤
        ((40 * (d : ℝ)) ^ d * S ^ d / Den) * (stageBudget C k : ℝ) :=
      mul_le_mul_of_nonneg_right hCount (by positivity)
    _ = (40 * (d : ℝ)) ^ d * S ^ d * ((stageBudget C k : ℝ) / Den) := by ring
    _ ≤ (40 * (d : ℝ)) ^ d * S ^ d * (16 * (C + 1) * (1 / 2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left hBudgetDiv (by positivity)
    _ = (40 * (d : ℝ)) ^ d * 16 * (C + 1) * S ^ d * (1 / 2 : ℝ) ^ k := by ring

private lemma sum_half_range_le_two (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) ≤ 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) n]
  have hEq : ((1 / 2 : ℝ) ^ n - 1) / ((1 / 2 : ℝ) - 1) =
      2 * (1 - (1 / 2 : ℝ) ^ n) := by field_simp; ring
  rw [hEq]
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

private lemma sum_half_Ico_le_two_mul (n j : ℕ) (hnj : n ≤ j + 1) :
    (∑ i ∈ Finset.Ico n (j + 1), (1 / 2 : ℝ) ^ i) ≤
      2 * (1 / 2 : ℝ) ^ n := by
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    (∑ i ∈ Finset.range (j + 1 - n), (1 / 2 : ℝ) ^ (n + i)) =
        (1 / 2 : ℝ) ^ n * ∑ i ∈ Finset.range (j + 1 - n), (1 / 2 : ℝ) ^ i := by
          simp_rw [pow_add]
          rw [Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) ^ n * 2 := by
      apply mul_le_mul_of_nonneg_left (sum_half_range_le_two _) (by positivity)
    _ = 2 * (1 / 2 : ℝ) ^ n := by ring

private theorem terminal_card_by_stage_budget {d m n₀ j l : ℕ} (hd : 3 ≤ d)
    (C : ℝ) (hC : 1 ≤ C) (hn₀ : 1 ≤ n₀) (hn₀j : n₀ ≤ j) (hjm : 2 * j ≤ m)
    (u : ℝ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (T : ClearingGeometry d m n₀ j l u C) :
    (geometryTerminals T).card ≤
      ∑ k ∈ Finset.Ico n₀ (j + 1),
        (Finset.univ.filter fun a : Fin l => T.index a = k).card * stageBudget C k := by
  classical
  have hgroup : ∀ a : Fin l, (T.edits a).card ≤ stageBudget C (T.index a) := by
    intro a
    have hst := T.stages a
    have hidx : 1 ≤ T.index a := by omega
    have hjm' : T.index a ≤ m := by omega
    exact stage_edit_card_le_budget hd C hC u hu T a hidx hjm'
  have hmaps : ∀ a ∈ (Finset.univ : Finset (Fin l)),
      T.index a ∈ Finset.Ico n₀ (j + 1) := by
    intro a ha
    have hst := T.stages a
    simp only [Finset.mem_Ico]
    omega
  have hsumFiber :
      ∑ a ∈ (Finset.univ : Finset (Fin l)), stageBudget C (T.index a) =
        ∑ k ∈ Finset.Ico n₀ (j + 1),
          (Finset.univ.filter fun a : Fin l => T.index a = k).card * stageBudget C k := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun k hk => ?_
    apply Finset.sum_const_nat
    intro a ha
    exact congrArg (stageBudget C) (Finset.mem_filter.mp ha).2
  have hsum :
      ∑ a ∈ (Finset.univ : Finset (Fin l)), (T.edits a).card ≤
        ∑ a ∈ (Finset.univ : Finset (Fin l)), stageBudget C (T.index a) :=
    Finset.sum_le_sum fun a ha => hgroup a
  calc
    (geometryTerminals T).card ≤ ∑ a ∈ (Finset.univ : Finset (Fin l)), (T.edits a).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ (Finset.univ : Finset (Fin l)), stageBudget C (T.index a) := hsum
    _ = ∑ k ∈ Finset.Ico n₀ (j + 1),
          (Finset.univ.filter fun a : Fin l => T.index a = k).card * stageBudget C k := hsumFiber

private theorem terminal_card_fraction_bound {d m n₀ j l : ℕ} (hd : 3 ≤ d)
    (C : ℝ) (hC : 1 ≤ C) (hn₀ : 1 ≤ n₀) (hn₀j : n₀ ≤ j) (hjm : 2 * j ≤ m)
    (u : ℝ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (T : ClearingGeometry d m n₀ j l u C) :
    ((geometryTerminals T).card : ℝ) ≤
      (40 * (d : ℝ)) ^ d * 16 * (C + 1) * (OAI.Anderson.sideLength m : ℝ) ^ d *
        (2 * (1 / 2 : ℝ) ^ n₀) := by
  classical
  have hterm := terminal_card_by_stage_budget hd C hC hn₀ hn₀j hjm u hu T
  have htermReal : ((geometryTerminals T).card : ℝ) ≤
      ∑ k ∈ Finset.Ico n₀ (j + 1),
        ((Finset.univ.filter fun a : Fin l => T.index a = k).card : ℝ) *
          (stageBudget C k : ℝ) := by
    exact_mod_cast hterm
  have hstages : ∀ k ∈ Finset.Ico n₀ (j + 1),
      ((Finset.univ.filter fun a : Fin l => T.index a = k).card : ℝ) *
        (stageBudget C k : ℝ) ≤
      (40 * (d : ℝ)) ^ d * 16 * (C + 1) *
        (OAI.Anderson.sideLength m : ℝ) ^ d * (1 / 2 : ℝ) ^ k := by
    intro k hk
    have hkBounds := (Finset.mem_Ico.mp hk)
    have hk1 : 1 ≤ k := le_trans hn₀ hkBounds.1
    have hkm : 2 * k ≤ m := by omega
    exact stage_removed_fraction_bound hd u C hC (by omega) k hk1 hkm T
  calc
    ((geometryTerminals T).card : ℝ) ≤
        ∑ k ∈ Finset.Ico n₀ (j + 1),
          ((Finset.univ.filter fun a : Fin l => T.index a = k).card : ℝ) *
            (stageBudget C k : ℝ) := htermReal
    _ ≤ ∑ k ∈ Finset.Ico n₀ (j + 1),
          (40 * (d : ℝ)) ^ d * 16 * (C + 1) *
            (OAI.Anderson.sideLength m : ℝ) ^ d * (1 / 2 : ℝ) ^ k :=
      Finset.sum_le_sum fun k hk => hstages k hk
    _ = (40 * (d : ℝ)) ^ d * 16 * (C + 1) *
          (OAI.Anderson.sideLength m : ℝ) ^ d *
          ∑ k ∈ Finset.Ico n₀ (j + 1), (1 / 2 : ℝ) ^ k := by
      rw [← Finset.mul_sum]
    _ ≤ (40 * (d : ℝ)) ^ d * 16 * (C + 1) *
          (OAI.Anderson.sideLength m : ℝ) ^ d * (2 * (1 / 2 : ℝ) ^ n₀) := by
      exact mul_le_mul_of_nonneg_left (sum_half_Ico_le_two_mul n₀ j (by omega)) (by positivity)

private lemma exists_small_real_power (A r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A * r ^ n ≤ 1 := by
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hlim : Tendsto (fun n : ℕ => A * r ^ n) atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have hev : ∀ᶠ n : ℕ in atTop, A * r ^ n < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N, fun n hn => (hN n hn).le⟩

private def metricDecayBase : ℝ := (4 : ℝ) ^ (-(1 / 50 : ℝ))
private def metricHeatBase : ℝ := (4 : ℝ) ^ (1.01 : ℝ)
private def metricAddCoeff (C : ℝ) : ℝ := 4 * (C + 1)
private def geometryOverlapCoeff (d : ℕ) (C : ℝ) : ℝ :=
  (8 * (d : ℝ) * (400 * C + 3)) ^ d
private def geometryHalfCutoffCoeff (d : ℕ) (C : ℝ) : ℝ :=
  1024 * (C + 1) + 8 * metricAddCoeff C +
    4 * (40 * (d : ℝ)) ^ d * 16 * (C + 1)
private def geometryGapCutoffCoeff (C : ℝ) : ℝ :=
  metricAddCoeff C * metricHeatBase * (2 : ℝ) ^ (1.03 : ℝ)

private theorem exists_geometry_cutoff (d : ℕ) (C : ℝ) :
    ∃ N : ℕ,
      (∀ n, N ≤ n → geometryHalfCutoffCoeff d C * (1 / 2 : ℝ) ^ n ≤ 1) ∧
      (∀ n, N ≤ n → geometryGapCutoffCoeff C * metricDecayBase ^ n ≤ 1) ∧
      1 ≤ N := by
  have hrho0 : 0 ≤ metricDecayBase := by
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _).le
  have hrho1 : metricDecayBase < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 4) (by norm_num [metricDecayBase])
  obtain ⟨N₁, hN₁⟩ := exists_small_real_power
    (geometryHalfCutoffCoeff d C) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := exists_small_real_power
    (geometryGapCutoffCoeff C) metricDecayBase hrho0 hrho1
  let N := max 1 (max N₁ N₂)
  refine ⟨N, ?_, ?_, ?_⟩
  · intro n hn
    apply hN₁ n
    exact (Nat.le_max_left N₁ N₂).trans ((Nat.le_max_right 1 (max N₁ N₂)).trans hn)
  · intro n hn
    apply hN₂ n
    exact (Nat.le_max_right N₁ N₂).trans ((Nat.le_max_right 1 (max N₁ N₂)).trans hn)
  · exact le_max_left _ _

private lemma four_ratio_metric_le_half_pow (k : ℕ) :
    (4 : ℝ) ^ (2 * k : ℕ) / (4 : ℝ) ^ (8 * k : ℕ) ≤ (1 / 2 : ℝ) ^ k := by
  have hdiff : 8 * k = 2 * k + 6 * k := by omega
  have hden : (4 : ℝ) ^ (8 * k : ℕ) =
      (4 : ℝ) ^ (2 * k : ℕ) * (4 : ℝ) ^ (6 * k : ℕ) := by
    rw [hdiff, pow_add]
  have hpow : (2 : ℝ) ^ k ≤ (4 : ℝ) ^ (6 * k : ℕ) := by
    calc
      (2 : ℝ) ^ k ≤ (4 : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) (by norm_num : (2 : ℝ) ≤ 4) k
      _ ≤ (4 : ℝ) ^ (6 * k : ℕ) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)
  rw [hden]
  have hrecip : 1 / (4 : ℝ) ^ (6 * k : ℕ) ≤ 1 / (2 : ℝ) ^ k :=
    one_div_le_one_div_of_le (by positivity) hpow
  calc
    (4 : ℝ) ^ (2 * k : ℕ) /
        ((4 : ℝ) ^ (2 * k : ℕ) * (4 : ℝ) ^ (6 * k : ℕ)) =
        1 / (4 : ℝ) ^ (6 * k : ℕ) := by field_simp
    _ ≤ 1 / (2 : ℝ) ^ k := hrecip
    _ = (1 / 2 : ℝ) ^ k := by rw [div_pow]; norm_num

private def prefixAnchorFinset {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) (s : ℕ) : Finset (Fin l) :=
  Finset.univ.filter fun a => T.index a < s

private def stageAnchorFinset {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) (s : ℕ) : Finset (Fin l) :=
  Finset.univ.filter fun a => T.index a = s

private def prefixTerms {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) (s : ℕ) : Finset (Torus d m) :=
  (prefixAnchorFinset T s).biUnion T.edits

private def stageTerms {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) (s : ℕ) : Finset (Torus d m) :=
  (stageAnchorFinset T s).biUnion T.edits

private lemma prefixTerms_succ {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) (s : ℕ) :
    prefixTerms T (s + 1) = prefixTerms T s ∪ stageTerms T s := by
  have hanchors : prefixAnchorFinset T (s + 1) =
      prefixAnchorFinset T s ∪ stageAnchorFinset T s := by
    ext a
    simp [prefixAnchorFinset, stageAnchorFinset]
    omega
  rw [prefixTerms, hanchors, Finset.union_biUnion, prefixTerms, stageTerms]

private lemma prefixTerms_first {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) : prefixTerms T n₀ = ∅ := by
  have hanchors : prefixAnchorFinset T n₀ = ∅ := by
    ext a
    simp only [prefixAnchorFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty]
    have hs := (T.stages a).1
    constructor
    · intro ha
      omega
    · intro h
      contradiction
  simp [prefixTerms, hanchors]

private lemma prefixTerms_last {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) :
    prefixTerms T (j + 1) = geometryTerminals T := by
  have hanchors : prefixAnchorFinset T (j + 1) = Finset.univ := by
    ext a
    simp only [prefixAnchorFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    have hs := (T.stages a).2
    constructor
    · intro _
      trivial
    · intro _
      omega
  simp [prefixTerms, geometryTerminals, hanchors]

private lemma metricHeatBase_pow (s : ℕ) :
    metricHeatBase ^ s = (4 : ℝ) ^ (1.01 * (s : ℝ)) := by
  unfold metricHeatBase
  symm
  exact Real.rpow_mul_natCast (by norm_num : 0 ≤ (4 : ℝ)) (1.01 : ℝ) s

private lemma metricHeatBase_pow_le (s : ℕ) :
    metricHeatBase ^ s ≤ (4 : ℝ) ^ (2 * s : ℕ) := by
  have hbase : metricHeatBase ≤ 16 := by
    unfold metricHeatBase
    have hexp : (1.01 : ℝ) ≤ 2 := by norm_num
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ (4 : ℝ)) hexp
    norm_num at hpow ⊢
    exact hpow
  have hbase_nonneg : 0 ≤ metricHeatBase := by
    unfold metricHeatBase
    positivity
  calc
    metricHeatBase ^ s ≤ (16 : ℝ) ^ s :=
      pow_le_pow_left₀ hbase_nonneg hbase s
    _ = (4 : ℝ) ^ (2 * s : ℕ) := by
      calc
        (16 : ℝ) ^ s = ((4 : ℝ) ^ 2) ^ s := by norm_num
        _ = (4 : ℝ) ^ (2 * s : ℕ) := by rw [pow_mul]

private lemma stageBudget_radius_ratio (C : ℝ) (hC : 1 ≤ C) (s : ℕ) :
    (stageBudget C s : ℝ) / (4 : ℝ) ^ (8 * s : ℕ) ≤
      16 * (C + 1) * (1 / 2 : ℝ) ^ s := by
  have hbudget := stageBudget_quadratic C hC s
  have hratio := four_ratio_metric_le_half_pow s
  calc
    (stageBudget C s : ℝ) / (4 : ℝ) ^ (8 * s : ℕ) ≤
        (16 * (C + 1) * (4 : ℝ) ^ (2 * s : ℕ)) /
          (4 : ℝ) ^ (8 * s : ℕ) :=
      div_le_div_of_nonneg_right hbudget (by positivity)
    _ = 16 * (C + 1) *
        ((4 : ℝ) ^ (2 * s : ℕ) / (4 : ℝ) ^ (8 * s : ℕ)) := by ring
    _ ≤ 16 * (C + 1) * (1 / 2 : ℝ) ^ s :=
      mul_le_mul_of_nonneg_left hratio (by positivity)

private lemma metric_stage_small {d s : ℕ} {C : ℝ}
    (hC : 1 ≤ C) (hsmall : geometryHalfCutoffCoeff d C * (1 / 2 : ℝ) ^ s ≤ 1) :
    256 * (C + 1) * (1 / 2 : ℝ) ^ s ≤ 1 / 4 ∧
    16 * (C + 1) * (1 / 2 : ℝ) ^ s ≤ 1 / 16 ∧
    metricAddCoeff C * (1 / 2 : ℝ) ^ s ≤ 1 / 8 ∧
    (40 * (d : ℝ)) ^ d * 16 * (C + 1) * (1 / 2 : ℝ) ^ s ≤ 1 / 4 := by
  have hD : 1024 * (C + 1) ≤ geometryHalfCutoffCoeff d C := by
    unfold geometryHalfCutoffCoeff
    have hCadd : 0 ≤ C + 1 := by linarith
    have hpos1 : 0 ≤ 8 * metricAddCoeff C := by
      rw [metricAddCoeff]
      positivity
    have hpos2 : 0 ≤ 4 * (40 * (d : ℝ)) ^ d * 16 * (C + 1) := by
      positivity [hCadd]
    linarith
  have hK : 4 * (40 * (d : ℝ)) ^ d * 16 * (C + 1) ≤
      geometryHalfCutoffCoeff d C := by
    unfold geometryHalfCutoffCoeff
    have hCadd : 0 ≤ C + 1 := by linarith
    have hpos : 0 ≤ 1024 * (C + 1) + 8 * metricAddCoeff C := by
      rw [metricAddCoeff]
      positivity [hCadd]
    linarith
  have hp : 0 ≤ (1 / 2 : ℝ) ^ s := by positivity
  have h1024 : 1024 * (C + 1) * (1 / 2 : ℝ) ^ s ≤ 1 := by
    calc
      1024 * (C + 1) * (1 / 2 : ℝ) ^ s ≤
          geometryHalfCutoffCoeff d C * (1 / 2 : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hD hp
      _ ≤ 1 := hsmall
  have hKsmall : (4 * (40 * (d : ℝ)) ^ d * 16 * (C + 1)) *
      (1 / 2 : ℝ) ^ s ≤ 1 := by
    calc
      (4 * (40 * (d : ℝ)) ^ d * 16 * (C + 1)) * (1 / 2 : ℝ) ^ s ≤
          geometryHalfCutoffCoeff d C * (1 / 2 : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hK hp
      _ ≤ 1 := hsmall
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [h1024]
  · nlinarith [h1024]
  · rw [metricAddCoeff]
    nlinarith [h1024]
  · nlinarith [hKsmall]

private lemma stage_target_lower (u : ℝ) (j m : ℕ)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j ≤ m) :
    (2 : ℝ) ^ (-1.03 : ℝ) * (4 : ℝ) ^ (1.03 * (j : ℝ)) ≤
      stageScale u j m ^ (-1.03 : ℝ) := by
  have hs := stage_scale_bounds u j m hu hjm
  have htpos : 0 < stageScale u j m := lt_trans (by positivity) hs.1
  have hupperPos : 0 < (2 : ℝ) / (4 : ℝ) ^ j := by positivity
  have hpow : ((2 : ℝ) / (4 : ℝ) ^ j) ^ (-1.03 : ℝ) ≤
      stageScale u j m ^ (-1.03 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos htpos hs.2 (by norm_num)
  have hden : ((4 : ℝ) ^ j) ^ (-1.03 : ℝ) =
      ((4 : ℝ) ^ (1.03 * (j : ℝ)))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (4 : ℝ))]
    rw [show (j : ℝ) * (-1.03 : ℝ) = -(1.03 * (j : ℝ)) by ring]
    rw [Real.rpow_neg_eq_inv_rpow]
    rw [Real.inv_rpow (by norm_num : 0 ≤ (4 : ℝ))]
  have hbase : ((2 : ℝ) / (4 : ℝ) ^ j) ^ (-1.03 : ℝ) =
      (2 : ℝ) ^ (-1.03 : ℝ) * (4 : ℝ) ^ (1.03 * (j : ℝ)) := by
    rw [Real.div_rpow (by norm_num) (by positivity)]
    rw [hden, div_eq_mul_inv, inv_inv]
  calc
    (2 : ℝ) ^ (-1.03 : ℝ) * (4 : ℝ) ^ (1.03 * (j : ℝ)) =
        ((2 : ℝ) / (4 : ℝ) ^ j) ^ (-1.03 : ℝ) := hbase.symm
    _ ≤ stageScale u j m ^ (-1.03 : ℝ) := hpow

private lemma stage_metric_additive_absorbed (C : ℝ) (j : ℕ)
    (hgap : geometryGapCutoffCoeff C * metricDecayBase ^ j ≤ 1) :
    metricAddCoeff C * metricHeatBase ^ (j + 1) ≤
      (2 : ℝ) ^ (-1.03 : ℝ) * (4 : ℝ) ^ (1.03 * (j : ℝ)) := by
  let gapBase : ℝ := (4 : ℝ) ^ (1 / 50 : ℝ)
  have hgapbase : metricHeatBase * gapBase = (4 : ℝ) ^ (1.03 : ℝ) := by
    unfold metricHeatBase gapBase
    have he : (1.03 : ℝ) = 1.01 + 1 / 50 := by norm_num
    rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
  have hrhogap : metricDecayBase * gapBase = 1 := by
    unfold metricDecayBase gapBase
    calc
      (4 : ℝ) ^ (-(1 / 50 : ℝ)) * (4 : ℝ) ^ (1 / 50 : ℝ) =
          (4 : ℝ) ^ (-(1 / 50 : ℝ) + 1 / 50 : ℝ) := by
            symm
            exact Real.rpow_add (by norm_num : (0 : ℝ) < 4) _ _
      _ = 1 := by norm_num
  have hcancel : metricDecayBase ^ j * gapBase ^ j = 1 := by
    calc
      metricDecayBase ^ j * gapBase ^ j = (metricDecayBase * gapBase) ^ j := by
        rw [← mul_pow]
      _ = 1 := by rw [hrhogap, one_pow]
  have hgapBound : geometryGapCutoffCoeff C ≤ gapBase ^ j := by
    calc
      geometryGapCutoffCoeff C =
          geometryGapCutoffCoeff C * (metricDecayBase ^ j * gapBase ^ j) := by
            rw [hcancel, mul_one]
      _ = (geometryGapCutoffCoeff C * metricDecayBase ^ j) * gapBase ^ j := by ring
      _ ≤ 1 * gapBase ^ j := mul_le_mul_of_nonneg_right hgap (by positivity)
      _ = gapBase ^ j := by ring
  have h2cancel : (2 : ℝ) ^ (1.03 : ℝ) * (2 : ℝ) ^ (-1.03 : ℝ) = 1 := by
    calc
      (2 : ℝ) ^ (1.03 : ℝ) * (2 : ℝ) ^ (-1.03 : ℝ) =
          (2 : ℝ) ^ (1.03 + (-1.03) : ℝ) := by
            symm
            exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
      _ = 1 := by norm_num
  have hgapPow : (4 : ℝ) ^ (1.03 * (j : ℝ)) =
      metricHeatBase ^ j * gapBase ^ j := by
    calc
      (4 : ℝ) ^ (1.03 * (j : ℝ)) = ((4 : ℝ) ^ (1.03 : ℝ)) ^ j :=
        Real.rpow_mul_natCast (by norm_num : 0 ≤ (4 : ℝ)) (1.03 : ℝ) j
      _ = (metricHeatBase * gapBase) ^ j := by rw [← hgapbase]
      _ = metricHeatBase ^ j * gapBase ^ j := by rw [mul_pow]
  have hfactor : 0 ≤ (2 : ℝ) ^ (-1.03 : ℝ) * metricHeatBase ^ j := by
    apply mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
    unfold metricHeatBase
    positivity
  have hmul := mul_le_mul_of_nonneg_right hgapBound hfactor
  calc
    metricAddCoeff C * metricHeatBase ^ (j + 1) =
        geometryGapCutoffCoeff C * ((2 : ℝ) ^ (-1.03 : ℝ) * metricHeatBase ^ j) := by
          unfold geometryGapCutoffCoeff metricAddCoeff
          rw [pow_succ]
          calc
            4 * (C + 1) * (metricHeatBase ^ j * metricHeatBase) =
                4 * (C + 1) * metricHeatBase *
                  ((2 : ℝ) ^ (1.03 : ℝ) * (2 : ℝ) ^ (-1.03 : ℝ)) * metricHeatBase ^ j := by
                    rw [h2cancel]
                    ring
            _ = (4 * (C + 1) * metricHeatBase * (2 : ℝ) ^ (1.03 : ℝ)) *
                ((2 : ℝ) ^ (-1.03 : ℝ) * metricHeatBase ^ j) := by ring
    _ ≤ gapBase ^ j * ((2 : ℝ) ^ (-1.03 : ℝ) * metricHeatBase ^ j) := hmul
    _ = (2 : ℝ) ^ (-1.03 : ℝ) * (4 : ℝ) ^ (1.03 * (j : ℝ)) := by
      rw [hgapPow]
      ring

private lemma torus_card_real (d m : ℕ) :
    (Fintype.card (Torus d m) : ℝ) = (OAI.Anderson.sideLength m : ℝ) ^ d := by
  exact_mod_cast OAI.Anderson.torus_card d m

private lemma sideLength_pow_real (d m : ℕ) :
    (OAI.Anderson.sideLength m : ℝ) ^ d = (4 : ℝ) ^ (20 * m * d : ℕ) := by
  rw [OAI.Anderson.sideLength]
  norm_cast
  exact (Nat.pow_mul 4 (20 * m) d).symm

private lemma stageScale_negNu_lt_half_torus (d m j : ℕ) (hd : 3 ≤ d)
    (hj : 1 ≤ j) (hjm : 2 * j ≤ m) (u : ℝ)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) :
    stageScale u j m ^ (-nu d) < (Fintype.card (Torus d m) : ℝ) / 2 := by
  have hs := stage_scale_bounds u j m hu (by omega)
  have htpos : 0 < stageScale u j m := lt_trans (by positivity) hs.1
  have hfour : 2 ≤ (4 : ℝ) ^ j := by
    calc
      2 ≤ 4 := by norm_num
      _ = (4 : ℝ) ^ 1 := by norm_num
      _ ≤ (4 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
  have hfrac : (2 : ℝ) / (4 : ℝ) ^ j ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ j)).2
    linarith
  have htle : stageScale u j m ≤ 1 := hs.2.trans hfrac
  have hnu : nu d ≤ 1 := by
    unfold nu delta
    have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
    have hden : 1 ≤ 100000 * (d : ℝ) := by nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 100000 * (d : ℝ))).2
    norm_num
    nlinarith
  have hExp : (-1 : ℝ) ≤ -nu d := by linarith
  have hnuLe : stageScale u j m ^ (-nu d) ≤ stageScale u j m ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge htpos htle hExp
  have hbase : (1 / 4 : ℝ) / (4 : ℝ) ^ j =
      ((4 : ℝ) ^ (j + 1 : ℕ))⁻¹ := by
    rw [pow_succ]
    field_simp
  have hbasePos : 0 < (1 / 4 : ℝ) / (4 : ℝ) ^ j := by positivity
  have hInv : stageScale u j m ^ (-1 : ℝ) < (4 : ℝ) ^ (j + 1 : ℕ) := by
    have hdiv := one_div_lt_one_div_of_lt hbasePos hs.1
    have htRpow : stageScale u j m ^ (-1 : ℝ) =
        1 / stageScale u j m := by
      rw [Real.rpow_neg_eq_inv_rpow]
      simp
    calc
      stageScale u j m ^ (-1 : ℝ) = 1 / stageScale u j m := htRpow
      _ < 1 / ((1 / 4 : ℝ) / (4 : ℝ) ^ j) := hdiv
      _ = (4 : ℝ) ^ (j + 1 : ℕ) := by rw [hbase]; simp
  have hexp : j + 2 ≤ 20 * m * d := by
    have hm2 : 2 ≤ m := by omega
    have hjm' : j ≤ m := by omega
    have hbaseExp : j + 2 ≤ 20 * m := by omega
    have hd1 : 1 ≤ d := by omega
    have hmul : 20 * m ≤ 20 * m * d := by
      simpa using Nat.mul_le_mul_left (20 * m) hd1
    exact hbaseExp.trans hmul
  have hpow : (4 : ℝ) ^ (j + 2 : ℕ) ≤ (4 : ℝ) ^ (20 * m * d : ℕ) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hexp
  have htwice : 2 * (4 : ℝ) ^ (j + 1 : ℕ) ≤ (4 : ℝ) ^ (j + 2 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left (by norm_num : (2 : ℝ) ≤ 4)
      (by positivity : 0 ≤ (4 : ℝ) ^ (j + 1 : ℕ))
    calc
      2 * (4 : ℝ) ^ (j + 1 : ℕ) ≤ (4 : ℝ) ^ (j + 1 : ℕ) * 4 := by nlinarith
      _ = (4 : ℝ) ^ (j + 2 : ℕ) := by rw [pow_succ]; ring
  have hvol : 2 * (4 : ℝ) ^ (j + 1 : ℕ) ≤
      (OAI.Anderson.sideLength m : ℝ) ^ d := by
    calc
      2 * (4 : ℝ) ^ (j + 1 : ℕ) ≤ (4 : ℝ) ^ (j + 2 : ℕ) := htwice
      _ ≤ (4 : ℝ) ^ (20 * m * d : ℕ) := hpow
      _ = (OAI.Anderson.sideLength m : ℝ) ^ d := (sideLength_pow_real d m).symm
  calc
    stageScale u j m ^ (-nu d) ≤ stageScale u j m ^ (-1 : ℝ) := hnuLe
    _ < (4 : ℝ) ^ (j + 1 : ℕ) := hInv
    _ ≤ (OAI.Anderson.sideLength m : ℝ) ^ d / 2 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa [mul_comm] using hvol)
    _ = (Fintype.card (Torus d m) : ℝ) / 2 := by rw [torus_card_real]

private lemma stageBudget_accumulation_step (C : ℝ) (hC : 1 ≤ C) (s : ℕ) :
    metricAddCoeff C * metricHeatBase ^ s + 2 * (stageBudget C s : ℝ) ≤
      metricAddCoeff C * metricHeatBase ^ (s + 1) := by
  have hstage : (stageBudget C s : ℝ) ≤
      (C + 1) * metricHeatBase ^ (s + 1) := by
    rw [metricHeatBase_pow]
    exact stageBudget_upper C hC s
  have hA : 0 ≤ C + 1 := by linarith
  have hbase : 2 ≤ metricHeatBase := by
    unfold metricHeatBase
    have hpow : (4 : ℝ) ^ (1 : ℝ) ≤ (4 : ℝ) ^ (1.01 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) (by norm_num)
    calc
      2 ≤ 4 := by norm_num
      _ = (4 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (4 : ℝ) ^ (1.01 : ℝ) := hpow
  have hpowpos : 0 ≤ metricHeatBase ^ s := by positivity
  have hX : 0 ≤ (C + 1) * metricHeatBase ^ s := mul_nonneg hA hpowpos
  have hmul : 4 * ((C + 1) * metricHeatBase ^ s) ≤
      2 * ((C + 1) * metricHeatBase ^ s) * metricHeatBase := by
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hbase)]
  have hmain : metricAddCoeff C * metricHeatBase ^ s +
      2 * ((C + 1) * metricHeatBase ^ (s + 1)) ≤
      metricAddCoeff C * metricHeatBase ^ (s + 1) := by
    rw [pow_succ, metricAddCoeff]
    nlinarith [hmul]
  have hfirst : metricAddCoeff C * metricHeatBase ^ s +
      2 * (stageBudget C s : ℝ) ≤
        metricAddCoeff C * metricHeatBase ^ s +
          2 * ((C + 1) * metricHeatBase ^ (s + 1)) := by
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hstage (by norm_num : 0 ≤ (2 : ℝ)))
  exact hfirst.trans hmain

private lemma stage_edits_separated {d m n₀ j l : ℕ} {u C : ℝ}
    (hm : 0 < m) (T : ClearingGeometry d m n₀ j l u C) (s : ℕ)
    (a b : Fin l) (hab : a ≠ b) (hsa : T.index a = s) (hsb : T.index b = s)
    (x : Torus d m) (hx : x ∈ T.edits a) (y : Torus d m) (hy : y ∈ T.edits b) :
    separationRadius s - inspectionRadius s ≤ physicalDistance d m x y := by
  obtain ⟨x₀, hx₀, hlocx⟩ := T.locations a x hx
  obtain ⟨y₀, hy₀, hlocy⟩ := T.locations b y hy
  have hcore := T.separated a b hab (by rw [hsa, hsb]) x₀ hx₀ y₀ hy₀
  have htri₁ := physicalDistance_triangle hm x₀ x y₀
  have htri₂ := physicalDistance_triangle hm x y y₀
  have hsym : physicalDistance d m x₀ x = physicalDistance d m x x₀ := by
    simp [physicalDistance, SimpleGraph.dist_comm]
  have htri : physicalDistance d m x₀ y₀ ≤
      physicalDistance d m x x₀ + physicalDistance d m x y + physicalDistance d m y y₀ := by
    calc
      physicalDistance d m x₀ y₀ ≤
          physicalDistance d m x₀ x + physicalDistance d m x y₀ := htri₁
      _ ≤ physicalDistance d m x₀ x +
          (physicalDistance d m x y + physicalDistance d m y y₀) :=
        add_le_add_right htri₂ _
      _ = physicalDistance d m x x₀ +
          physicalDistance d m x y + physicalDistance d m y y₀ := by rw [hsym]; ring
  have hlocx' : physicalDistance d m x x₀ ≤ inspectionRadius s / 2 := by
    simpa [hsa] using hlocx
  have hlocy' : physicalDistance d m y y₀ ≤ inspectionRadius s / 2 := by
    simpa [hsb] using hlocy
  have hcore' : separationRadius s < physicalDistance d m x₀ y₀ := by
    simpa [hsa] using hcore
  linarith

private theorem assembly_metric_bridge {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (G : SimpleGraph ι) (hconn : G.Connected) (T : Finset ι) (O : κ → Finset ι)
    (c μ R ℓ : ℝ) (M : ℕ) (hc : 0 < c) (hμ : 0 ≤ μ)
    (hold : ∀ u v, c * (G.dist u v : ℝ) - μ ≤ AndersonAC.S78.terminalDistance G T u v)
    (hsize : ∀ a, (O a).card ≤ M)
    (hsep : ∀ a a', a ≠ a' → ∀ u ∈ O a, ∀ v ∈ O a', R - 2 * ℓ ≤ (G.dist u v : ℝ))
    (hmargin : 2 * (M : ℝ) < c * (R - 2 * ℓ) - μ) :
    ∀ u v, c * (1 - 2 * (M : ℝ) / (c * (R - 2 * ℓ) - μ)) * (G.dist u v : ℝ) - μ - 2 * (M : ℝ) ≤
      AndersonAC.S78.terminalDistance G (T ∪ Finset.univ.biUnion O) u v := by
  exact AndersonAC.SolS78.assembly_metric_proof G hconn T O c μ R ℓ M hc hμ hold hsize hsep hmargin

private theorem clearing_metric_prefix {d m n₀ j l : ℕ} (hd : 3 ≤ d) (C : ℝ)
    (hC : 1 ≤ C) (hm : 0 < m) (u : ℝ) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (T : ClearingGeometry d m n₀ j l u C) (N : ℕ) (hN : N ≤ n₀)
    (hn₀ : 1 ≤ n₀) (hn₀j : n₀ ≤ j) (hjm : 2 * j ≤ m)
    (hhalf : ∀ n, N ≤ n →
      geometryHalfCutoffCoeff d C * (1 / 2 : ℝ) ^ n ≤ 1) :
    ∃ c μ, (∀ x y, c * physicalDistance d m x y - μ ≤
        AndersonAC.S78.terminalDistance (nnGraph d m) (prefixTerms T (j + 1)) x y) ∧
      3 / 4 ≤ c ∧ c ≤ 1 ∧ 0 ≤ μ ∧
      μ ≤ metricAddCoeff C * metricHeatBase ^ (j + 1) := by
  let loss : ℕ → ℝ := fun s => 256 * (C + 1) * (1 / 2 : ℝ) ^ s
  let P : ℕ → Prop := fun s => s ≤ j + 1 →
    ∃ c μ,
      (∀ x y, c * physicalDistance d m x y - μ ≤
        AndersonAC.S78.terminalDistance (nnGraph d m) (prefixTerms T s) x y) ∧
      1 - loss n₀ + loss s ≤ c ∧ c ≤ 1 ∧ 0 ≤ μ ∧
      μ ≤ metricAddCoeff C * metricHeatBase ^ s
  have hconn : (nnGraph d m).Connected := nnGraph_connected hm
  have hsmall₀ := metric_stage_small (d := d) (s := n₀) (C := C) hC (hhalf n₀ hN)
  have hE₀ : loss n₀ ≤ 1 / 4 := by simpa [loss] using hsmall₀.1
  have hrun : ∀ s, n₀ ≤ s → P s := by
    apply Nat.le_induction
    · intro hbound
      refine ⟨1, 0, ?_, ?_, le_rfl, by norm_num, ?_⟩
      · intro x y
        rw [prefixTerms_first T]
        rw [terminalDistance_empty_eq_dist (nnGraph d m) hconn x y]
        simp [physicalDistance]
      · calc
          1 - loss n₀ + loss n₀ = 1 := by ring
          _ ≤ 1 := le_rfl
      · have hB : 0 ≤ metricAddCoeff C := by
          unfold metricAddCoeff
          positivity
        have hbase0 : 0 ≤ metricHeatBase := by
          unfold metricHeatBase
          exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _).le
        have hbase : 0 ≤ metricHeatBase ^ n₀ := pow_nonneg hbase0 _
        exact mul_nonneg hB hbase
    · intro s hs ih hbound
      have hprevBound : s ≤ j + 1 := by omega
      rcases ih hprevBound with ⟨c, μ, hmetric, hclower, hcup, hμnonneg, hμbound⟩
      have hsj : s ≤ j := by omega
      have h2sm : 2 * s ≤ m := by omega
      have hsN : N ≤ s := hN.trans hs
      have hsmallS := metric_stage_small (d := d) (s := s) (C := C) hC (hhalf s hsN)
      rcases hsmallS with ⟨hstageE, hstageM, hstageMu, hstageVol⟩
      have hRpos : 0 < (4 : ℝ) ^ (8 * s : ℕ) := by positivity
      let R : ℝ := (4 : ℝ) ^ (8 * s : ℕ)
      let ell : ℝ := inspectionRadius s / 2
      have hRdef : R = separationRadius s := rfl
      have hinspPos : 0 < inspectionRadius s := by
        unfold inspectionRadius
        positivity
      have hinspLarge : 2 ≤ inspectionRadius s := by
        unfold inspectionRadius
        have hexp : 1 ≤ 4 * s := by omega
        calc
          2 ≤ 4 := by norm_num
          _ = (4 : ℝ) ^ 1 := by norm_num
          _ ≤ (4 : ℝ) ^ (4 * s : ℕ) :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hexp
      have hRfact : R = inspectionRadius s * inspectionRadius s := by
        dsimp [R, inspectionRadius]
        have hexp : 8 * s = (4 * s) * 2 := by omega
        rw [hexp, pow_mul]
        ring
      have hRhalf : R / 2 ≤ R - inspectionRadius s := by
        have hprod : 0 ≤ inspectionRadius s * (inspectionRadius s - 2) :=
          mul_nonneg (le_of_lt hinspPos) (by linarith)
        rw [hRfact]
        nlinarith [hprod]
      have hRminus : R / 2 ≤ R - 2 * ell := by
        calc
          R / 2 ≤ R - inspectionRadius s := hRhalf
          _ = R - 2 * ell := by dsimp [ell]; ring
      have hcLower : 3 / 4 ≤ c := by
        have hEs : 0 ≤ loss s := by positivity
        linarith
      have hcpos : 0 < c := by linarith
      have hbaseRatio : metricHeatBase ^ s / R ≤ (1 / 2 : ℝ) ^ s := by
        calc
          metricHeatBase ^ s / R ≤ (4 : ℝ) ^ (2 * s : ℕ) / R :=
            div_le_div_of_nonneg_right (metricHeatBase_pow_le s) (by positivity)
          _ = (4 : ℝ) ^ (2 * s : ℕ) / (4 : ℝ) ^ (8 * s : ℕ) := by rfl
          _ ≤ (1 / 2 : ℝ) ^ s := four_ratio_metric_le_half_pow s
      have hμRatio : μ / R ≤ metricAddCoeff C * (1 / 2 : ℝ) ^ s := by
        calc
          μ / R ≤ (metricAddCoeff C * metricHeatBase ^ s) / R :=
            div_le_div_of_nonneg_right hμbound (by positivity)
          _ = metricAddCoeff C * (metricHeatBase ^ s / R) := by ring
          _ ≤ metricAddCoeff C * (1 / 2 : ℝ) ^ s :=
            mul_le_mul_of_nonneg_left hbaseRatio (by
              unfold metricAddCoeff
              positivity)
      have hμR : μ ≤ R / 8 := by
        have hmul := (div_le_iff₀ hRpos).mp (hμRatio.trans hstageMu)
        nlinarith
      have hMratio : (stageBudget C s : ℝ) / R ≤
          16 * (C + 1) * (1 / 2 : ℝ) ^ s := by
        simpa [R] using stageBudget_radius_ratio C hC s
      have hMR : (stageBudget C s : ℝ) / R ≤ 1 / 16 :=
        hMratio.trans hstageM
      have hMle : 2 * (stageBudget C s : ℝ) ≤ R / 8 := by
        have hmul := (div_le_iff₀ hRpos).mp hMR
        nlinarith
      have hL : R / 4 ≤ c * (R - 2 * ell) - μ := by
        have hterm₁ := mul_le_mul_of_nonneg_right hcLower (by positivity : 0 ≤ R / 2)
        have hterm₂ := mul_le_mul_of_nonneg_left hRminus (le_of_lt hcpos)
        nlinarith
      have hLpos : 0 < c * (R - 2 * ell) - μ := by
        exact lt_of_lt_of_le (by positivity : (0 : ℝ) < R / 4) hL
      have hmargin : 2 * (stageBudget C s : ℝ) < c * (R - 2 * ell) - μ := by
        have hstrict : R / 8 < R / 4 := by nlinarith [hRpos]
        linarith
      let O : Fin l → Finset (Torus d m) := fun a =>
        if T.index a = s then T.edits a else ∅
      have hO : Finset.univ.biUnion O = stageTerms T s := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hx⟩
          have hidx : T.index a = s := by
            by_contra hidx
            simp [O, hidx] at hx
          have hx' : x ∈ T.edits a := by simpa [O, hidx] using hx
          change x ∈ (stageAnchorFinset T s).biUnion T.edits
          exact Finset.mem_biUnion.mpr ⟨a,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hidx⟩, hx'⟩
        · intro hx
          change x ∈ (stageAnchorFinset T s).biUnion T.edits at hx
          rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hx⟩
          have hidx : T.index a = s := (Finset.mem_filter.mp ha).2
          apply Finset.mem_biUnion.mpr
          exact ⟨a, Finset.mem_univ _, by simpa [O, hidx] using hx⟩
      have hsize : ∀ a, (O a).card ≤ stageBudget C s := by
        intro a
        by_cases hsa : T.index a = s
        · have hidx₁ : 1 ≤ T.index a := by omega
          have hidxm : T.index a ≤ m := by omega
          simpa [O, hsa] using
            (stage_edit_card_le_budget hd C hC u hu T a hidx₁ hidxm)
        · simp [O, hsa]
      have hsep : ∀ a a', a ≠ a' → ∀ x ∈ O a, ∀ y ∈ O a',
          R - 2 * ell ≤ physicalDistance d m x y := by
        intro a b hab x hx y hy
        by_cases hsa : T.index a = s
        · by_cases hsb : T.index b = s
          · have hxedit : x ∈ T.edits a := by simpa [O, hsa] using hx
            have hyedit : y ∈ T.edits b := by simpa [O, hsb] using hy
            have hse := stage_edits_separated hm T s a b hab hsa hsb x hxedit y hyedit
            calc
              R - 2 * ell = separationRadius s - inspectionRadius s := by
                dsimp [R, ell, separationRadius, inspectionRadius]
                ring
              _ ≤ physicalDistance d m x y := hse
          · have hfalse : False := by simpa [O, hsb] using hy
            exact False.elim hfalse
        · have hfalse : False := by simpa [O, hsa] using hx
          exact False.elim hfalse
      have hbaseMetric : ∀ x y,
          c * physicalDistance d m x y - μ ≤
            AndersonAC.S78.terminalDistance (nnGraph d m) (prefixTerms T s) x y := hmetric
      have hass : ∀ x y,
          c * (1 - 2 * (stageBudget C s : ℝ) /
            (c * (R - 2 * ell) - μ)) * physicalDistance d m x y - μ -
              2 * (stageBudget C s : ℝ) ≤
            AndersonAC.S78.terminalDistance (nnGraph d m)
              (prefixTerms T s ∪ Finset.univ.biUnion O) x y := by
        intro x y
        have hbridge := assembly_metric_bridge (nnGraph d m) hconn (prefixTerms T s) O c μ R ell
          (stageBudget C s) hcpos hμnonneg hbaseMetric hsize hsep hmargin x y
        simpa [physicalDistance] using hbridge
      have hupdate : prefixTerms T (s + 1) =
          prefixTerms T s ∪ Finset.univ.biUnion O := by
        rw [prefixTerms_succ, hO]
      let q : ℝ := 2 * (stageBudget C s : ℝ) / (c * (R - 2 * ell) - μ)
      let c' : ℝ := c * (1 - q)
      let μ' : ℝ := μ + 2 * (stageBudget C s : ℝ)
      have hqnonneg : 0 ≤ q := by
        dsimp [q]
        exact div_nonneg (by positivity) (le_of_lt hLpos)
      have hqsmall : q ≤ 8 * (stageBudget C s : ℝ) / R := by
        apply (div_le_iff₀ hLpos).2
        have hcoefpos : 0 ≤ 8 * (stageBudget C s : ℝ) / R := by
          have hMnonneg : 0 ≤ (stageBudget C s : ℝ) := Nat.cast_nonneg _
          exact div_nonneg (mul_nonneg (by norm_num) hMnonneg) hRpos.le
        have hmul := mul_le_mul_of_nonneg_left hL hcoefpos
        have hRne : R ≠ 0 := ne_of_gt (by simpa [R] using hRpos)
        have heq : (8 * (stageBudget C s : ℝ) / R) * (R / 4) =
            2 * (stageBudget C s : ℝ) := by
          calc
            (8 * (stageBudget C s : ℝ) / R) * (R / 4) =
                (8 * (stageBudget C s : ℝ)) * (R⁻¹ * R) / 4 := by ring
            _ = (8 * (stageBudget C s : ℝ)) * 1 / 4 := by
              rw [inv_mul_cancel₀ hRne]
            _ = 2 * (stageBudget C s : ℝ) := by ring
        calc
          2 * (stageBudget C s : ℝ) =
              (8 * (stageBudget C s : ℝ) / R) * (R / 4) := heq.symm
          _ ≤ (8 * (stageBudget C s : ℝ) / R) *
              (c * (R - 2 * ell) - μ) := hmul
      have hqLoss : q ≤ 128 * (C + 1) * (1 / 2 : ℝ) ^ s := by
        calc
          q ≤ 8 * (stageBudget C s : ℝ) / R := hqsmall
          _ = 8 * ((stageBudget C s : ℝ) / R) := by ring
          _ ≤ 8 * (16 * (C + 1) * (1 / 2 : ℝ) ^ s) :=
            mul_le_mul_of_nonneg_left hMratio (by norm_num)
          _ = 128 * (C + 1) * (1 / 2 : ℝ) ^ s := by ring
      have hdecr : c - q ≤ c' := by
        dsimp [c']
        have hmul : c * q ≤ q := by
          have := mul_le_mul_of_nonneg_right hcup hqnonneg
          linarith
        calc
          c - q ≤ c - c * q := by linarith
          _ = c * (1 - q) := by ring
      have hLossEq : loss s = 128 * (C + 1) * (1 / 2 : ℝ) ^ s + loss (s + 1) := by
        dsimp [loss]
        rw [pow_succ]
        ring
      have hclower' : 1 - loss n₀ + loss (s + 1) ≤ c' := by
        have hstage₁ : 1 - loss n₀ + loss (s + 1) ≤
            c - 128 * (C + 1) * (1 / 2 : ℝ) ^ s := by
          linarith [hclower, hLossEq]
        have hstage₂ : c - 128 * (C + 1) * (1 / 2 : ℝ) ^ s ≤ c - q := by
          linarith [hqLoss]
        have hstage : 1 - loss n₀ + loss (s + 1) ≤ c - q := hstage₁.trans hstage₂
        exact hstage.trans hdecr
      have hq_lt : q < 1 := by
        dsimp [q]
        exact (div_lt_one hLpos).2 hmargin
      have hcup' : c' ≤ 1 := by
        have hfactor : 1 - q ≤ 1 := by linarith
        have hcnonneg : 0 ≤ c := by linarith
        have hle := mul_le_mul_of_nonneg_left hfactor hcnonneg
        have hle' : c' ≤ c := by
          dsimp [c']
          calc
            c * (1 - q) ≤ c * 1 := hle
            _ = c := by ring
        exact hle'.trans hcup
      have hμ'nonneg : 0 ≤ μ' := by positivity
      have hμ'bound : μ' ≤ metricAddCoeff C * metricHeatBase ^ (s + 1) := by
        dsimp [μ']
        exact (add_le_add hμbound le_rfl).trans (stageBudget_accumulation_step C hC s)
      have hmetric' : ∀ x y,
          c' * physicalDistance d m x y - μ' ≤
            AndersonAC.S78.terminalDistance (nnGraph d m) (prefixTerms T (s + 1)) x y := by
        intro x y
        rw [hupdate]
        have h := hass x y
        convert h using 1 <;> dsimp [c', μ', q] <;> ring
      exact ⟨c', μ', hmetric', hclower', hcup', hμ'nonneg, hμ'bound⟩
  rcases hrun (j + 1) (by omega) (le_rfl) with
    ⟨c, μ, hmetric, hclower, hcup, hμnonneg, hμbound⟩
  have hEs : 0 ≤ loss (j + 1) := by positivity
  have hc : 3 / 4 ≤ c := by
    have hE₀' := hE₀
    linarith
  exact ⟨c, μ, by simpa [prefixTerms_last] using hmetric, hc, hcup, hμnonneg, hμbound⟩

def UniformClearingGeometryContract (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) : Prop :=
  ∃ N : ℕ, ∃ C' : ℝ, 0 < C' ∧ ∀ (m n₀ j l : ℕ) (u : ℝ),
    N ≤ n₀ → n₀ ≤ j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    ∀ T : ClearingGeometry d m n₀ j l u C,
    (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
      AndersonAC.S78.terminalDistance (nnGraph d m) (geometryTerminals T) x y) ∧
    Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ geometryTerminals T).card ∧
    (∀ a, T.index a = j → (T.core a \ geometryTerminals T).card <
      (Finset.univ \ geometryTerminals T).card) ∧
    (∀ x, ((Finset.univ.filter fun a => T.index a = j ∧ x ∈ cube d m (T.anchor a)
        (200 * C * stageScale u j m ^ (-nu d) * separationRadius j)).card : ℝ) ≤
      C' * stageScale u j m ^ (-(d : ℝ) * nu d))

theorem clearing_locality_of_uniform_geometry
    (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C)
    (hgeometry : UniformClearingGeometryContract d hd C hC) :
    ∃ N : ℕ, ∀ (m n₀ j q : ℕ) (u : ℝ) (B : Finset (Torus d m))
      (pivot : Fin q → Torus d m) (T : Fin (q + 1) → Finset (Torus d m)),
      N ≤ n₀ → n₀ ≤ j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      (∀ a, (∀ i : Fin q, i.val < a.val → ∃ y ∈ B,
          physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) →
        ∃ l : ℕ, ∃ trace : ClearingGeometry d m n₀ j l u C, T a = geometryTerminals trace) →
      (∀ i : Fin q,
        (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
          AndersonAC.S78.terminalDistance (nnGraph d m) (T i.castSucc) x y) →
        ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) →
      (∀ i, ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) ∧
      (∀ a x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        AndersonAC.S78.terminalDistance (nnGraph d m) (T a) x y) ∧
      (∀ a, Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ T a).card) := by
  rcases hgeometry with ⟨N, C', hC', hgeometry⟩
  refine ⟨N, ?_⟩
  intro m n₀ j q u B pivot T hn hj hscheduled hu hrepresentation hselection
  have htrace (a : Fin (q + 1))
      (hprefix : ∀ i : Fin q, i.val < a.val →
        ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) :
      (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        AndersonAC.S78.terminalDistance (nnGraph d m) (T a) x y) ∧
        Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ T a).card := by
    rcases hrepresentation a hprefix with ⟨l, trace, hT⟩
    rcases hgeometry m n₀ j l u hn hj hscheduled hu trace with ⟨hmetric, hcount, _, _⟩
    constructor
    · simpa [hT] using hmetric
    · simpa [hT] using hcount
  have hmain : ∀ a : Fin (q + 1),
      (∀ i : Fin q, i.val < a.val →
        ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) ∧
      (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        AndersonAC.S78.terminalDistance (nnGraph d m) (T a) x y) ∧
      Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ T a).card := by
    intro a
    induction a using Fin.induction with
    | zero =>
        have hprefix : ∀ i : Fin q, i.val < 0 →
            ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2 := by
          intro i hi
          omega
        rcases htrace 0 hprefix with ⟨hm, hc⟩
        exact ⟨hprefix, hm, hc⟩
    | succ i ih =>
        have hloc : ∃ y ∈ B,
            physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2 := by
          exact hselection i ih.2.1
        have hprefix' : ∀ r : Fin q, r.val < (i.succ).val →
            ∃ y ∈ B, physicalDistance d m (pivot r) y ≤ inspectionRadius j / 2 := by
          intro r hr
          by_cases hri : r.val < i.val
          · exact ih.1 r hri
          · have hrlt : r.val < i.val + 1 := by simpa using hr
            have hval : r.val = i.val := by omega
            have hriEq : r = i := Fin.ext hval
            rw [hriEq]
            simpa using hloc
        rcases htrace i.succ hprefix' with ⟨hm, hc⟩
        exact ⟨hprefix', hm, hc⟩
  rcases hmain (Fin.last q) with ⟨_, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hselection i (hmain i.castSucc).2.1
  · intro a x y
    exact (hmain a).2.1 x y
  · intro a
    exact (hmain a).2.2

/-- Lemma 7.2, assertions (1),(3): exact frozen type of `S78.uniform_clearing_geometry`. -/
theorem uniform_clearing_geometry_proof (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∃ C' : ℝ, 0 < C' ∧ ∀ (m n₀ j l : ℕ) (u : ℝ),
      N ≤ n₀ → n₀ ≤ j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ T : ClearingGeometry d m n₀ j l u C,
      (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        AndersonAC.S78.terminalDistance (nnGraph d m) (geometryTerminals T) x y) ∧
      Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ geometryTerminals T).card ∧
      (∀ a, T.index a = j → (T.core a \ geometryTerminals T).card <
        (Finset.univ \ geometryTerminals T).card) ∧
      (∀ x, ((Finset.univ.filter fun a => T.index a = j ∧ x ∈ cube d m (T.anchor a)
          (200 * C * stageScale u j m ^ (-nu d) * separationRadius j)).card : ℝ) ≤
        C' * stageScale u j m ^ (-(d : ℝ) * nu d)) := by
  classical
  obtain ⟨N, hhalf, hgap, hN1⟩ := exists_geometry_cutoff d C
  have hCpos : 0 < geometryOverlapCoeff d C := by
    unfold geometryOverlapCoeff
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hbase : 0 < 8 * (d : ℝ) * (400 * C + 3) := by
      have : 0 < 400 * C + 3 := by linarith
      positivity
    exact pow_pos hbase d
  refine ⟨N, geometryOverlapCoeff d C, hCpos, ?_⟩
  intro m n₀ j l u hN hn₀j hsched hu T
  have hj1 : 1 ≤ j := by omega
  have hjm : 2 * j ≤ m := by
    unfold clearingScheduled at hsched
    omega
  have hm : 0 < m := by omega
  have hn₀ : 1 ≤ n₀ := by omega
  have hs := stage_scale_bounds u j m hu (by omega)
  have htpos : 0 < stageScale u j m := lt_trans (by positivity) hs.1
  have hfour : 2 ≤ (4 : ℝ) ^ j := by
    calc
      (2 : ℝ) ≤ 4 := by norm_num
      _ = (4 : ℝ) ^ 1 := by norm_num
      _ ≤ (4 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj1
  have htle : stageScale u j m ≤ 1 := by
    refine hs.2.trans ?_
    apply (div_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ j)).2
    linarith
  -- active volume
  have hcount : Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ geometryTerminals T).card := by
    have hfrac := terminal_card_fraction_bound hd C hC hn₀ hn₀j hjm u hu T
    have hsmall := (metric_stage_small (d := d) hC (hhalf n₀ hN)).2.2.2
    have hL : 0 ≤ (OAI.Anderson.sideLength m : ℝ) ^ d := by positivity
    have hcardR : 2 * ((geometryTerminals T).card : ℝ) ≤ (Fintype.card (Torus d m) : ℝ) := by
      rw [torus_card_real]
      have h2 : (40 * (d : ℝ)) ^ d * 16 * (C + 1) * (OAI.Anderson.sideLength m : ℝ) ^ d *
          (2 * (1 / 2 : ℝ) ^ n₀) =
          2 * ((OAI.Anderson.sideLength m : ℝ) ^ d *
            ((40 * (d : ℝ)) ^ d * 16 * (C + 1) * (1 / 2 : ℝ) ^ n₀)) := by ring
      have h3 : (OAI.Anderson.sideLength m : ℝ) ^ d *
          ((40 * (d : ℝ)) ^ d * 16 * (C + 1) * (1 / 2 : ℝ) ^ n₀) ≤
          (OAI.Anderson.sideLength m : ℝ) ^ d * (1 / 4) :=
        mul_le_mul_of_nonneg_left hsmall hL
      nlinarith
    have hcardN : 2 * (geometryTerminals T).card ≤ Fintype.card (Torus d m) := by
      exact_mod_cast hcardR
    have hsd : (Finset.univ \ geometryTerminals T).card =
        Fintype.card (Torus d m) - (geometryTerminals T).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    rw [hsd]
    omega
  refine ⟨?_, hcount, ?_, ?_⟩
  · -- metric
    obtain ⟨c, μ, hmet, hc34, _hc1, _hμ0, hμ⟩ :=
      clearing_metric_prefix hd C hC hm u hu T N hN hn₀ hn₀j hjm hhalf
    have habs := stage_metric_additive_absorbed C j (hgap j (le_trans hN hn₀j))
    have htarget := stage_target_lower u j m hu (by omega)
    intro x y
    have hxy := hmet x y
    rw [prefixTerms_last] at hxy
    have hdist : 0 ≤ physicalDistance d m x y := by
      unfold physicalDistance
      positivity
    have hcd : physicalDistance d m x y / 2 ≤ c * physicalDistance d m x y := by
      nlinarith
    linarith
  · -- core exterior
    intro a ha
    have hcore := T.eligible a
    rw [ha] at hcore
    have hlt := stageScale_negNu_lt_half_torus d m j hd hj1 hjm u hu
    have hsub : (T.core a \ geometryTerminals T).card ≤ (T.core a).card :=
      Finset.card_le_card Finset.sdiff_subset
    have hcountR : (Fintype.card (Torus d m) : ℝ) ≤
        2 * ((Finset.univ \ geometryTerminals T).card : ℝ) := by
      exact_mod_cast hcount
    have hsubR : ((T.core a \ geometryTerminals T).card : ℝ) ≤ ((T.core a).card : ℝ) := by
      exact_mod_cast hsub
    have hfinal : ((T.core a \ geometryTerminals T).card : ℝ) <
        ((Finset.univ \ geometryTerminals T).card : ℝ) := by
      linarith
    exact_mod_cast hfinal
  · -- halo overlap
    intro x
    have h := halo_overlap_bound hd C hC hm u hj1 hjm hu T htpos htle x
    simpa [geometryOverlapCoeff] using h

/-- Lemma 7.2 assertion (2): exact frozen type of `S78.clearing_locality`. -/
theorem clearing_locality_proof (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ (m n₀ j q : ℕ) (u : ℝ) (B : Finset (Torus d m))
      (pivot : Fin q → Torus d m) (T : Fin (q + 1) → Finset (Torus d m)),
      N ≤ n₀ → n₀ ≤ j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      (∀ a, (∀ i : Fin q, i.val < a.val → ∃ y ∈ B,
          physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) →
        ∃ l : ℕ, ∃ trace : ClearingGeometry d m n₀ j l u C, T a = geometryTerminals trace) →
      (∀ i : Fin q,
        (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
          AndersonAC.S78.terminalDistance (nnGraph d m) (T i.castSucc) x y) →
        ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) →
      (∀ i, ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) ∧
      (∀ a x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        AndersonAC.S78.terminalDistance (nnGraph d m) (T a) x y) ∧
      (∀ a, Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ T a).card) :=
  clearing_locality_of_uniform_geometry d hd C hC (uniform_clearing_geometry_proof d hd C hC)

end AndersonAC.SolS78
