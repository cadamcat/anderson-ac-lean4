import AndersonAC.S78.Definitions

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78AnchorTail

open AndersonAC.S78

private theorem nnGraph_connected (d m : ℕ) : (nnGraph d m).Connected := by
  classical
  by_cases hm : m = 0
  · subst m
    letI : Subsingleton (ZMod (OAI.Anderson.sideLength 0)) :=
      ZMod.subsingleton_iff.mpr (by simp [OAI.Anderson.sideLength])
    letI : Subsingleton (Torus d 0) := inferInstance
    have hpre : (nnGraph d 0).Preconnected := by
      intro x y
      have hxy : x = y := Subsingleton.elim _ _
      subst y
      exact SimpleGraph.Reachable.refl x
    letI : Nonempty (Torus d 0) := ⟨0⟩
    exact ⟨hpre⟩
  · have hn : 2 ≤ OAI.Anderson.sideLength m := by
      dsimp [OAI.Anderson.sideLength]
      have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hexp : 1 ≤ 20 * m := by omega
      calc
        2 ≤ 4 := by norm_num
        _ = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (20 * m) := Nat.pow_le_pow_right (by omega) hexp
    let G := nnGraph d m
    have hsingle (x : Torus d m) (i : Fin d)
        (a : ZMod (OAI.Anderson.sideLength m)) :
        G.Reachable x (x + Pi.single i a) := by
      have hb : OAI.Anderson.torusBasisVector i ≠ (0 : Torus d m) := by
        intro h
        have hcoord : ((1 : ℕ) : ZMod (OAI.Anderson.sideLength m)) = 0 := by
          simpa [OAI.Anderson.torusBasisVector] using congrFun h i
        have hval : 1 % OAI.Anderson.sideLength m = 0 := by
          simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val hcoord
        have hlt : 1 < OAI.Anderson.sideLength m := by omega
        have hmod : 1 % OAI.Anderson.sideLength m = 1 := Nat.mod_eq_of_lt hlt
        omega
      have hstep (z : Torus d m) :
          G.Adj z (z + OAI.Anderson.torusBasisVector i) := by
        have hne : z ≠ z + OAI.Anderson.torusBasisVector i := by
          intro h
          apply hb
          have hc : z + OAI.Anderson.torusBasisVector i = z + 0 := by simpa using h.symm
          exact add_left_cancel hc
        apply (SimpleGraph.fromRel_adj _ _ _).2
        refine ⟨hne, Or.inl ?_⟩
        exact ⟨i, Or.inl rfl⟩
      have hsteps (z : Torus d m) (k : ℕ) :
          G.Reachable z (z + k • OAI.Anderson.torusBasisVector i) := by
        induction k with
        | zero => simp
        | succ k ih =>
            have hadj := hstep (z + k • OAI.Anderson.torusBasisVector i)
            have htarget :
                (z + k • OAI.Anderson.torusBasisVector i) + OAI.Anderson.torusBasisVector i =
                  z + (k + 1) • OAI.Anderson.torusBasisVector i := by
              ext j
              simp only [Pi.add_apply, Pi.smul_apply]
              ring
            rw [htarget] at hadj
            exact ih.trans hadj.reachable
      have hvec : a.val • OAI.Anderson.torusBasisVector i = Pi.single i a := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [OAI.Anderson.torusBasisVector]
        · simp [OAI.Anderson.torusBasisVector, hji]
      rw [← hvec]
      exact hsteps x a.val
    have hall (z : Torus d m) : ∀ x, G.Reachable x (x + z) := by
      apply Pi.single_induction (p := fun z => ∀ x, G.Reachable x (x + z)) z
      · intro x
        simp
      · intro f g hf hg x
        exact (hf x).trans (by simpa [add_assoc] using hg (x + f))
      · intro i a x
        exact hsingle x i a
    have hpre : (nnGraph d m).Preconnected := by
      intro x y
      have h := hall (y - x) x
      change G.Reachable x y
      simpa using h
    letI : Nonempty (Torus d m) := ⟨0⟩
    exact ⟨hpre⟩

theorem physicalDistance_triangle (d m : ℕ)
    (x y z : Torus d m) :
    physicalDistance d m x z ≤ physicalDistance d m x y + physicalDistance d m y z := by
  change ((nnGraph d m).dist x z : ℝ) ≤
    ((nnGraph d m).dist x y : ℝ) + ((nnGraph d m).dist y z : ℝ)
  exact_mod_cast (nnGraph_connected d m).dist_triangle (u := x) (v := y) (w := z)

private theorem coord_edge_small {d m : ℕ} (i : Fin d) {x y : Torus d m}
    (hxy : (nnGraph d m).Adj x y) :
    (x i - y i).valMinAbs.natAbs ≤ 1 := by
  have hone : (1 : ZMod (OAI.Anderson.sideLength m)).valMinAbs.natAbs ≤ 1 := by
    rw [ZMod.valMinAbs_natAbs_eq_min]
    rw [ZMod.val_one_eq_one_mod]
    exact (Nat.min_le_left _ _).trans (Nat.mod_le _ _)
  have hneg : (-1 : ZMod (OAI.Anderson.sideLength m)).valMinAbs.natAbs ≤ 1 := by
    rw [ZMod.natAbs_valMinAbs_neg]
    exact hone
  have hrel : ∃ j : Fin d,
      y = x + OAI.Anderson.torusBasisVector j ∨
        y = x - OAI.Anderson.torusBasisVector j := by
    rcases (SimpleGraph.fromRel_adj _ _ _).1 hxy with ⟨_, hxy | hyx⟩
    · exact hxy
    · rcases hyx with ⟨j, h | h⟩
      · refine ⟨j, Or.inr ?_⟩
        rw [h]
        abel
      · refine ⟨j, Or.inl ?_⟩
        rw [h]
        abel
  rcases hrel with ⟨j, hmove | hmove⟩
  · rw [hmove]
    by_cases hij : i = j
    · subst j
      simpa [OAI.Anderson.torusBasisVector] using hneg
    · simp [OAI.Anderson.torusBasisVector, hij]
  · rw [hmove]
    by_cases hij : i = j
    · subst j
      simpa [OAI.Anderson.torusBasisVector] using hone
    · simp [OAI.Anderson.torusBasisVector, hij]

private theorem coord_abs_le_walk {d m : ℕ} (i : Fin d) {x y : Torus d m}
    (p : (nnGraph d m).Walk x y) :
    (x i - y i).valMinAbs.natAbs ≤ p.length := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    have hsplit : x i - z i = (x i - y i) + (y i - z i) := by abel
    rw [hsplit]
    calc
      ((x i - y i) + (y i - z i)).valMinAbs.natAbs ≤
          (x i - y i).valMinAbs.natAbs + (y i - z i).valMinAbs.natAbs :=
        (ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)
      _ ≤ 1 + p.length := Nat.add_le_add (coord_edge_small i hxy) ih
      _ = (SimpleGraph.Walk.cons hxy p).length := by simp [Nat.add_comm]

private theorem coord_abs_le_dist {d m : ℕ} (i : Fin d) (x y : Torus d m) :
    (x i - y i).valMinAbs.natAbs ≤ (nnGraph d m).dist x y := by
  obtain ⟨p, hp⟩ := (nnGraph_connected d m).exists_walk_length_eq_dist x y
  rw [← hp]
  exact coord_abs_le_walk i p

theorem coordNat_le_physicalDistance {d m : ℕ} (i : Fin d)
    (x y : Torus d m) :
    (min ((x i - y i).val) (OAI.Anderson.sideLength m - (x i - y i).val) : ℕ) ≤
      physicalDistance d m x y := by
  rw [← ZMod.valMinAbs_natAbs_eq_min]
  unfold physicalDistance
  exact_mod_cast coord_abs_le_dist i x y

end AndersonAC.SolS78AnchorTail
