import AndersonAC.S78.Definitions

open scoped BigOperators

namespace AndersonAC.SolS78

open AndersonAC.S78

private theorem nnGraph_connected (d m : ℕ) :
    (nnGraph d m).Connected := by
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

private theorem physicalDistance_comm (d m : ℕ) (x y : Torus d m) :
    physicalDistance d m x y = physicalDistance d m y x := by
  simp [physicalDistance, SimpleGraph.dist_comm]

private theorem physicalDistance_triangle (d m : ℕ)
    (x y z : Torus d m) :
    physicalDistance d m x z ≤ physicalDistance d m x y + physicalDistance d m y z := by
  change ((nnGraph d m).dist x z : ℝ) ≤
    ((nnGraph d m).dist x y : ℝ) + ((nnGraph d m).dist y z : ℝ)
  exact_mod_cast (nnGraph_connected d m).dist_triangle (u := x) (v := y) (w := z)

private theorem witness_support_aux (d m n₀ j : ℕ) (x : Torus d m)
    (L : Finset (BirthLabel (Torus d m))) (h : IsWitness d m n₀ j x L) :
    (∀ a ∈ L, physicalDistance d m x a.anchor ≤ witnessRadius j) ∧
      (∀ a ∈ L, n₀ < a.scale ∧ a.scale ≤ j) := by
  induction h with
  | leaf j x a hj hs hnear =>
      rcases hs with ⟨hscale, hle, _⟩
      constructor
      · intro b hb
        have hb' : b = a := by simpa using hb
        subst b
        have hrad : 0 ≤ witnessRadius j := by
          unfold witnessRadius
          exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 4) _)
        linarith
      · intro b hb
        have hb' : b = a := by simpa using hb
        subst b
        exact ⟨hscale, hle⟩
  | @branch j x hj hr hdec centers leaves hnear hsep children ih =>
      have hradChild : witnessRadius (historyEarlier d j) ≤ witnessRadius j / 2 := by
        have hexp : 10 * historyEarlier d j + 1 ≤ 10 * j := by omega
        have hpow :
            (4 : ℝ) ^ (10 * historyEarlier d j) * 4 ≤ (4 : ℝ) ^ (10 * j) := by
          calc
            (4 : ℝ) ^ (10 * historyEarlier d j) * 4 =
                (4 : ℝ) ^ (10 * historyEarlier d j + 1) := by rw [pow_succ]
            _ ≤ (4 : ℝ) ^ (10 * j) :=
              pow_le_pow_right₀ (by norm_num) hexp
        have hpowR : witnessRadius (historyEarlier d j) * 4 ≤ witnessRadius j := by
          simpa [witnessRadius] using hpow
        have hrad : 0 ≤ witnessRadius (historyEarlier d j) := by
          unfold witnessRadius
          exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 4) _)
        have htwice : 2 * witnessRadius (historyEarlier d j) ≤ witnessRadius j := by
          calc
            2 * witnessRadius (historyEarlier d j) ≤
                witnessRadius (historyEarlier d j) * 4 := by nlinarith
            _ ≤ witnessRadius j := hpowR
        nlinarith
      constructor
      · intro a ha
        rcases Finset.mem_biUnion.mp ha with ⟨i, _, hia⟩
        have hchild := (ih i).1 a hia
        calc
          physicalDistance d m x a.anchor ≤
              physicalDistance d m x (centers i) +
                physicalDistance d m (centers i) a.anchor :=
            physicalDistance_triangle d m x (centers i) a.anchor
          _ ≤ witnessRadius j / 2 + witnessRadius (historyEarlier d j) :=
            add_le_add (hnear i) hchild
          _ ≤ witnessRadius j := by nlinarith [hradChild]
      · intro a ha
        rcases Finset.mem_biUnion.mp ha with ⟨i, _, hia⟩
        have hchild := (ih i).2 a hia
        exact ⟨hchild.1, hchild.2.trans (Nat.le_of_lt hdec)⟩

theorem witness_support_proof (d : ℕ) (hd : 3 ≤ d) :
    ∃ N : ℕ, ∀ m n₀ j x L, N ≤ n₀ → IsWitness d m n₀ j x L →
      (∀ a ∈ L, physicalDistance d m x a.anchor ≤ witnessRadius j) ∧
      (∀ a ∈ L, n₀ < a.scale ∧ a.scale ≤ j) := by
  refine ⟨0, ?_⟩
  intro m n₀ j x L _ h
  exact witness_support_aux d m n₀ j x L h

theorem witness_children_disjoint_proof (d : ℕ) (hd : 3 ≤ d) :
    ∃ N : ℕ, ∀ m n₀ r x y L K, N ≤ n₀ →
      IsWitness d m n₀ r x L → IsWitness d m n₀ r y K →
      3 * witnessRadius r < physicalDistance d m x y → Disjoint L K := by
  refine ⟨0, ?_⟩
  intro m n₀ r x y L K _ hx hy hsep
  classical
  rw [Finset.disjoint_left]
  intro a haL haK
  have hxa := (witness_support_aux d m n₀ r x L hx).1 a haL
  have hya := (witness_support_aux d m n₀ r y K hy).1 a haK
  have hya' : physicalDistance d m a.anchor y ≤ witnessRadius r := by
    rw [physicalDistance_comm]
    exact hya
  have hxy : physicalDistance d m x y ≤ 2 * witnessRadius r := by
    calc
      physicalDistance d m x y ≤
          physicalDistance d m x a.anchor + physicalDistance d m a.anchor y :=
        physicalDistance_triangle d m x a.anchor y
      _ ≤ witnessRadius r + witnessRadius r := add_le_add hxa hya'
      _ = 2 * witnessRadius r := by ring
  have hrad : 0 ≤ witnessRadius r := by
    unfold witnessRadius
    exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 4) _)
  linarith

end AndersonAC.SolS78
