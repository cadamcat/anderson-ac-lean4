import AndersonAC.S78.Definitions

open scoped BigOperators

noncomputable section

namespace AndersonAC.S78WRec

open AndersonAC.S78

theorem nnGraph_connected (d m : ℕ) (hm : 1 ≤ m) :
    (nnGraph d m).Connected := by
  classical
  have hn : 2 ≤ OAI.Anderson.sideLength m := by
    dsimp [OAI.Anderson.sideLength]
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
        have hc : z + OAI.Anderson.torusBasisVector i = z + 0 := by simpa using h.symm
        exact hb (add_left_cancel hc)
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

private theorem nnGraph_adj_step {d m : ℕ} {u v : Torus d m}
    (h : (nnGraph d m).Adj u v) :
    ∃ i : Fin d,
      v = u + OAI.Anderson.torusBasisVector i ∨
        v = u - OAI.Anderson.torusBasisVector i := by
  change u ≠ v ∧
    ((∃ i : Fin d, v = u + OAI.Anderson.torusBasisVector i ∨
        v = u - OAI.Anderson.torusBasisVector i) ∨
      (∃ i : Fin d, u = v + OAI.Anderson.torusBasisVector i ∨
        u = v - OAI.Anderson.torusBasisVector i)) at h
  rcases h with ⟨_, hrel⟩
  rcases hrel with hrel | hrel
  · exact hrel
  · obtain ⟨i, hmove | hmove⟩ := hrel
    · refine ⟨i, Or.inr ?_⟩
      rw [hmove]
      abel
    · refine ⟨i, Or.inl ?_⟩
      rw [hmove]
      abel

private theorem walk_int_displacement {d m : ℕ} {x y : Torus d m}
    (p : (nnGraph d m).Walk x y) :
    ∃ q : Fin d → ℤ,
      (∀ i, y i = x i + (q i : ZMod (OAI.Anderson.sideLength m))) ∧
      (∀ i, |q i| ≤ (p.length : ℤ)) := by
  induction p with
  | nil =>
      refine ⟨0, ?_, ?_⟩
      · intro i
        simp
      · intro i
        simp
  | @cons u v w hadj p ih =>
      obtain ⟨q, hq, hqb⟩ := ih
      obtain ⟨i, hmove⟩ := nnGraph_adj_step hadj
      have combine (s : Fin d → ℤ)
          (hv : ∀ k, v k = u k + (s k : ZMod (OAI.Anderson.sideLength m)))
          (hs : ∀ k, |s k| ≤ 1) :
          ∃ q' : Fin d → ℤ,
            (∀ k, w k = u k + (q' k : ZMod (OAI.Anderson.sideLength m))) ∧
            (∀ k, |q' k| ≤ ((p.length + 1 : ℕ) : ℤ)) := by
        refine ⟨fun k => s k + q k, ?_, ?_⟩
        · intro k
          calc
            w k = v k + (q k : ZMod (OAI.Anderson.sideLength m)) := hq k
            _ = u k + (s k : ZMod (OAI.Anderson.sideLength m)) +
                (q k : ZMod (OAI.Anderson.sideLength m)) := by rw [hv k]
            _ = u k + ((s k + q k : ℤ) : ZMod (OAI.Anderson.sideLength m)) := by
              rw [Int.cast_add]
              ring
        · intro k
          calc
            |s k + q k| ≤ |s k| + |q k| := abs_add_le _ _
            _ ≤ 1 + (p.length : ℤ) := add_le_add (hs k) (hqb k)
            _ = ((p.length + 1 : ℕ) : ℤ) := by push_cast; omega
      rcases hmove with hplus | hminus
      · let s : Fin d → ℤ := fun k => if k = i then 1 else 0
        have hv' : ∀ k,
            v k = u k + (if k = i then (1 : ZMod (OAI.Anderson.sideLength m)) else 0) := by
          intro k
          rw [hplus]
          simp [OAI.Anderson.torusBasisVector, Pi.single_apply]
        have hv : ∀ k, v k = u k + (s k : ZMod (OAI.Anderson.sideLength m)) := by
          intro k
          simpa [s, Int.cast_ite] using hv' k
        have hs : ∀ k, |(if k = i then (1 : ℤ) else 0)| ≤ 1 := by
          intro k
          by_cases hk : k = i <;> simp [hk]
        obtain ⟨q', hq', hqb'⟩ := combine s hv hs
        refine ⟨q', hq', ?_⟩
        simpa only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] using hqb'
      · let s : Fin d → ℤ := fun k => if k = i then -1 else 0
        have hv' : ∀ k,
            v k = u k + (if k = i then (-1 : ZMod (OAI.Anderson.sideLength m)) else 0) := by
          intro k
          rw [hminus]
          by_cases hk : k = i <;>
            simp [OAI.Anderson.torusBasisVector, Pi.single_apply, hk, sub_eq_add_neg]
        have hv : ∀ k, v k = u k + (s k : ZMod (OAI.Anderson.sideLength m)) := by
          intro k
          simpa [s, Int.cast_ite] using hv' k
        have hs : ∀ k, |(if k = i then (-1 : ℤ) else 0)| ≤ 1 := by
          intro k
          by_cases hk : k = i <;> simp [hk]
        obtain ⟨q', hq', hqb'⟩ := combine s hv hs
        refine ⟨q', hq', ?_⟩
        simpa only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] using hqb'

def witnessBall (d m j : ℕ) (x : Torus d m) : Finset (Torus d m) :=
  Finset.univ.filter fun y => physicalDistance d m x y ≤ witnessRadius j / 2

lemma witnessBall_card_le (d m j : ℕ) (x : Torus d m)
    (hconn : (nnGraph d m).Connected) :
    (witnessBall d m j x).card ≤ (3 * 4 ^ (10 * j)) ^ d := by
  classical
  let R : ℕ := 4 ^ (10 * j)
  let D : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  let V : Finset (Fin d → ℤ) := Fintype.piFinset fun _ : Fin d => D
  let code : (Fin d → ℤ) → Torus d m := fun q i => x i + (q i : ZMod (OAI.Anderson.sideLength m))
  have hRpos : 1 ≤ R := by
    dsimp [R]
    exact Nat.one_le_pow (10 * j) 4 (by omega)
  have hR : (R : ℝ) = witnessRadius j := by
    simp [R, witnessRadius, Nat.cast_pow]
  have hsub : witnessBall d m j x ⊆ V.image code := by
    intro y hy
    simp only [witnessBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hdistReal : ((nnGraph d m).dist x y : ℝ) ≤ (R : ℝ) := by
      have h : ((nnGraph d m).dist x y : ℝ) ≤ witnessRadius j / 2 := by
        simpa [physicalDistance] using hy
      exact le_trans h (by rw [← hR]; linarith)
    have hdistNat : (nnGraph d m).dist x y ≤ R := by exact_mod_cast hdistReal
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
    obtain ⟨q, hq, hqb⟩ := walk_int_displacement p
    have hlen : p.length ≤ R := by exact_mod_cast (hp ▸ hdistNat)
    have hqmem : q ∈ V := by
      apply Fintype.mem_piFinset.2
      intro i
      apply Finset.mem_Icc.mpr
      have habs : |q i| ≤ (R : ℤ) := by
        exact (hqb i).trans (by exact_mod_cast hlen)
      exact abs_le.mp habs
    apply Finset.mem_image.mpr
    refine ⟨q, hqmem, ?_⟩
    funext i
    exact (hq i).symm
  calc
    (witnessBall d m j x).card ≤ (V.image code).card := Finset.card_le_card hsub
    _ ≤ V.card := Finset.card_image_le
    _ = (2 * R + 1) ^ d := by
      dsimp [V]
      rw [Fintype.card_piFinset_const]
      change (Finset.Icc (-(R : ℤ)) (R : ℤ)).card ^ d = (2 * R + 1) ^ d
      rw [Int.card_Icc]
      have hcalc : (R : ℤ) + 1 - (-(R : ℤ)) = ((2 * R + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hcalc, Int.toNat_natCast]
    _ ≤ (3 * R) ^ d := by gcongr <;> omega
    _ = (3 * 4 ^ (10 * j)) ^ d := by simp [R]

end AndersonAC.S78WRec
