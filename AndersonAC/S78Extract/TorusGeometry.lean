import AndersonAC.S78.Definitions

open scoped BigOperators
namespace AndersonAC.SolS78

open AndersonAC.S78

private lemma sideLength_gt_one {m : ℕ} (hm : 0 < m) : 1 < OAI.Anderson.sideLength m := by
  dsimp [OAI.Anderson.sideLength]
  have hpow : 0 < 20 * m := by omega
  exact one_lt_pow₀ (by decide : 1 < 4) hpow.ne'

private lemma torusBasisVector_ne_zero {d m : ℕ} (hm : 0 < m) (i : Fin d) :
    OAI.Anderson.torusBasisVector (d := d) (m := m) i ≠ (0 : Torus d m) := by
  intro h
  have hi := congrFun h i
  have hi' : (1 : ZMod (OAI.Anderson.sideLength m)) = 0 := by
    simpa [OAI.Anderson.torusBasisVector] using hi
  have hv := congrArg ZMod.val hi'
  have hlen := sideLength_gt_one hm
  haveI : Fact (1 < OAI.Anderson.sideLength m) := ⟨hlen⟩
  simp only [ZMod.val_one, ZMod.val_zero] at hv
  omega

private def nnGraph_translate (d m : ℕ) (a : Torus d m) :
    nnGraph d m →g nnGraph d m := by
  classical
  refine ⟨fun x => a + x, ?_⟩
  intro x y hxy
  rw [nnGraph, SimpleGraph.fromRel_adj] at hxy ⊢
  refine ⟨?_, ?_⟩
  · intro h
    exact hxy.1 (add_left_cancel h)
  · rcases hxy.2 with hxy | hyx
    · rcases hxy with ⟨i, hxy | hxy⟩
      · exact Or.inl ⟨i, Or.inl (by simpa [add_assoc] using congrArg (a + ·) hxy)⟩
      · exact Or.inl ⟨i, Or.inr (by simpa [sub_eq_add_neg, add_assoc] using congrArg (a + ·) hxy)⟩
    · rcases hyx with ⟨i, hyx | hyx⟩
      · exact Or.inr ⟨i, Or.inl (by simpa [add_assoc] using congrArg (a + ·) hyx)⟩
      · exact Or.inr ⟨i, Or.inr (by simpa [sub_eq_add_neg, add_assoc] using congrArg (a + ·) hyx)⟩

private lemma nnGraph_step {d m : ℕ} (hm : 0 < m) (x : Torus d m) (i : Fin d) :
    (nnGraph d m).Reachable x
      (x + OAI.Anderson.torusBasisVector (d := d) (m := m) i) := by
  apply SimpleGraph.Adj.reachable
  rw [nnGraph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨i, Or.inl rfl⟩⟩
  intro h
  apply torusBasisVector_ne_zero hm i
  have heq : x + OAI.Anderson.torusBasisVector (d := d) (m := m) i = x + 0 := by
    simpa using h.symm
  exact add_left_cancel heq

private lemma nnGraph_reachable_steps {d m : ℕ} (hm : 0 < m) (x : Torus d m) (i : Fin d) :
    ∀ n : ℕ, (nnGraph d m).Reachable x (x + n • OAI.Anderson.torusBasisVector i)
  | 0 => by simp
  | n + 1 => by
      have ih := nnGraph_reachable_steps hm x i n
      have hs := nnGraph_step hm (x + n • OAI.Anderson.torusBasisVector (d := d) (m := m) i) i
      have heq : x + (n + 1) • OAI.Anderson.torusBasisVector (d := d) (m := m) i =
          x + n • OAI.Anderson.torusBasisVector (d := d) (m := m) i +
            OAI.Anderson.torusBasisVector (d := d) (m := m) i := by
        ext k
        simp [Nat.cast_succ, add_mul, add_assoc]
      rw [heq]
      exact ih.trans hs

private lemma nnGraph_reachable_zero {d m : ℕ} (hm : 0 < m) (z : Torus d m) :
    (nnGraph d m).Reachable 0 z := by
  classical
  have hcoord : ∀ i : Fin d, (nnGraph d m).Reachable 0 (Pi.single i (z i)) := by
    intro i
    have h := nnGraph_reachable_steps hm (0 : Torus d m) i (z i).val
    have heq : (z i).val • OAI.Anderson.torusBasisVector (d := d) (m := m) i =
        Pi.single i (z i) := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [OAI.Anderson.torusBasisVector]
      · simp [OAI.Anderson.torusBasisVector, hki]
    simpa [heq] using h
  have hsum : ∀ s : Finset (Fin d),
      (nnGraph d m).Reachable 0 (∑ i ∈ s, Pi.single i (z i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his]
        have hmove : (nnGraph d m).Reachable (∑ j ∈ s, Pi.single j (z j))
            ((∑ j ∈ s, Pi.single j (z j)) + Pi.single i (z i)) := by
          simpa [nnGraph_translate] using SimpleGraph.Reachable.map
            (nnGraph_translate d m (∑ j ∈ s, Pi.single j (z j))) (hcoord i)
        have hjoined := ih.trans hmove
        simpa [add_comm] using hjoined
  have h := hsum Finset.univ
  have hz : (∑ i, Pi.single i (z i)) = z := by
    ext i
    simp
  simpa [hz] using h

theorem nnGraph_connected_of_pos {d m : ℕ} (hm : 0 < m) : (nnGraph d m).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro y
  exact nnGraph_reachable_zero hm y

def circleCoordinateDistance {n : ℕ} (x y : ZMod n) : ℕ := (y - x).valMinAbs.natAbs

private lemma circleCoordinateDistance_triangle {n : ℕ} (x y z : ZMod n) :
    circleCoordinateDistance x z ≤ circleCoordinateDistance x y + circleCoordinateDistance y z := by
  unfold circleCoordinateDistance
  have hz : z - x = (y - x) + (z - y) := by abel
  rw [hz]
  calc
    ((y - x + (z - y)).valMinAbs.natAbs) ≤
        ((y - x).valMinAbs + (z - y).valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le _ _
    _ ≤ (y - x).valMinAbs.natAbs + (z - y).valMinAbs.natAbs := by
      exact Int.natAbs_add_le _ _

private lemma circleCoordinateNatAbs_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (1 : ZMod n).valMinAbs.natAbs = 1 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hval : (1 : ZMod n).val = 1 := ZMod.val_one n
  rw [ZMod.valMinAbs_natAbs_eq_min, hval]
  exact min_eq_left (by omega)

private lemma circleCoordinateNatAbs_neg_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (-1 : ZMod n).valMinAbs.natAbs = 1 := by
  rw [ZMod.natAbs_valMinAbs_neg]
  exact circleCoordinateNatAbs_one hn

private lemma circleCoordinateDistance_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    circleCoordinateDistance (0 : ZMod n) 1 = 1 := by
  simp only [circleCoordinateDistance, sub_zero]
  exact circleCoordinateNatAbs_one hn

private lemma circleCoordinateDistance_neg_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    circleCoordinateDistance (0 : ZMod n) (-1) = 1 := by
  simp only [circleCoordinateDistance, sub_zero]
  exact circleCoordinateNatAbs_neg_one hn

private lemma circleCoordinateDistance_sub_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) {x y : ZMod n}
    (h : y - x = 1) : circleCoordinateDistance x y = 1 := by
  unfold circleCoordinateDistance
  rw [h]
  exact circleCoordinateNatAbs_one hn

private lemma circleCoordinateDistance_sub_neg_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) {x y : ZMod n}
    (h : y - x = -1) : circleCoordinateDistance x y = 1 := by
  unfold circleCoordinateDistance
  rw [h]
  exact circleCoordinateNatAbs_neg_one hn

private lemma circleCoordinateDistance_sub_zero {n : ℕ} {x y : ZMod n}
    (h : y - x = 0) : circleCoordinateDistance x y = 0 := by
  unfold circleCoordinateDistance
  rw [h]
  simp

private lemma nnGraph_adj_coordinate_le {d m : ℕ} (hm : 0 < m) {x y : Torus d m}
    (hxy : (nnGraph d m).Adj x y) (i : Fin d) :
    circleCoordinateDistance (x i) (y i) ≤ 1 := by
  classical
  have hn : 2 ≤ OAI.Anderson.sideLength m := by
    have hside := sideLength_gt_one hm
    omega
  rw [nnGraph, SimpleGraph.fromRel_adj] at hxy
  rcases hxy.2 with hxy | hyx
  · rcases hxy with ⟨k, hxy | hxy⟩
    · by_cases hik : i = k
      · have hdiff : y i - x i = 1 := by
          rw [hxy]
          simp [OAI.Anderson.torusBasisVector, hik]
        exact (circleCoordinateDistance_sub_one hn hdiff).le
      · have hdiff : y i - x i = 0 := by
          rw [hxy]
          simp [OAI.Anderson.torusBasisVector, hik]
        rw [circleCoordinateDistance_sub_zero hdiff]
        omega
    · by_cases hik : i = k
      · have hdiff : y i - x i = -1 := by
          rw [hxy]
          simp [OAI.Anderson.torusBasisVector, hik]
        exact (circleCoordinateDistance_sub_neg_one hn hdiff).le
      · have hdiff : y i - x i = 0 := by
          rw [hxy]
          simp [OAI.Anderson.torusBasisVector, hik]
        rw [circleCoordinateDistance_sub_zero hdiff]
        omega
  · rcases hyx with ⟨k, hyx | hyx⟩
    · by_cases hik : i = k
      · have hdiff : y i - x i = -1 := by
          rw [hyx]
          simp [OAI.Anderson.torusBasisVector, hik]
        exact (circleCoordinateDistance_sub_neg_one hn hdiff).le
      · have hdiff : y i - x i = 0 := by
          rw [hyx]
          simp [OAI.Anderson.torusBasisVector, hik]
        rw [circleCoordinateDistance_sub_zero hdiff]
        omega
    · by_cases hik : i = k
      · have hdiff : y i - x i = 1 := by
          rw [hyx]
          simp [OAI.Anderson.torusBasisVector, hik]
        exact (circleCoordinateDistance_sub_one hn hdiff).le
      · have hdiff : y i - x i = 0 := by
          rw [hyx]
          simp [OAI.Anderson.torusBasisVector, hik]
        rw [circleCoordinateDistance_sub_zero hdiff]
        omega

private lemma circleCoordinateDistance_le_walk {d m : ℕ} (hm : 0 < m) {x y : Torus d m}
    (p : (nnGraph d m).Walk x y) (i : Fin d) :
    circleCoordinateDistance (x i) (y i) ≤ p.length := by
  induction p with
  | nil => simp [circleCoordinateDistance]
  | @cons u v w hadj p ih =>
      have hs := nnGraph_adj_coordinate_le hm hadj i
      have ht := circleCoordinateDistance_triangle (u i) (v i) (w i)
      simp only [circleCoordinateDistance] at ht
      have h := le_trans ht (Nat.add_le_add hs ih)
      simpa [circleCoordinateDistance, Nat.add_comm] using h

private lemma circleCoordinateDistance_le_graphDist {d m : ℕ} (hm : 0 < m)
    (x y : Torus d m) (i : Fin d) :
    circleCoordinateDistance (x i) (y i) ≤ (nnGraph d m).dist x y := by
  obtain ⟨p, hp⟩ := (nnGraph_connected_of_pos hm).exists_walk_length_eq_dist x y
  simpa [hp] using circleCoordinateDistance_le_walk hm p i

private lemma card_smallIntInterval (R : ℕ)
    [Fintype (Set.Icc (-(R : ℤ)) (R : ℤ))] :
    Fintype.card (Set.Icc (-(R : ℤ)) (R : ℤ)) = 2 * R + 1 := by
  rw [Fintype.card_Icc, Int.card_Icc]
  have h : (R : ℤ) + 1 - (-(R : ℤ)) = (2 * R + 1 : ℤ) := by omega
  rw [h]
  omega

private lemma card_smallZMod (n R : ℕ) [NeZero n] :
    Fintype.card {z : ZMod n // z.valMinAbs.natAbs ≤ R} ≤ 2 * R + 1 := by
  classical
  letI : Fintype (Set.Icc (-(R : ℤ)) (R : ℤ)) :=
    (Set.finite_Icc (-(R : ℤ)) (R : ℤ)).fintype
  let f : {z : ZMod n // z.valMinAbs.natAbs ≤ R} → Set.Icc (-(R : ℤ)) (R : ℤ) := fun z =>
    ⟨z.val.valMinAbs, by
      have hz : (z.val.valMinAbs.natAbs : ℤ) ≤ R := by exact_mod_cast z.property
      rw [← Int.abs_eq_natAbs] at hz
      exact abs_le.mp hz⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact ZMod.valMinAbs_inj.mp (congrArg Subtype.val hab)
  exact (Fintype.card_le_of_injective f hf).trans_eq (card_smallIntInterval R)

theorem torus_ball_card_bound {d m : ℕ} (hm : 0 < m) (R : ℕ) (x : Torus d m) :
    Fintype.card {y : Torus d m // (nnGraph d m).dist x y ≤ R} ≤ (2 * R + 1) ^ d := by
  classical
  let L := OAI.Anderson.sideLength m
  letI : NeZero L := OAI.Anderson.sideLength_neZero m
  let A := {z : ZMod L // z.valMinAbs.natAbs ≤ R}
  let f : {y : Torus d m // (nnGraph d m).dist x y ≤ R} → (Fin d → A) := fun y i =>
    ⟨y.val i - x i, by
      have hcoord := circleCoordinateDistance_le_graphDist hm x y.val i
      dsimp [circleCoordinateDistance] at hcoord
      exact hcoord.trans y.property⟩
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    funext i
    have h := congrFun hyz i
    have hval : y.val i - x i = z.val i - x i := congrArg Subtype.val h
    have h' := congrArg (fun t => t + x i) hval
    simpa using h'
  calc
    Fintype.card {y : Torus d m // (nnGraph d m).dist x y ≤ R} ≤ Fintype.card (Fin d → A) :=
      Fintype.card_le_of_injective f hf
    _ = (Fintype.card A) ^ d := by simp [A]
    _ ≤ (2 * R + 1) ^ d := by
      gcongr
      exact card_smallZMod L R

private def IsSeparatedFamily {d m : ℕ} (S : Finset (Torus d m)) (ρ : ℝ)
    (P : Finset (Torus d m)) : Prop :=
  P ⊆ S ∧ ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ρ < physicalDistance d m x y

theorem exists_separated_centers {d m : ℕ} (hm : 0 < m)
    (S : Finset (Torus d m)) (ρ : ℝ) (hρ : 0 ≤ ρ) (R k : ℕ)
    (hρR : ρ ≤ (R : ℝ))
    (hcount : (k : ℝ) * ((2 * R + 1) ^ d : ℕ) < (S.card : ℝ)) :
    ∃ centers : Fin k → Torus d m,
      (∀ i, centers i ∈ S) ∧
      (∀ i l, i ≠ l → ρ < physicalDistance d m (centers i) (centers l)) := by
  classical
  let candidates : Finset (Finset (Torus d m)) :=
    Finset.univ.filter (IsSeparatedFamily S ρ)
  have hempty : ∅ ∈ candidates := by simp [candidates, IsSeparatedFamily]
  obtain ⟨P, hPmem, hPmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hP : IsSeparatedFamily S ρ P := (Finset.mem_filter.mp hPmem).2
  have hcover : ∀ y ∈ S, ∃ z ∈ P, physicalDistance d m z y ≤ ρ := by
    intro y hy
    by_contra hnot
    have hfar : ∀ z ∈ P, ρ < physicalDistance d m y z := by
      intro z hz
      have hnle : ¬ physicalDistance d m y z ≤ ρ := by
        intro hdist
        apply hnot
        exact ⟨z, hz, by simpa [physicalDistance, SimpleGraph.dist_comm] using hdist⟩
      exact lt_of_not_ge hnle
    have hyP : y ∉ P := by
      intro hyP
      apply hnot
      refine ⟨y, hyP, ?_⟩
      simpa [physicalDistance] using hρ
    have hP' : IsSeparatedFamily S ρ (insert y P) := by
      refine ⟨Finset.insert_subset hy hP.1, ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hab rfl).elim
        · exact hfar b hb
      · rcases hb with rfl | hb
        · simpa [physicalDistance, SimpleGraph.dist_comm] using hfar a ha
        · exact hP.2 a ha b hb hab
    have hP'mem : insert y P ∈ candidates := by
      simp [candidates, hP']
    have := hPmax (insert y P) hP'mem
    have hcard : (insert y P).card = P.card + 1 := Finset.card_insert_of_notMem hyP
    omega
  let balls : Torus d m → Finset (Torus d m) := fun z =>
    Finset.univ.filter (fun y => (nnGraph d m).dist z y ≤ R)
  have hsubset : S ⊆ P.biUnion balls := by
    intro y hy
    rcases hcover y hy with ⟨z, hz, hnear⟩
    have hreal : ((nnGraph d m).dist z y : ℝ) ≤ (R : ℝ) := by
      exact hnear.trans hρR
    have hnat : (nnGraph d m).dist z y ≤ R := by exact_mod_cast hreal
    exact Finset.mem_biUnion.mpr ⟨z, hz, by simp [balls, hnat]⟩
  have hball : ∀ z, (balls z).card ≤ (2 * R + 1) ^ d := by
    intro z
    have hcard : Fintype.card {y : Torus d m // (nnGraph d m).dist z y ≤ R} =
        (balls z).card := by
      exact Fintype.card_of_subtype (p := fun y : Torus d m => (nnGraph d m).dist z y ≤ R)
        (balls z) (by intro y; simp [balls])
    rw [← hcard]
    exact torus_ball_card_bound hm R z
  have hcardNat : S.card ≤ P.card * ((2 * R + 1) ^ d) := by
    calc
      S.card ≤ (P.biUnion balls).card := Finset.card_le_card hsubset
      _ ≤ ∑ z ∈ P, (balls z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ P, ((2 * R + 1) ^ d) := by
        apply Finset.sum_le_sum
        intro z hz
        exact hball z
      _ = P.card * ((2 * R + 1) ^ d) := by simp
  have hcardReal : (S.card : ℝ) ≤ (P.card : ℝ) * ((2 * R + 1) ^ d : ℝ) := by
    exact_mod_cast hcardNat
  have hk : k ≤ P.card := by
    by_contra hnot
    have hp : P.card < k := Nat.lt_of_not_ge hnot
    have hpR : (P.card : ℝ) < (k : ℝ) := by exact_mod_cast hp
    have hpos : 0 < ((2 * R + 1) ^ d : ℝ) := by positivity
    have hprod := mul_lt_mul_of_pos_right hpR hpos
    norm_cast at hcount
    have hcountR : (k : ℝ) * ((2 * R + 1) ^ d : ℝ) < (S.card : ℝ) := by
      exact_mod_cast hcount
    linarith
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hk
  let e : Q ≃ Fin k := Q.equivFinOfCardEq hQcard
  refine ⟨fun i => (e.symm i).val, ?_, ?_⟩
  · intro i
    exact hP.1 (hQP (e.symm i).property)
  · intro i l hil
    have hne : (e.symm i).val ≠ (e.symm l).val := by
      intro hval
      apply hil
      apply e.symm.injective
      exact Subtype.ext hval
    exact hP.2 _ (hQP (e.symm i).property) _ (hQP (e.symm l).property) hne

end AndersonAC.SolS78
