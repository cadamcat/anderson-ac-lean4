import AndersonAC.S78.Definitions

open scoped BigOperators

noncomputable section

namespace AndersonAC.SolS78Deviation

open AndersonAC.S78

variable {d m : ℕ}

abbrev CoordCube (d l : ℕ) := Fin d → Fin l

def coordCubeAdjacent {d l : ℕ} (x y : CoordCube d l) : Prop :=
  ∃ j : Fin d, (∀ i, i ≠ j → x i = y i) ∧ |((x j).val : ℤ) - (y j).val| = 1

def coordCubeEnergy {d l : ℕ} (v : CoordCube d l → ℂ) : ℝ := by
  classical
  exact (1 / 2) * ∑ x, ∑ y, if coordCubeAdjacent x y then ‖v x - v y‖ ^ 2 else 0

def localCubeRadius (R : ℝ) : ℕ := ⌊2 * R⌋₊

def localCubeLength (R : ℝ) : ℕ := 2 * localCubeRadius R + 1

def localCubeDomain (z : Torus d m) (R : ℝ) :=
  {x : Torus d m // x ∈ cube d m z (2 * R)}

noncomputable instance localCubeDomainFintype (z : Torus d m) (R : ℝ) :
    Fintype (localCubeDomain z R) := by
  classical
  change Fintype {x : Torus d m // x ∈ cube d m z (2 * R)}
  exact Fintype.subtype (cube d m z (2 * R)) (by intro x; rfl)

lemma localCubeDomain_sum (z : Torus d m) (R : ℝ) (f : Torus d m → ℝ) :
    (∑ x : localCubeDomain z R, f x.val) =
      ∑ x ∈ cube d m z (2 * R), f x := by
  classical
  change (∑ x ∈ (cube d m z (2 * R)).attach, f x.val) =
    ∑ x ∈ cube d m z (2 * R), f x
  exact Finset.sum_attach _ _

lemma localCubeDomain_double_sum (z : Torus d m) (R : ℝ)
    (f : Torus d m → Torus d m → ℝ) :
    (∑ x : localCubeDomain z R, ∑ y : localCubeDomain z R, f x.val y.val) =
      ∑ x ∈ cube d m z (2 * R), ∑ y ∈ cube d m z (2 * R), f x y := by
  calc
    (∑ x : localCubeDomain z R, ∑ y : localCubeDomain z R, f x.val y.val) =
        ∑ x : localCubeDomain z R, ∑ y ∈ cube d m z (2 * R), f x.val y := by
          apply Fintype.sum_congr
          intro x
          exact localCubeDomain_sum z R (f x.val)
    _ = ∑ x ∈ cube d m z (2 * R), ∑ y ∈ cube d m z (2 * R), f x y := by
          exact localCubeDomain_sum z R (fun x => ∑ y ∈ cube d m z (2 * R), f x y)

def centeredCoordinate (R : ℝ) (i : Fin (localCubeLength R)) : ℤ :=
  (i.val : ℤ) - (localCubeRadius R : ℤ)

def localCubeToTorus (z : Torus d m) (R : ℝ)
    (x : CoordCube d (localCubeLength R)) : Torus d m :=
  fun j => z j + (centeredCoordinate R (x j) : ZMod (OAI.Anderson.sideLength m))

lemma localCubeRadius_le (R : ℝ) (hR : 1 ≤ R) :
    (localCubeRadius R : ℝ) ≤ 2 * R := by
  unfold localCubeRadius
  exact Nat.floor_le (by linarith)

lemma localCubeRadius_side_lt (R : ℝ) (hR : 1 ≤ R)
    (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ)) :
    2 * localCubeRadius R < OAI.Anderson.sideLength m := by
  have hn := localCubeRadius_le R hR
  have hreal : (2 * localCubeRadius R : ℝ) < OAI.Anderson.sideLength m := by
    calc
      (2 * localCubeRadius R : ℝ) ≤ 4 * R := by exact_mod_cast (show
          2 * localCubeRadius R ≤ 4 * R from by nlinarith [hn])
      _ < OAI.Anderson.sideLength m := hside
  exact_mod_cast hreal

lemma centeredCoordinate_abs_le (R : ℝ)
    (i : Fin (localCubeLength R)) :
    |centeredCoordinate R i| ≤ (localCubeRadius R : ℤ) := by
  have hi : i.val < 2 * localCubeRadius R + 1 := i.isLt
  unfold centeredCoordinate
  rw [abs_le]
  constructor <;> omega

lemma centeredCoordinate_valMinAbs (R : ℝ) (hR : 1 ≤ R)
    (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ))
    (i : Fin (localCubeLength R)) :
    (centeredCoordinate R i : ZMod (OAI.Anderson.sideLength m)).valMinAbs =
      centeredCoordinate R i := by
  have habs := centeredCoordinate_abs_le R i
  have h2n : (2 * localCubeRadius R : ℤ) < OAI.Anderson.sideLength m := by
    exact_mod_cast localCubeRadius_side_lt R hR hside
  apply (ZMod.valMinAbs_spec _ _).2
  constructor
  · rfl
  · constructor
    · have h := habs
      rw [abs_le] at h
      change -(OAI.Anderson.sideLength m : ℤ) <
        centeredCoordinate R i * 2
      omega
    · have h := habs
      rw [abs_le] at h
      change centeredCoordinate R i * 2 ≤ OAI.Anderson.sideLength m
      omega

lemma localCubeToTorus_mem (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
    (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ))
    (x : CoordCube d (localCubeLength R)) :
    localCubeToTorus z R x ∈ cube d m z (2 * R) := by
  classical
  simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j
  have hsub : (localCubeToTorus z R x j - z j) =
      (centeredCoordinate R (x j) : ZMod (OAI.Anderson.sideLength m)) := by
    simp [localCubeToTorus]
  rw [hsub, ← ZMod.valMinAbs_natAbs_eq_min]
  rw [centeredCoordinate_valMinAbs R hR hside (x j)]
  have hn := centeredCoordinate_abs_le R (x j)
  have hnat : (centeredCoordinate R (x j)).natAbs ≤ localCubeRadius R := by
    have : ((centeredCoordinate R (x j)).natAbs : ℤ) ≤ localCubeRadius R := by
      simpa only [Int.abs_eq_natAbs] using hn
    exact_mod_cast this
  calc
    ((centeredCoordinate R (x j)).natAbs : ℝ) ≤ localCubeRadius R := by exact_mod_cast hnat
    _ ≤ 2 * R := localCubeRadius_le R hR

lemma localCubeToTorus_sub (z : Torus d m) (R : ℝ)
    (x : CoordCube d (localCubeLength R)) (j : Fin d) :
    localCubeToTorus z R x j - z j =
      (centeredCoordinate R (x j) : ZMod (OAI.Anderson.sideLength m)) := by
  simp [localCubeToTorus]

lemma localCubeDelta_bound (z : Torus d m) (R : ℝ)
    (x : localCubeDomain z R) (j : Fin d) :
    ((x.val j - z j).valMinAbs).natAbs ≤ localCubeRadius R := by
  have hx := x.property
  simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have hcoord := hx j
  rw [← ZMod.valMinAbs_natAbs_eq_min] at hcoord
  have hnreal : (((x.val j - z j).valMinAbs).natAbs : ℝ) ≤ 2 * R := by
    exact_mod_cast hcoord
  exact Nat.le_floor hnreal

def localCubeFromTorus (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
    (x : localCubeDomain z R) : CoordCube d (localCubeLength R) :=
  fun j =>
    let δ := (x.val j - z j).valMinAbs
    ⟨(δ + localCubeRadius R).toNat, by
      have hδnat := localCubeDelta_bound z R x j
      have hδ : |δ| ≤ (localCubeRadius R : ℤ) := by
        have h' : (δ.natAbs : ℤ) ≤ localCubeRadius R := by exact_mod_cast hδnat
        simpa only [Int.abs_eq_natAbs] using h'
      have hlo : 0 ≤ δ + localCubeRadius R := by omega
      have hhi : δ + localCubeRadius R ≤ 2 * localCubeRadius R := by omega
      have hltInt : ((δ + localCubeRadius R).toNat : ℤ) <
          (localCubeLength R : ℤ) := by
        rw [Int.toNat_of_nonneg hlo]
        unfold localCubeLength
        omega
      exact_mod_cast hltInt⟩

lemma localCubeFromTorus_toTorus (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
    (q : localCubeDomain z R) :
    localCubeToTorus z R (localCubeFromTorus z R hR q) = q.val := by
  funext j
  let δ := (q.val j - z j).valMinAbs
  have hδnat : δ.natAbs ≤ localCubeRadius R := localCubeDelta_bound z R q j
  have hδ : |δ| ≤ (localCubeRadius R : ℤ) := by
    have h' : (δ.natAbs : ℤ) ≤ localCubeRadius R := by exact_mod_cast hδnat
    simpa only [Int.abs_eq_natAbs] using h'
  have hlo : 0 ≤ δ + localCubeRadius R := by omega
  have hindex :
      (((localCubeFromTorus z R hR q) j).val : ℤ) - localCubeRadius R = δ := by
    change ((δ + localCubeRadius R).toNat : ℤ) - localCubeRadius R = δ
    rw [Int.toNat_of_nonneg hlo]
    ring
  dsimp [localCubeToTorus, centeredCoordinate]
  rw [hindex]
  rw [ZMod.coe_valMinAbs]
  abel

lemma localCubeToTorus_fromTorus (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
    (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ))
    (x : CoordCube d (localCubeLength R)) :
    localCubeFromTorus z R hR ⟨localCubeToTorus z R x, localCubeToTorus_mem z R hR hside x⟩ = x := by
  funext j
  apply Fin.ext
  dsimp [localCubeFromTorus]
  rw [localCubeToTorus_sub]
  rw [centeredCoordinate_valMinAbs R hR hside]
  have hlo : 0 ≤ centeredCoordinate R (x j) + localCubeRadius R := by
    have habs := centeredCoordinate_abs_le R (x j)
    rw [abs_le] at habs
    omega
  have hcast :
      ((centeredCoordinate R (x j) + localCubeRadius R).toNat : ℤ) = (x j).val := by
    rw [Int.toNat_of_nonneg hlo]
    unfold centeredCoordinate
    ring
  exact_mod_cast hcast

def localCubeEquiv (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
    (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ)) :
    CoordCube d (localCubeLength R) ≃ localCubeDomain z R :=
  Equiv.ofBijective
    (fun x => (⟨localCubeToTorus z R x, localCubeToTorus_mem z R hR hside x⟩ : localCubeDomain z R))
    ⟨by
      intro x y hxy
      have := congrArg (localCubeFromTorus z R hR) hxy
      simpa only [localCubeToTorus_fromTorus z R hR hside] using this,
      by
      intro q
      refine ⟨localCubeFromTorus z R hR q, ?_⟩
      exact Subtype.ext (localCubeFromTorus_toTorus z R hR q)⟩

lemma localCubeToTorus_adj (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
    (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ))
    (x y : CoordCube d (localCubeLength R)) (hxy : coordCubeAdjacent x y) :
    (nnGraph d m).Adj (localCubeToTorus z R x) (localCubeToTorus z R y) := by
  classical
  rcases hxy with ⟨k, hrest, hstep⟩
  have hstepNat : (x k).val + 1 = (y k).val ∨ (y k).val + 1 = (x k).val := by
    have hstep' : |((x k).val : ℤ) - (y k).val| = 1 := hstep
    by_cases hxy : (x k).val ≤ (y k).val
    · have hdiff : ((x k).val : ℤ) - (y k).val = -((y k).val - (x k).val : ℕ) := by omega
      rw [hdiff] at hstep'
      have hnat : ((y k).val - (x k).val : ℕ) = 1 := by
        have hcast : (((y k).val - (x k).val : ℕ) : ℤ) = 1 := by
          simpa using hstep'
        exact_mod_cast hcast
      omega
    · have hyx : (y k).val ≤ (x k).val := by omega
      have hdiff : ((x k).val : ℤ) - (y k).val = ((x k).val - (y k).val : ℕ) := by omega
      rw [hdiff, abs_of_nonneg (Nat.cast_nonneg _)] at hstep'
      have hnat : ((x k).val - (y k).val : ℕ) = 1 := by exact_mod_cast hstep'
      omega
  have hneCoord : x ≠ y := by
    intro h
    subst y
    simp at hstep
  have hneTorus : localCubeToTorus z R x ≠ localCubeToTorus z R y := by
    intro heq
    apply hneCoord
    apply (localCubeEquiv z R hR hside).injective
    have hsub :
        localCubeEquiv z R hR hside x = localCubeEquiv z R hR hside y := by
      apply Subtype.ext
      change localCubeToTorus z R x = localCubeToTorus z R y
      exact heq
    exact hsub
  have hplus :
      (y k).val = (x k).val + 1 →
      localCubeToTorus z R y = localCubeToTorus z R x + OAI.Anderson.torusBasisVector k := by
    intro hval
    have hcoord : centeredCoordinate R (y k) = centeredCoordinate R (x k) + 1 := by
      unfold centeredCoordinate
      omega
    funext j
    by_cases hj : j = k
    · subst j
      simp [localCubeToTorus, OAI.Anderson.torusBasisVector, hcoord]
      abel
    · have hsame := hrest j hj
      simp [localCubeToTorus, OAI.Anderson.torusBasisVector, hsame, hj]
  have hminus :
      (x k).val = (y k).val + 1 →
      localCubeToTorus z R y = localCubeToTorus z R x - OAI.Anderson.torusBasisVector k := by
    intro hval
    have hcoord : centeredCoordinate R (y k) = centeredCoordinate R (x k) - 1 := by
      unfold centeredCoordinate
      omega
    funext j
    by_cases hj : j = k
    · subst j
      simp [localCubeToTorus, OAI.Anderson.torusBasisVector, hcoord]
      abel
    · have hsame := hrest j hj
      simp [localCubeToTorus, OAI.Anderson.torusBasisVector, hsame, hj]
  rw [nnGraph, SimpleGraph.fromRel_adj]
  refine ⟨hneTorus, ?_⟩
  rcases hstepNat with h | h
  · exact Or.inl ⟨k, Or.inl (hplus h.symm)⟩
  · exact Or.inl ⟨k, Or.inr (hminus h.symm)⟩

theorem coordCubeEnergy_le_cubeGradient (z : Torus d m) (R : ℝ) (hR : 1 ≤ R)
    (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ)) (v : Torus d m → ℝ) :
    coordCubeEnergy (fun x => (v (localCubeToTorus z R x) : ℂ)) ≤
      cubeGradient d m (cube d m z (2 * R)) v := by
  classical
  let e := localCubeEquiv z R hR hside
  let F (x y : localCubeDomain z R) : ℝ :=
    if coordCubeAdjacent (e.symm x) (e.symm y) then
      ‖(v x.val : ℂ) - (v y.val : ℂ)‖ ^ 2 else 0
  let Graw (x y : Torus d m) : ℝ :=
    if (nnGraph d m).Adj x y then (v x - v y) ^ 2 else 0
  let G (x y : localCubeDomain z R) : ℝ := Graw x.val y.val
  have heval (x : CoordCube d (localCubeLength R)) :
      (e x).val = localCubeToTorus z R x := rfl
  have hesymm (x : localCubeDomain z R) :
      localCubeToTorus z R (e.symm x) = x.val := by
    have h₁ : e (e.symm x) = x := e.apply_symm_apply x
    have h₂ : e (localCubeFromTorus z R hR x) = x := by
      apply Subtype.ext
      exact localCubeFromTorus_toTorus z R hR x
    have hinv : e.symm x = localCubeFromTorus z R hR x :=
      e.injective (h₁.trans h₂.symm)
    rw [hinv]
    exact localCubeFromTorus_toTorus z R hR x
  have henergy_reindex :
      coordCubeEnergy (fun x => (v (localCubeToTorus z R x) : ℂ)) =
        (1 / 2) * ∑ x : localCubeDomain z R, ∑ y : localCubeDomain z R, F x y := by
    unfold coordCubeEnergy
    congr 1
    calc
      (∑ x, ∑ y, if coordCubeAdjacent x y then
          ‖(v (localCubeToTorus z R x) : ℂ) - (v (localCubeToTorus z R y) : ℂ)‖ ^ 2 else 0) =
          ∑ x, ∑ y, F (e x) (e y) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            simp [F, heval]
      _ = ∑ x : localCubeDomain z R, ∑ y, F x (e y) := by
            rw [Equiv.sum_comp e (fun x => ∑ y, F x (e y))]
      _ = ∑ x : localCubeDomain z R, ∑ y : localCubeDomain z R, F x y := by
            apply Fintype.sum_congr
            intro x
            exact Equiv.sum_comp e (F x)
  have htarget_reindex : cubeGradient d m (cube d m z (2 * R)) v =
      (1 / 2) * ∑ x : localCubeDomain z R, ∑ y : localCubeDomain z R, G x y := by
    unfold cubeGradient
    rw [localCubeDomain_double_sum z R Graw]
  have hterm (x y : localCubeDomain z R) : F x y ≤ G x y := by
    by_cases hxy : coordCubeAdjacent (e.symm x) (e.symm y)
    · have hAdj := localCubeToTorus_adj z R hR hside (e.symm x) (e.symm y) hxy
      have hmapx := hesymm x
      have hmapy := hesymm y
      have hG : (nnGraph d m).Adj x.val y.val := by
        simpa [hmapx, hmapy] using hAdj
      have hnorm :
          ‖(v x.val : ℂ) - (v y.val : ℂ)‖ ^ 2 = (v x.val - v y.val) ^ 2 := by
        have hcast :
            ((v x.val - v y.val : ℝ) : ℂ) = (v x.val : ℂ) - (v y.val : ℂ) := by
          push_cast
          rfl
        rw [← hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp [F, G, Graw, hxy, hG, hnorm]
    · have hG : 0 ≤ G x y := by
        simp only [G, Graw]
        split_ifs <;> positivity
      simp [F, hxy]
      exact hG
  have hsum :
      (∑ x : localCubeDomain z R, ∑ y : localCubeDomain z R, F x y) ≤
        ∑ x : localCubeDomain z R, ∑ y : localCubeDomain z R, G x y := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    exact hterm x y
  rw [henergy_reindex, htarget_reindex]
  exact mul_le_mul_of_nonneg_left hsum (by norm_num)

end AndersonAC.SolS78Deviation
