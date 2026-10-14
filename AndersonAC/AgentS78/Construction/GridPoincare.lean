import AndersonAC.AgentS78.Construction.TileCoverParts
import AndersonAC.S3WCube.Reflect

/-! A finite grid Poincaré bound used by the §5 tile-cover construction. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace AndersonAC.AgentS78

open AndersonAC.S3

private theorem torus_poincare_any_dim {d : ℕ} :
    ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ v : Torus d L → ℂ, neutral v →
        normSq v ≤ (1 / 16) * (L : ℝ) ^ 2 * gradientEnergy v := by
  intro L inst hL v hv
  have hzero : AndersonAC.S3.fourier v 0 = 0 := by
    rw [AndersonAC.AgentS3.fourier_zero_eq_sum]
    exact hv
  have hmode : ∀ k : Torus d L,
      ‖AndersonAC.S3.fourier v k‖ ^ 2 ≤
        ((L : ℝ) ^ 2 / 16) *
          (laplacianSymbol (gridAngle k) * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [hzero, laplacianSymbol, gridAngle]
    · have hgap := AndersonAC.AgentS3.laplacianSymbol_lower_nonzero hL hk
      have hcoef : 1 ≤ (L : ℝ) ^ 2 / 16 * laplacianSymbol (gridAngle k) := by
        have hscale : 0 ≤ (L : ℝ) ^ 2 / 16 := by positivity
        have hmul := mul_le_mul_of_nonneg_left hgap hscale
        have hinv : (L : ℝ) ^ 2 / 16 * (16 / (L : ℝ) ^ 2) = 1 := by field_simp
        nlinarith
      have hnonneg := sq_nonneg ‖AndersonAC.S3.fourier v k‖
      nlinarith
  have havg : gridAvgReal (fun k => ‖AndersonAC.S3.fourier v k‖ ^ 2) ≤
      ((L : ℝ) ^ 2 / 16) * gridAvgReal (fun k =>
        laplacianSymbol (gridAngle k) * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
    unfold gridAvgReal
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hmode k)
    have hsum' : (∑ k, ‖AndersonAC.S3.fourier v k‖ ^ 2) ≤
        ((L : ℝ) ^ 2 / 16) *
          (∑ k, laplacianSymbol (gridAngle k) * ‖AndersonAC.S3.fourier v k‖ ^ 2) := by
      calc
        (∑ k, ‖AndersonAC.S3.fourier v k‖ ^ 2)
            ≤ ∑ k, ((L : ℝ) ^ 2 / 16) *
                (laplacianSymbol (gridAngle k) *
                  ‖AndersonAC.S3.fourier v k‖ ^ 2) := hsum
        _ = _ := by rw [← Finset.mul_sum]
    have hN : 0 ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ := by positivity
    calc
      (Fintype.card (Torus d L) : ℝ)⁻¹ *
          ∑ k, ‖AndersonAC.S3.fourier v k‖ ^ 2
        ≤ (Fintype.card (Torus d L) : ℝ)⁻¹ *
            (((L : ℝ) ^ 2 / 16) *
              ∑ k, laplacianSymbol (gridAngle k) *
                ‖AndersonAC.S3.fourier v k‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hsum' hN
      _ = ((L : ℝ) ^ 2 / 16) *
            ((Fintype.card (Torus d L) : ℝ)⁻¹ *
              ∑ k, laplacianSymbol (gridAngle k) *
                ‖AndersonAC.S3.fourier v k‖ ^ 2) := by ring
  calc
    normSq v = gridAvgReal (fun k => ‖AndersonAC.S3.fourier v k‖ ^ 2) :=
      AndersonAC.S3.parseval v
    _ ≤ ((L : ℝ) ^ 2 / 16) * gradientEnergy v := by
      rw [AndersonAC.AgentS3.fourier_gradientEnergy hL v]
      exact havg
    _ = (1 / 16) * (L : ℝ) ^ 2 * gradientEnergy v := by ring

private def gridSucc {d K : ℕ} (x : Fin d → Fin K) (i : Fin d)
    (h : (x i).val + 1 < K) : Fin d → Fin K :=
  Function.update x i ⟨(x i).val + 1, h⟩

private def gridPred {d K : ℕ} (x : Fin d → Fin K) (i : Fin d)
    (_h : 0 < (x i).val) : Fin d → Fin K :=
  Function.update x i ⟨Nat.sub (x i).val 1,
    lt_of_le_of_lt (Nat.sub_le _ _) (x i).isLt⟩

private def gridPredAny {d K : ℕ} (x : Fin d → Fin K) (i : Fin d) : Fin d → Fin K :=
  if h : 0 < (x i).val then gridPred x i h else x

private def gridSuccAny {d K : ℕ} (x : Fin d → Fin K) (i : Fin d) : Fin d → Fin K :=
  if h : (x i).val + 1 < K then gridSucc x i h else x

private def gridPlus {d K : ℕ} (f : (Fin d → Fin K) → ℝ)
    (x : Fin d → Fin K) (i : Fin d) : ℝ :=
  if (x i).val + 1 < K then (f (gridSuccAny x i) - f x) ^ 2 else 0

private def gridMinus {d K : ℕ} (f : (Fin d → Fin K) → ℝ)
    (x : Fin d → Fin K) (i : Fin d) : ℝ :=
  if 0 < (x i).val then (f (gridPredAny x i) - f x) ^ 2 else 0

private lemma gridSuccAny_predAny {d K : ℕ} (x : Fin d → Fin K) (i : Fin d)
    (hx : 0 < (x i).val) : gridSuccAny (gridPredAny x i) i = x := by
  have hsub : Nat.sub (x i).val 1 + 1 = (x i).val := Nat.sub_add_cancel hx
  have hpred : gridPredAny x i = gridPred x i hx := by
    simp [gridPredAny, hx]
  have hlt : (gridPred x i hx i).val + 1 < K := by
    simp only [gridPred, Function.update_self]
    change Nat.sub (x i).val 1 + 1 < K
    rw [hsub]
    exact (x i).isLt
  calc
    gridSuccAny (gridPredAny x i) i = gridSuccAny (gridPred x i hx) i := by rw [hpred]
    _ = gridSucc (gridPred x i hx) i hlt := by simp [gridSuccAny, hlt]
    _ = x := by
      funext k
      by_cases hk : k = i
      · subst k
        apply Fin.ext
        simp only [gridSucc, gridPred, Function.update_self]
        change Nat.sub (x i).val 1 + 1 = (x i).val
        exact hsub
      · simp [gridSucc, gridPred, Function.update_of_ne hk]

private lemma gridPredAny_succAny {d K : ℕ} (x : Fin d → Fin K) (i : Fin d)
    (hx : (x i).val + 1 < K) : gridPredAny (gridSuccAny x i) i = x := by
  have hsucc : gridSuccAny x i = gridSucc x i hx := by simp [gridSuccAny, hx]
  have hpos : 0 < (gridSucc x i hx i).val := by
    simp [gridSucc, Function.update_self]
  have hpred : gridPredAny (gridSucc x i hx) i = gridPred (gridSucc x i hx) i hpos := by
    simp [gridPredAny, hpos]
  calc
    gridPredAny (gridSuccAny x i) i = gridPredAny (gridSucc x i hx) i := by rw [hsucc]
    _ = gridPred (gridSucc x i hx) i hpos := hpred
    _ = x := by
      funext k
      by_cases hk : k = i
      · subst k
        apply Fin.ext
        simp only [gridPred, gridSucc, Function.update_self]
        change Nat.sub ((x i).val + 1) 1 = (x i).val
        exact Nat.add_sub_cancel_right _ _
      · simp [gridPred, gridSucc, Function.update_of_ne hk]

private lemma gridMinus_sum_eq_gridPlus_sum {d K : ℕ}
    (f : (Fin d → Fin K) → ℝ) :
    (∑ x, ∑ i, gridMinus f x i) = ∑ x, ∑ i, gridPlus f x i := by
  classical
  have hcoord (i : Fin d) : (∑ x, gridMinus f x i) = ∑ x, gridPlus f x i := by
    let N : Finset (Fin d → Fin K) := Finset.univ.filter (fun x => 0 < (x i).val)
    let P : Finset (Fin d → Fin K) := Finset.univ.filter (fun x => (x i).val + 1 < K)
    have hminus : (∑ x, gridMinus f x i) =
        ∑ x ∈ N, (f (gridPredAny x i) - f x) ^ 2 := by
      unfold gridMinus
      rw [Finset.sum_filter]
    have hplus : (∑ x, gridPlus f x i) =
        ∑ x ∈ P, (f (gridSuccAny x i) - f x) ^ 2 := by
      unfold gridPlus
      rw [Finset.sum_filter]
    have hbij : (∑ x ∈ N, (f (gridPredAny x i) - f x) ^ 2) =
        ∑ x ∈ P, (f (gridSuccAny x i) - f x) ^ 2 := by
      refine Finset.sum_bij (fun x _ => gridPredAny x i) ?_ ?_ ?_ ?_
      · intro x hx
        have hxpos : 0 < (x i).val := (Finset.mem_filter.mp hx).2
        have hsub : Nat.sub (x i).val 1 + 1 = (x i).val := Nat.sub_add_cancel hxpos
        have hbound : (gridPredAny x i i).val + 1 < K := by
          simp only [gridPredAny, dif_pos hxpos, gridPred, Function.update_self]
          change Nat.sub (x i).val 1 + 1 < K
          rw [hsub]
          exact (x i).isLt
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbound⟩
      · intro x hx y hy hxy
        have hxpos : 0 < (x i).val := (Finset.mem_filter.mp hx).2
        have hypos : 0 < (y i).val := (Finset.mem_filter.mp hy).2
        calc
          x = gridSuccAny (gridPredAny x i) i := (gridSuccAny_predAny x i hxpos).symm
          _ = gridSuccAny (gridPredAny y i) i := congrArg (fun z => gridSuccAny z i) hxy
          _ = y := gridSuccAny_predAny y i hypos
      · intro y hy
        have hybound : (y i).val + 1 < K := (Finset.mem_filter.mp hy).2
        refine ⟨gridSuccAny y i, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simp only [gridSuccAny, dif_pos hybound, gridSucc, Function.update_self]
          omega
        · exact gridPredAny_succAny y i hybound
      · intro x hx
        have hxpos : 0 < (x i).val := (Finset.mem_filter.mp hx).2
        rw [gridSuccAny_predAny x i hxpos]
        ring
    calc
      (∑ x, gridMinus f x i) =
          ∑ x ∈ N, (f (gridPredAny x i) - f x) ^ 2 := hminus
      _ = ∑ x ∈ P, (f (gridSuccAny x i) - f x) ^ 2 := hbij
      _ = ∑ x, gridPlus f x i := hplus.symm
  calc
    (∑ x, ∑ i, gridMinus f x i)
        = ∑ i, ∑ x, gridMinus f x i := Finset.sum_comm
    _ = ∑ i, ∑ x, gridPlus f x i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcoord i
    _ = ∑ x, ∑ i, gridPlus f x i := Finset.sum_comm

private noncomputable def adjCoord {d K : ℕ} (x : Fin d → Fin K)
    (y : {y : (Fin d → Fin K) // AndersonAC.S3.cubeAdjacent x y}) : Fin d :=
  Classical.choose y.2

private lemma adjCoord_spec {d K : ℕ} (x : Fin d → Fin K)
    (y : {y : (Fin d → Fin K) // AndersonAC.S3.cubeAdjacent x y}) :
    (∀ k, k ≠ adjCoord x y → x k = y.1 k) ∧
      |((x (adjCoord x y)).val : ℤ) - (y.1 (adjCoord x y)).val| = 1 :=
  Classical.choose_spec y.2

private noncomputable def adjIndex {d K : ℕ} (x : Fin d → Fin K)
    (y : {y : (Fin d → Fin K) // AndersonAC.S3.cubeAdjacent x y}) : Fin d × Bool :=
  let i := adjCoord x y
  (i, decide ((y.1 i).val = (x i).val + 1))

private lemma adjCoord_dir {d K : ℕ} (x : Fin d → Fin K)
    (y : {y : (Fin d → Fin K) // AndersonAC.S3.cubeAdjacent x y}) :
    (x (adjCoord x y)).val + 1 = (y.1 (adjCoord x y)).val ∨
      (y.1 (adjCoord x y)).val + 1 = (x (adjCoord x y)).val := by
  have hdist := (adjCoord_spec x y).2
  by_cases hnonneg : 0 ≤
      ((x (adjCoord x y)).val : ℤ) - (y.1 (adjCoord x y)).val
  · rw [abs_of_nonneg hnonneg] at hdist
    right
    omega
  · rw [abs_of_neg (lt_of_not_ge hnonneg)] at hdist
    left
    omega

private def gridCandidateWeight {d K : ℕ} (f : (Fin d → Fin K) → ℝ)
    (x : Fin d → Fin K) (p : Fin d × Bool) : ℝ :=
  if p.2 then gridPlus f x p.1 else gridMinus f x p.1

private lemma norm_sub_real_sq (a b : ℝ) :
    ‖((a : ℂ) - (b : ℂ))‖ ^ 2 = (a - b) ^ 2 := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma adjIndex_weight {d K : ℕ} (f : (Fin d → Fin K) → ℝ)
    (x : Fin d → Fin K)
    (y : {y : (Fin d → Fin K) // AndersonAC.S3.cubeAdjacent x y}) :
    gridCandidateWeight f x (adjIndex x y) =
      ‖((f x : ℂ) - (f y.1 : ℂ))‖ ^ 2 := by
  let i := adjCoord x y
  have hrest := (adjCoord_spec x y).1
  rcases adjCoord_dir x y with hplus | hminus
  · have hval : (y.1 i).val = (x i).val + 1 := by dsimp [i] at hplus ⊢; omega
    have hlt : (x i).val + 1 < K := by have := (y.1 i).isLt; omega
    have heq : gridSucc x i hlt = y.1 := by
      funext k
      by_cases hk : k = i
      · subst k
        apply Fin.ext
        simp [gridSucc, Function.update_self]
        omega
      · simp [gridSucc, Function.update_of_ne hk,
          hrest k (by simpa [i] using hk)]
    have hi : adjIndex x y = (i, true) := by
      simp [adjIndex, i, hval]
    rw [hi]
    change gridPlus f x i = ‖((f x : ℂ) - (f y.1 : ℂ))‖ ^ 2
    calc
      gridPlus f x i = (f (gridSucc x i hlt) - f x) ^ 2 := by
        simp [gridPlus, gridSuccAny, hlt]
      _ = (f y.1 - f x) ^ 2 := by rw [heq]
      _ = ‖((f x : ℂ) - (f y.1 : ℂ))‖ ^ 2 := by
        rw [norm_sub_real_sq]
        ring
  · have hval : (y.1 i).val + 1 = (x i).val := by dsimp [i] at hminus ⊢; omega
    have hlt : 0 < (x i).val := by omega
    have heq : gridPred x i hlt = y.1 := by
      funext k
      by_cases hk : k = i
      · subst k
        apply Fin.ext
        simp [gridPred, Function.update_self]
        omega
      · simp [gridPred, Function.update_of_ne hk,
          hrest k (by simpa [i] using hk)]
    have hnot : ¬((y.1 i).val = (x i).val + 1) := by omega
    have hi : adjIndex x y = (i, false) := by
      simp [adjIndex, i, hnot]
    rw [hi]
    change gridMinus f x i = ‖((f x : ℂ) - (f y.1 : ℂ))‖ ^ 2
    calc
      gridMinus f x i = (f (gridPred x i hlt) - f x) ^ 2 := by
        simp [gridMinus, gridPredAny, hlt]
      _ = (f y.1 - f x) ^ 2 := by rw [heq]
      _ = ‖((f x : ℂ) - (f y.1 : ℂ))‖ ^ 2 := by
        rw [norm_sub_real_sq]
        ring

private lemma adjIndex_injective {d K : ℕ} (x : Fin d → Fin K) :
    Function.Injective (adjIndex x) := by
  intro y z h
  let i := adjCoord x y
  have hij : adjCoord x y = adjCoord x z := congrArg Prod.fst h
  have hdec0 := congrArg Prod.snd h
  have hdec : decide ((y.1 i).val = (x i).val + 1) =
      decide ((z.1 i).val = (x i).val + 1) := by
    dsimp [adjIndex] at hdec0
    change decide ((y.1 i).val = (x i).val + 1) =
      decide ((z.1 (adjCoord x z)).val = (x (adjCoord x z)).val + 1) at hdec0
    rw [← hij] at hdec0
    exact hdec0
  have hb : ((y.1 i).val = (x i).val + 1) ↔
      ((z.1 i).val = (x i).val + 1) := by
    constructor
    · intro hp
      have htrue : decide ((y.1 i).val = (x i).val + 1) = true := by simp [hp]
      rw [hdec] at htrue
      exact of_decide_eq_true htrue
    · intro hp
      have htrue : decide ((z.1 i).val = (x i).val + 1) = true := by simp [hp]
      rw [← hdec] at htrue
      exact of_decide_eq_true htrue
  have hyr := (adjCoord_spec x y).1
  have hzr := (adjCoord_spec x z).1
  have hzr' : ∀ k, k ≠ i → x k = z.1 k := by
    intro k hk
    have hne : k ≠ adjCoord x z := by
      intro hki
      apply hk
      change k = adjCoord x y
      calc
        k = adjCoord x z := hki
        _ = adjCoord x y := hij.symm
    exact hzr k hne
  apply Subtype.ext
  funext k
  by_cases hk : k = i
  · subst k
    by_cases hypos : (y.1 i).val = (x i).val + 1
    · have hzpos := hb.mp hypos
      apply Fin.ext
      omega
    · have hyneg : (y.1 i).val + 1 = (x i).val := by
        have hdiry :
            (x i).val + 1 = (y.1 i).val ∨ (y.1 i).val + 1 = (x i).val := by
          simpa [i] using adjCoord_dir x y
        rcases hdiry with hpos | hneg
        · omega
        · exact hneg
      have hznot : ¬((z.1 i).val = (x i).val + 1) := by
        intro hzpos
        exact hypos (hb.mpr hzpos)
      have hdirz :
          (x i).val + 1 = (z.1 i).val ∨ (z.1 i).val + 1 = (x i).val := by
        have hz := adjCoord_dir x z
        rw [← hij] at hz
        simpa [i] using hz
      have hzneg : (z.1 i).val + 1 = (x i).val := by
        rcases hdirz with hpos | hneg
        · omega
        · exact hneg
      apply Fin.ext
      omega
  · calc
      y.1 k = x k := (hyr k (by simpa [i] using hk)).symm
      _ = z.1 k := hzr' k hk

private lemma cubeNeighbourSum_le_gridBoth {d K : ℕ}
    (f : (Fin d → Fin K) → ℝ) (x : Fin d → Fin K) :
    AndersonAC.AgentS3.cubeNeighbourSum (fun y => (f y : ℂ)) x ≤
      ∑ i, (gridPlus f x i + gridMinus f x i) := by
  classical
  let Adj := {y : (Fin d → Fin K) // AndersonAC.S3.cubeAdjacent x y}
  let w : (Fin d → Fin K) → ℝ := fun y => ‖((f x : ℂ) - (f y : ℂ))‖ ^ 2
  have hconvert : (∑ y, if h : AndersonAC.S3.cubeAdjacent x y then w y else 0) =
      ∑ y : Adj, w y.1 := by
    classical
    calc
      (∑ y, if h : AndersonAC.S3.cubeAdjacent x y then w y else 0) =
          ∑ y ∈ Finset.univ.filter (fun y => AndersonAC.S3.cubeAdjacent x y), w y := by
            simp [Finset.sum_filter]
      _ = ∑ y : Adj, w y.1 := by
            rw [← Finset.sum_subtype_eq_sum_filter]
            simp [Adj]
  have himage : (∑ y : Adj, w y.1) =
      ∑ p ∈ (Finset.univ : Finset Adj).image (adjIndex x),
        gridCandidateWeight f x p := by
    calc
      (∑ y : Adj, w y.1) =
          ∑ y : Adj, gridCandidateWeight f x (adjIndex x y) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact (adjIndex_weight f x y).symm
      _ = ∑ p ∈ (Finset.univ : Finset Adj).image (adjIndex x),
            gridCandidateWeight f x p := by
              symm
              exact Finset.sum_image
                (fun a ha b hb hab => adjIndex_injective x hab)
  have hsubset : (Finset.univ : Finset Adj).image (adjIndex x) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hnonneg : ∀ p ∈ (Finset.univ : Finset (Fin d × Bool)),
      0 ≤ gridCandidateWeight f x p := by
    intro p hp
    unfold gridCandidateWeight
    split_ifs with hpdir
    · unfold gridPlus
      split_ifs <;> positivity
    · unfold gridMinus
      split_ifs <;> positivity
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun p hp hnot => hnonneg p (Finset.mem_univ p))
  have hfull : (∑ p : Fin d × Bool, gridCandidateWeight f x p) =
      ∑ i, (gridPlus f x i + gridMinus f x i) := by
    rw [Fintype.sum_prod_type]
    simp [gridCandidateWeight]
  unfold AndersonAC.AgentS3.cubeNeighbourSum
  change (∑ y, if h : AndersonAC.S3.cubeAdjacent x y then w y else 0) ≤ _
  calc
    (∑ y, if h : AndersonAC.S3.cubeAdjacent x y then w y else 0)
        = ∑ y : Adj, w y.1 := hconvert
    _ = ∑ p ∈ (Finset.univ : Finset Adj).image (adjIndex x),
          gridCandidateWeight f x p := himage
    _ ≤ ∑ p : Fin d × Bool, gridCandidateWeight f x p := hsum
    _ = _ := hfull

private lemma cubeEnergy_le_gridEnergy {d K : ℕ}
    (f : (Fin d → Fin K) → ℝ) :
    AndersonAC.S3.cubeEnergy (fun x => (f x : ℂ)) ≤ gridEnergy f := by
  classical
  rw [AndersonAC.AgentS3.cubeEnergy_eq_neighbour]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => cubeNeighbourSum_le_gridBoth f x)
  calc
    (1 / 2 : ℝ) * ∑ x,
        AndersonAC.AgentS3.cubeNeighbourSum (fun y => (f y : ℂ)) x
      ≤ (1 / 2) * ∑ x, ∑ i, (gridPlus f x i + gridMinus f x i) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2) * ((∑ x, ∑ i, gridPlus f x i) +
          (∑ x, ∑ i, gridMinus f x i)) := by
        congr 1
        simp_rw [Finset.sum_add_distrib]
    _ = gridEnergy f := by
        rw [gridMinus_sum_eq_gridPlus_sum]
        have hG : (∑ x, ∑ i, gridPlus f x i) = gridEnergy f := by
          unfold gridEnergy
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : (x i).val + 1 < K
          · simp [gridPlus, gridSuccAny, gridSucc, h, Function.update_self]
          · simp [gridPlus, h]
        calc
          (1 / 2) * ((∑ x, ∑ i, gridPlus f x i) +
              (∑ x, ∑ i, gridPlus f x i)) =
              ∑ x, ∑ i, gridPlus f x i := by ring
          _ = gridEnergy f := hG

private lemma cubeMean_real {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → Fin K) → ℝ) :
    AndersonAC.S3.cubeMean (fun x => (f x : ℂ)) =
      ((∑ x, f x) / (K : ℝ) ^ d : ℂ) := by
  have hcard : Fintype.card (Cube d K) = K ^ d := by
    simp [AndersonAC.S3.Cube]
  unfold AndersonAC.S3.cubeMean
  rw [hcard, ← Complex.ofReal_sum]
  push_cast
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  field_simp [hKne]

private lemma gridEnergy_nonneg {d K : ℕ} (f : (Fin d → Fin K) → ℝ) :
    0 ≤ gridEnergy f := by
  unfold gridEnergy
  apply Finset.sum_nonneg
  intro w hw
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> positivity

theorem gridPoincare_proof : GridPoincareStatement := by
  intro d K f
  classical
  by_cases hK0 : K = 0
  · subst K
    by_cases hd0 : d = 0
    · subst d
      letI : Unique (Fin 0 → Fin 0) := inferInstance
      simp [gridEnergy]
    · letI : IsEmpty (Fin d → Fin 0) :=
        ⟨fun w => Fin.elim0 (w ⟨0, by omega⟩)⟩
      simp [gridEnergy]
  by_cases hK1 : K = 1
  · subst K
    letI : Unique (Fin d → Fin 1) := inferInstance
    simp [gridEnergy]
  have hK : 2 ≤ K := by omega
  by_cases hd0 : d = 0
  · subst d
    letI : Unique (Fin 0 → Fin K) := inferInstance
    simp [gridEnergy]
  letI : NeZero (2 * K) := ⟨by omega⟩
  have hL : 4 ≤ 2 * K := by omega
  have hl : 0 < K := by omega
  let fC : Cube d K → ℂ := fun x => (f x : ℂ)
  let g := AndersonAC.S3.reflected hl fC
  have hnorm (x : Cube d K) :
      ‖fC x - AndersonAC.S3.cubeMean fC‖ ^ 2 =
        (f x - (∑ y, f y) / (K : ℝ) ^ d) ^ 2 := by
    rw [show fC = (fun x => (f x : ℂ)) by rfl, cubeMean_real (by omega)]
    simpa [fC, Complex.ofReal_div, Complex.ofReal_pow] using
      (norm_sub_real_sq (f x) ((∑ y, f y) / (K : ℝ) ^ d))
  have hnormRef : AndersonAC.S3.normSq g =
      (2 : ℝ) ^ d * ∑ x,
        (f x - (∑ y, f y) / (K : ℝ) ^ d) ^ 2 := by
    calc
      AndersonAC.S3.normSq g =
          ∑ x : Torus d (2 * K),
            ‖fC (AndersonAC.AgentS3.foldPt x) - AndersonAC.S3.cubeMean fC‖ ^ 2 := by
              change (∑ x : Torus d (2 * K),
                ‖AndersonAC.S3.reflected hl fC x‖ ^ 2) = _
              simp_rw [AndersonAC.AgentS3.reflected_eq_foldPt]
      _ = (2 : ℝ) ^ d * ∑ x : Cube d K,
            ‖fC x - AndersonAC.S3.cubeMean fC‖ ^ 2 :=
              AndersonAC.AgentS3.foldPt_sum_real (d := d) (l := K) hl
                (fun x => ‖fC x - AndersonAC.S3.cubeMean fC‖ ^ 2)
      _ = (2 : ℝ) ^ d * ∑ x,
            (f x - (∑ y, f y) / (K : ℝ) ^ d) ^ 2 := by
              congr 1
              apply Finset.sum_congr rfl
              intro x hx
              exact hnorm x
  have hP := torus_poincare_any_dim (d := d) (2 * K) hL g
    (AndersonAC.AgentS3.reflected_neutral hl fC)
  have hE := AndersonAC.AgentS3.reflected_gradientEnergy_le hl fC
  have hE' : AndersonAC.S3.gradientEnergy g ≤
      (2 : ℝ) ^ (d + 1) * gridEnergy f := by
    exact hE.trans (mul_le_mul_of_nonneg_left (cubeEnergy_le_gridEnergy f)
      (by positivity))
  have hbound :
      (2 : ℝ) ^ d * ∑ x,
          (f x - (∑ y, f y) / (K : ℝ) ^ d) ^ 2 ≤
        (2 : ℝ) ^ d * ((1 / 2) * (K : ℝ) ^ 2 * gridEnergy f) := by
    rw [← hnormRef]
    calc
      AndersonAC.S3.normSq g ≤ ((1 / 16) : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
          AndersonAC.S3.gradientEnergy g := hP
      _ ≤ (1 / 16) * ((2 * K : ℕ) : ℝ) ^ 2 *
          ((2 : ℝ) ^ (d + 1) * gridEnergy f) := by
            gcongr
      _ = (2 : ℝ) ^ d * ((1 / 2) * (K : ℝ) ^ 2 * gridEnergy f) := by
            push_cast
            ring
  have hp : 0 < (2 : ℝ) ^ d := by positivity
  have hvariance :
      ∑ x, (f x - (∑ y, f y) / (K : ℝ) ^ d) ^ 2 ≤
        (1 / 2) * (K : ℝ) ^ 2 * gridEnergy f :=
    (mul_le_mul_iff_of_pos_left hp).mp hbound
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hcoef : (1 / 2 : ℝ) ≤ (d : ℝ) := by nlinarith
  have hfactor : 0 ≤ (K : ℝ) ^ 2 * gridEnergy f :=
    mul_nonneg (sq_nonneg _) (gridEnergy_nonneg f)
  calc
    ∑ x, (f x - (∑ y, f y) / (K : ℝ) ^ d) ^ 2
        ≤ (1 / 2) * (K : ℝ) ^ 2 * gridEnergy f := hvariance
    _ ≤ (d : ℝ) * (K : ℝ) ^ 2 * gridEnergy f := by nlinarith

end AndersonAC.AgentS78
