import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.EndpointAlgebra
import AndersonAC.S78BridgeEnergy.Basic
import AndersonAC.S78BridgeEnergy.Ward

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- `heatLimit` is bounded by its rpow value. -/
theorem heatLimit_le_rpow {t : ℝ} (ht : 0 < t) :
    ((heatLimit t : ℕ) : ℝ) ≤ t ^ (-1 - heatExponent) := by
  unfold heatLimit
  exact Nat.floor_le (Real.rpow_nonneg ht.le _)

/-- Removed-set cardinality via `removedSize` and `heatLimit`. -/
theorem card_removed_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (C : ℝ) (hC : 1 ≤ C)
    (hIC : I.C = C) (ht : 0 < t) (a : Fin k) :
    (((removedSet I a).card : ℕ) : ℝ) ≤ C * t ^ (-1 - heatExponent) := by
  classical
  have hsize := I.removedSize a
  rw [hIC] at hsize
  have hlim := heatLimit_le_rpow ht
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  calc (((removedSet I a).card : ℕ) : ℝ)
      = ((((I.state a.castSucc).active \ (I.state a.succ).active).card : ℕ) : ℝ) := by
        rfl
      _ ≤ C * ((heatLimit t : ℕ) : ℝ) := hsize
      _ ≤ C * t ^ (-1 - heatExponent) :=
        mul_le_mul_of_nonneg_left hlim hC0

/-- Cauchy–Schwarz for nonnegative rows: `(∑ |h|^2)^2 ≤ |O| * ∑ |h|^4`. -/
theorem sq_sum_sq_le_card_mul_sum_fourth {d m : ℕ}
    (h : Matrix (Torus d m) (Torus d m) ℂ) (i : Torus d m)
    (O : Finset (Torus d m)) :
    (∑ x ∈ O, ‖h i x‖ ^ 2) ^ 2 ≤ (O.card : ℝ) * ∑ x ∈ O, ‖h i x‖ ^ 4 := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq (s := O) (f := fun x => ‖h i x‖ ^ 2)
  have heq : (∑ x ∈ O, (‖h i x‖ ^ 2) ^ 2) = ∑ x ∈ O, ‖h i x‖ ^ 4 := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  simpa [heq] using hcs

/-- Abstract max-weight bound via Cauchy–Schwarz. -/
theorem weight_sum_le_sqrt {d m : ℕ}
    (h : Matrix (Torus d m) (Torus d m) ℂ) (p : Torus d m → ℝ)
    (C R4 : ℝ) (hC : 1 ≤ C) (hR4 : 0 ≤ R4)
    (O : Finset (Torus d m)) (i : Torus d m)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ C)
    (hfourth : ∑ x ∈ O, ‖h i x‖ ^ 4 ≤ R4) :
    ∑ x ∈ O, p i * p x * ‖h i x‖ ^ 2 ≤ C ^ 2 * Real.sqrt ((O.card : ℝ) * R4) := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hpi_nonneg : 0 ≤ p i := (hp i).1
  have hpi_le : p i ≤ C := (hp i).2
  have hsum_nonneg : 0 ≤ ∑ x ∈ O, p x * ‖h i x‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (hp x).1 (sq_nonneg _)
  have hsq_nonneg : 0 ≤ ∑ x ∈ O, ‖h i x‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro x _
    positivity
  have hcard_nonneg : 0 ≤ (O.card : ℝ) := Nat.cast_nonneg _
  -- Factor `p i`.
  have hfac1 : ∑ x ∈ O, p i * p x * ‖h i x‖ ^ 2 =
      p i * (∑ x ∈ O, p x * ‖h i x‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  -- Bound inner `p x`.
  have hinner : ∑ x ∈ O, p x * ‖h i x‖ ^ 2 ≤ C * (∑ x ∈ O, ‖h i x‖ ^ 2) := by
    calc ∑ x ∈ O, p x * ‖h i x‖ ^ 2
        ≤ ∑ x ∈ O, C * ‖h i x‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact (hp x).2
      _ = C * (∑ x ∈ O, ‖h i x‖ ^ 2) := by rw [Finset.mul_sum]
  -- Cauchy for `∑ ‖h‖^2`.
  have hsq : (∑ x ∈ O, ‖h i x‖ ^ 2) ^ 2 ≤ (O.card : ℝ) * R4 := by
    calc (∑ x ∈ O, ‖h i x‖ ^ 2) ^ 2
        ≤ (O.card : ℝ) * ∑ x ∈ O, ‖h i x‖ ^ 4 :=
          sq_sum_sq_le_card_mul_sum_fourth h i O
      _ ≤ (O.card : ℝ) * R4 :=
        mul_le_mul_of_nonneg_left hfourth hcard_nonneg
  have hsqrt : ∑ x ∈ O, ‖h i x‖ ^ 2 ≤ Real.sqrt ((O.card : ℝ) * R4) := by
    have hmem : 0 ≤ (O.card : ℝ) * R4 := mul_nonneg hcard_nonneg hR4
    rw [← Real.sqrt_sq hsq_nonneg]
    apply Real.sqrt_le_sqrt
    exact hsq
  calc ∑ x ∈ O, p i * p x * ‖h i x‖ ^ 2
      = p i * (∑ x ∈ O, p x * ‖h i x‖ ^ 2) := hfac1
    _ ≤ C * (C * (∑ x ∈ O, ‖h i x‖ ^ 2)) := by
        apply mul_le_mul hpi_le hinner hsum_nonneg hC0
    _ = C ^ 2 * (∑ x ∈ O, ‖h i x‖ ^ 2) := by ring
    _ ≤ C ^ 2 * Real.sqrt ((O.card : ℝ) * R4) := by
        apply mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Row-four mass over the removed set is bounded by the full row. -/
theorem rowFour_removed_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (i : Torus d m) (R4 : ℝ)
    (hrow : rowFour (oldInv I a) i < R4) :
    ∑ x ∈ removedSet I a, ‖oldInv I a i x‖ ^ 4 ≤ R4 := by
  classical
  have hsub : ∑ x ∈ removedSet I a, ‖oldInv I a i x‖ ^ 4 ≤
      rowFour (oldInv I a) i := by
    unfold rowFour
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro x _ _
    positivity
  exact hsub.trans hrow.le

/-- Lag controls the imaginary part of the diagonal. -/
theorem lag_Im_le (Gii ri : ℂ) (C Cmat L : ℝ) (hri : (ri).im ≤ C)
    (hlag : ‖Gii - ri‖ ≤ L) (hL : L ≤ Cmat) : (Gii).im ≤ C + Cmat := by
  have h := Complex.abs_im_le_norm (Gii - ri)
  have heq : ((Gii - ri)).im = (Gii).im - (ri).im := by
    simp [Complex.sub_im]
  rw [heq] at h
  have hle : (Gii).im - (ri).im ≤ ‖Gii - ri‖ :=
    (le_abs_self _).trans h
  linarith

/-- Simplification of the Cauchy product to `t^(0.27δ)`.
Uses `heatExponent = 0.46δ`, so `-1-e+1+δ = 0.54δ = 2*0.27δ`. -/
theorem sqrt_card_rowFour_le (C t : ℝ) (hC : 1 ≤ C) (ht : 0 < t) :
    Real.sqrt ((C * t ^ (-1 - heatExponent)) * (0.8 * t ^ (1 + delta))) ≤
      Real.sqrt (0.8 * C) * t ^ (0.27 * delta) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have ht0 : 0 ≤ t := ht.le
  have he : (-1 - heatExponent) + (1 + delta) = 0.54 * delta := by
    unfold heatExponent delta
    ring
  have he2 : (0.54 * delta) / 2 = 0.27 * delta := by ring
  have hprod : (C * t ^ (-1 - heatExponent)) * (0.8 * t ^ (1 + delta)) =
      (0.8 * C) * t ^ (0.54 * delta) := by
    have hrw : t ^ (-1 - heatExponent) * t ^ (1 + delta) = t ^ (0.54 * delta) := by
      rw [← Real.rpow_add ht, he]
    calc _ = (C * 0.8) * (t ^ (-1 - heatExponent) * t ^ (1 + delta)) := by ring
      _ = (0.8 * C) * t ^ (0.54 * delta) := by rw [hrw]; ring
  rw [hprod, Real.sqrt_mul (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  -- `sqrt (t^(0.54δ)) = t^(0.27δ)`
  have hsqrt : Real.sqrt (t ^ (0.54 * delta)) = t ^ (0.27 * delta) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul ht0]
    congr 1
    linarith [he2]
  exact hsqrt.le

/-- Max near-weight with the explicit `t^(0.27δ)` rate. -/
theorem Lmax_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (C : ℝ) (hC : 1 ≤ C)
    (hIC : I.C = C) (ht : 0 < t) (ht1 : t ≤ 1)
    (a : Fin k) (i : Torus d m)
    (hrow : rowFour (oldInv I a) i < 0.8 * t ^ (1 + delta))
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C) :
    ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 ≤
      C ^ 2 * Real.sqrt (0.8 * C) * t ^ (0.27 * delta) := by
  classical
  have hR4 : 0 ≤ (0.8 : ℝ) * t ^ (1 + delta) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg ht.le _)
  have hfourth : ∑ x ∈ removedSet I a, ‖oldInv I a i x‖ ^ 4 ≤
      0.8 * t ^ (1 + delta) :=
    rowFour_removed_le I a i _ hrow
  have h1 := weight_sum_le_sqrt (oldInv I a) (fun j => (r j).im) C
    (0.8 * t ^ (1 + delta)) hC hR4 (removedSet I a) i hdamp hfourth
  have hcard := card_removed_le I C hC hIC ht a
  have h2 : ((removedSet I a).card : ℝ) * (0.8 * t ^ (1 + delta)) ≤
      (C * t ^ (-1 - heatExponent)) * (0.8 * t ^ (1 + delta)) :=
    mul_le_mul_of_nonneg_right hcard hR4
  have h3 : Real.sqrt (((removedSet I a).card : ℝ) * (0.8 * t ^ (1 + delta))) ≤
      Real.sqrt (0.8 * C) * t ^ (0.27 * delta) := by
    calc _ ≤ Real.sqrt ((C * t ^ (-1 - heatExponent)) * (0.8 * t ^ (1 + delta))) :=
          Real.sqrt_le_sqrt h2
      _ ≤ Real.sqrt (0.8 * C) * t ^ (0.27 * delta) :=
          sqrt_card_rowFour_le C t hC ht
  calc ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2
      ≤ C ^ 2 * Real.sqrt (((removedSet I a).card : ℝ) * (0.8 * t ^ (1 + delta))) := h1
    _ ≤ C ^ 2 * (Real.sqrt (0.8 * C) * t ^ (0.27 * delta)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- Total near-weight from per-site row sums (abstract, no Ward needed). -/
theorem total_weight_le {d m : ℕ}
    (h : Matrix (Torus d m) (Torus d m) ℂ) (p : Torus d m → ℝ)
    (C Rw : ℝ) (hC : 1 ≤ C) (hRw : 0 ≤ Rw)
    (B O : Finset (Torus d m))
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ C)
    (hrow : ∀ x ∈ O, ∑ i ∈ B, ‖h i x‖ ^ 2 ≤ Rw) :
    ∑ i ∈ B, ∑ x ∈ O, p i * p x * ‖h i x‖ ^ 2 ≤ C ^ 2 * Rw * (O.card : ℝ) := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hinner : ∀ i ∈ B, ∑ x ∈ O, p i * p x * ‖h i x‖ ^ 2 ≤
      C * (∑ x ∈ O, p x * ‖h i x‖ ^ 2) := by
    intro i _
    have hfac : ∑ x ∈ O, p i * p x * ‖h i x‖ ^ 2 =
        p i * (∑ x ∈ O, p x * ‖h i x‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hfac]
    have hnn : 0 ≤ ∑ x ∈ O, p x * ‖h i x‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro x _
      exact mul_nonneg (hp x).1 (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hp i).2 hnn
  have hswap : (∑ i ∈ B, ∑ x ∈ O, p x * ‖h i x‖ ^ 2) =
      ∑ x ∈ O, ∑ i ∈ B, p x * ‖h i x‖ ^ 2 := Finset.sum_comm
  have hper : ∀ x ∈ O, (∑ i ∈ B, p x * ‖h i x‖ ^ 2) ≤ C * Rw := by
    intro x hx
    have hfac : (∑ i ∈ B, p x * ‖h i x‖ ^ 2) =
        p x * (∑ i ∈ B, ‖h i x‖ ^ 2) := by
      rw [Finset.mul_sum]
    rw [hfac]
    have hnn : 0 ≤ ∑ i ∈ B, ‖h i x‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro y _
      positivity
    exact mul_le_mul (hp x).2 (hrow x hx) hnn hC0
  calc ∑ i ∈ B, ∑ x ∈ O, p i * p x * ‖h i x‖ ^ 2
      ≤ ∑ i ∈ B, C * (∑ x ∈ O, p x * ‖h i x‖ ^ 2) :=
        Finset.sum_le_sum fun i hi => hinner i hi
    _ = C * (∑ i ∈ B, ∑ x ∈ O, p x * ‖h i x‖ ^ 2) := by rw [Finset.mul_sum]
    _ = C * (∑ x ∈ O, ∑ i ∈ B, p x * ‖h i x‖ ^ 2) := by rw [hswap]
    _ ≤ C * ((O.card : ℝ) * (C * Rw)) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        calc ∑ x ∈ O, ∑ i ∈ B, p x * ‖h i x‖ ^ 2
            ≤ ∑ _x ∈ O, C * Rw := Finset.sum_le_sum fun x hx => hper x hx
          _ = (O.card : ℝ) * (C * Rw) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by ring

/-- Row sums over a sub-active set are bounded by the subtype Ward row.
Reindexes `B` into the active subtype via `attach`. -/
theorem row_swap_le {d m : ℕ}
    (G : Matrix (Torus d m) (Torus d m) ℂ) (t Rw : ℝ)
    (A B : Finset (Torus d m)) (hBA : B ⊆ A)
    (hsymG : ∀ i j, G i j = G j i)
    (hsub : ∀ j : {x : Torus d m // x ∈ A},
      rowTwo ((Real.sqrt t : ℂ) •
        G.submatrix (fun i : {x : Torus d m // x ∈ A} => (i.val : Torus d m))
          (fun i : {x : Torus d m // x ∈ A} => (i.val : Torus d m))) j ≤ Rw)
    (x : Torus d m) (hx : x ∈ A) :
    ∑ i ∈ B, ‖((Real.sqrt t : ℂ) • G) i x‖ ^ 2 ≤ Rw := by
  classical
  let S := {x : Torus d m // x ∈ A}
  let GS : Matrix S S ℂ :=
    G.submatrix (fun i : S => (i.val : Torus d m)) (fun i : S => (i.val : Torus d m))
  let hN : Matrix S S ℂ := (Real.sqrt t : ℂ) • GS
  let bx : S := ⟨x, hx⟩
  let F : S → ℝ := fun j => ‖hN bx j‖ ^ 2
  have hpoint : ∀ y : S, F y = ‖((Real.sqrt t : ℂ) • G) y.val x‖ ^ 2 := by
    intro y
    show ‖hN bx y‖ ^ 2 = ‖((Real.sqrt t : ℂ) • G) y.val x‖ ^ 2
    have h1 : GS ⟨x, hx⟩ y = G x y.val := rfl
    have h2 : hN bx y = ((Real.sqrt t : ℂ) • G) y.val x := by
      show ((Real.sqrt t : ℂ) • GS) ⟨x, hx⟩ y = _
      simp only [Matrix.smul_apply, h1]
      rw [hsymG x y.val]
    rw [h2]
  have hA : (∑ i ∈ A, ‖((Real.sqrt t : ℂ) • G) i x‖ ^ 2) = ∑ j : S, F j := by
    rw [← Finset.sum_attach A (fun i => ‖((Real.sqrt t : ℂ) • G) i x‖ ^ 2)]
    refine Finset.sum_congr Finset.attach_eq_univ ?_
    intro y _
    exact (hpoint y).symm
  calc ∑ i ∈ B, ‖((Real.sqrt t : ℂ) • G) i x‖ ^ 2
      ≤ ∑ i ∈ A, ‖((Real.sqrt t : ℂ) • G) i x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hBA (fun i _ _ => sq_nonneg _)
    _ = ∑ j : S, F j := hA
    _ = rowTwo hN bx := rfl
    _ ≤ Rw := hsub bx

/-- Total near-weight from the Ward row via the subtype transfer. -/
theorem Ltotal_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (C Rw : ℝ) (hC : 1 ≤ C) (hRw : 0 ≤ Rw)
    (hIC : I.C = C) (ht : 0 < t)
    (a : Fin k) (B : Finset (Torus d m)) (hB : B ⊆ (I.state a.succ).active)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C)
    (hsymG : ∀ i j, (I.state a.castSucc).g i j = (I.state a.castSucc).g j i)
    (hsub : ∀ j : {x : Torus d m // x ∈ (I.state a.castSucc).active},
      rowTwo ((Real.sqrt t : ℂ) •
        (I.state a.castSucc).g.submatrix (fun i => (i.val : Torus d m))
          (fun i => (i.val : Torus d m))) j ≤ Rw) :
    ∑ i ∈ B, ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 ≤
      C ^ 2 * Rw * (C * t ^ (-1 - heatExponent)) := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hBA : B ⊆ (I.state a.castSucc).active := hB.trans (I.nested a)
  have hrow : ∀ x ∈ removedSet I a, ∑ i ∈ B, ‖oldInv I a i x‖ ^ 2 ≤ Rw := by
    intro x hx
    have hxA : x ∈ (I.state a.castSucc).active := by
      have : x ∈ (I.state a.castSucc).active \ (I.state a.succ).active := hx
      exact (Finset.mem_sdiff.mp this).1
    have h := row_swap_le (I.state a.castSucc).g t Rw
      (I.state a.castSucc).active B hBA hsymG hsub x hxA
    simpa [oldInv, normalizedInverse] using h
  have htot := total_weight_le (oldInv I a) (fun j => (r j).im) C Rw hC hRw
    B (removedSet I a) hdamp hrow
  have hcard := card_removed_le I C hC hIC ht a
  calc ∑ i ∈ B, ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2
      ≤ C ^ 2 * Rw * ((removedSet I a).card : ℝ) := htot
    _ ≤ C ^ 2 * Rw * (C * t ^ (-1 - heatExponent)) := by
        apply mul_le_mul_of_nonneg_left hcard (by positivity)

end AndersonAC.S78BridgeEnergy
