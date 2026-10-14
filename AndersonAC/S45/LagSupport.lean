import AndersonAC.S45.Definitions
import AndersonAC.S45.RecordsProof
import AndersonAC.S45.SchurProof
import AndersonAC.S45.SweepEndpointProof
import AndersonAC.S45.GammaProof
import AndersonAC.S45.PrestateProof
import AndersonAC.S45.OverlapLemmas

set_option maxHeartbeats 5000000

/-!
Proof of the transformed lag increment bound (Lemma 4.6).

The finite-array estimates below are arranged around the coordinatewise
square-sum used by `arraymonitor boundssq`; no section statement module is imported here.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45.LagSupport

open AndersonAC.S45

lemma arrayA2sq_le_of_rows {P : Type*} [Fintype P]
    (S : Finset P) (Y : P → P → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ x ∈ S, ‖Y i x‖ ^ 2 ≤ B) :
    AndersonAC.S45.arrayA2sq S Y ≤ B := by
  rw [AndersonAC.S45.arrayA2sq, pi_norm_le_iff_of_nonneg hB]
  intro i
  have hnonneg : 0 ≤ ∑ x ∈ S, ‖Y i x‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro x hx
    exact sq_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hrow i

lemma arrayA2sq_row_le {P : Type*} [Fintype P]
    (S : Finset P) (Y : P → P → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hY : AndersonAC.S45.arrayA2sq S Y ≤ B) (i : P) :
    ∑ x ∈ S, ‖Y i x‖ ^ 2 ≤ B := by
  have hi := (pi_norm_le_iff_of_nonneg hB).1 hY i
  have hnonneg : 0 ≤ ∑ x ∈ S, ‖Y i x‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro x hx
    exact sq_nonneg _
  simpa only [AndersonAC.S45.arrayA2sq, Real.norm_eq_abs,
    abs_of_nonneg hnonneg] using hi

lemma rowSum_le_rowNorm {P : Type*} [Fintype P]
    (A : AndersonAC.S45.CMat P) (i : P) :
    ∑ j, ‖A i j‖ ≤ AndersonAC.S45.rowNorm A := by
  have hfun : ‖fun k => AndersonAC.S45.l1 (A k)‖ ≤
      AndersonAC.S45.rowNorm A := le_rfl
  have hi := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).1 hfun i
  have hnonneg : 0 ≤ ∑ j, ‖A i j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  simpa [AndersonAC.S45.rowNorm, AndersonAC.S45.l1, Real.norm_eq_abs,
    abs_of_nonneg hnonneg] using hi

lemma matrix_pi_norm_mulVec_le {P : Type*} [Fintype P]
    (A : AndersonAC.S45.CMat P) (v : P → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ L) :
    ‖A *ᵥ v‖ ≤ L * ‖v‖ := by
  have hv : ∀ j, ‖v j‖ ≤ ‖v‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).1 le_rfl
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg _))).2
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      calc
        ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
        _ = ∑ j, ‖A i j‖ * ‖v j‖ := by simp [norm_mul]
    _ ≤ ∑ j, ‖A i j‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ L * ‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

lemma lag_matrix_entry_norm_le {P : Type*} [Fintype P] [DecidableEq P]
    (A : AndersonAC.S45.CMat P) (i j : P) : ‖A i j‖ ≤ ‖A‖ := by
  let v := EuclideanSpace.single j (1 : ℂ)
  have hcoord : ‖A i j‖ ≤
      ‖(EuclideanSpace.equiv P ℂ).symm (A *ᵥ v.ofLp)‖ := by
    have h := PiLp.norm_apply_le
      ((EuclideanSpace.equiv P ℂ).symm (A *ᵥ v.ofLp)) i
    simpa [v, EuclideanSpace.equiv, Matrix.mulVec] using h
  have hmul := Matrix.l2_opNorm_mulVec A v
  have hv : ‖v‖ = 1 := by simp [v]
  calc
    ‖A i j‖ ≤ ‖(EuclideanSpace.equiv P ℂ).symm (A *ᵥ v.ofLp)‖ := hcoord
    _ ≤ ‖A‖ * ‖v‖ := hmul
    _ = ‖A‖ := by rw [hv, mul_one]

lemma weighted_sum_sq_le {α : Type*} (s : Finset α) (w b : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * b i) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * b i ^ 2 := by
  have hg : ∀ i ∈ s, 0 ≤ w i * b i ^ 2 := fun i hi =>
    mul_nonneg (hw i hi) (sq_nonneg _)
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => w i * b i) (f := w) (g := fun i => w i * b i ^ 2)
    hw hg (fun i hi => calc
      (w i * b i) ^ 2 = w i * (w i * b i ^ 2) := by ring
      _ ≤ _ := le_rfl)
  simpa only [mul_assoc] using h

lemma lag_weighted_schur_norm_le {P : Type*} [Fintype P] [DecidableEq P]
    (A : AndersonAC.S45.CMat P) (w : P → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, ‖A i j‖ * w j ≤ L * w i)
    (hcol : ∀ j, ∑ i, w i * ‖A i j‖ ≤ L * w j) :
    ‖A‖ ≤ L := by
  apply opNorm_le_of_sq A L hL
  intro v
  let a : P → P → ℝ := fun i j => ‖A i j‖ * w j
  let b : P → P → ℝ := fun i j => ‖v j‖ / w j
  let c : P → ℝ := fun i => ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 / w j
  have ha : ∀ i j, 0 ≤ a i j := fun _ _ => mul_nonneg (norm_nonneg _) (le_of_lt (hw _))
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (le_of_lt (hw j))
  have hab : ∀ i, (∑ j, a i j) ≤ L * w i := hrow
  have hsumprod : ∀ i,
      (∑ j, a i j * b i j) = ∑ j, ‖A i j‖ * ‖v j‖ := by
    intro i
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a, b]
    field_simp [ne_of_gt (hw j)]
  have hsumSq : ∀ i, (∑ j, a i j * b i j ^ 2) = c i := by
    intro i
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a, b, c]
    field_simp [ne_of_gt (hw j)]
  have hpoint : ∀ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ L * w i * c i := by
    intro i
    have hnorm : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      calc
        ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
        _ = ∑ j, ‖A i j‖ * ‖v j‖ := by simp [norm_mul]
    have hcs := weighted_sum_sq_le Finset.univ (a i) (b i)
      (fun j _ => ha i j)
    have hcs' : (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 ≤ L * w i * c i := by
      rw [← hsumprod i]
      calc
        (∑ j, a i j * b i j) ^ 2 ≤
            (∑ j, a i j) * ∑ j, a i j * b i j ^ 2 := hcs
        _ ≤ (L * w i) * ∑ j, a i j * b i j ^ 2 :=
          mul_le_mul_of_nonneg_right (hab i)
            (Finset.sum_nonneg fun j _ => mul_nonneg (ha i j) (sq_nonneg _))
        _ = L * w i * c i := by rw [hsumSq i]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm |>.trans hcs'
  calc
    (∑ i, ‖(A *ᵥ v) i‖ ^ 2) ≤ ∑ i, L * w i * c i :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = L * ∑ j, (∑ i, w i * ‖A i j‖) * ‖v j‖ ^ 2 / w j := by
      calc
        (∑ i, L * w i * c i) =
            ∑ i, ∑ j, (L * w i) * (‖A i j‖ * ‖v j‖ ^ 2 / w j) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [c]
              rw [Finset.mul_sum]
        _ = ∑ j, ∑ i, (L * w i) * (‖A i j‖ * ‖v j‖ ^ 2 / w j) :=
          Finset.sum_comm
        _ = ∑ j, L * ((∑ i, w i * ‖A i j‖) * ‖v j‖ ^ 2 / w j) := by
          apply Finset.sum_congr rfl
          intro j _
          calc
            (∑ i, (L * w i) * (‖A i j‖ * ‖v j‖ ^ 2 / w j)) =
                (L * ‖v j‖ ^ 2 / w j) * ∑ i, w i * ‖A i j‖ := by
                  calc
                    _ = ∑ i, (L * ‖v j‖ ^ 2 / w j) * (w i * ‖A i j‖) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      ring
                    _ = _ := by rw [← Finset.mul_sum]
            _ = L * ((∑ i, w i * ‖A i j‖) * ‖v j‖ ^ 2 / w j) := by ring
        _ = L * ∑ j, (∑ i, w i * ‖A i j‖) * ‖v j‖ ^ 2 / w j := by
          rw [← Finset.mul_sum]
    _ ≤ L * ∑ j, (L * w j) * ‖v j‖ ^ 2 / w j := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro j _
      have hmul := mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg (‖v j‖))
      exact div_le_div_of_nonneg_right hmul (le_of_lt (hw j))
    _ = L ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
      have hcollapse :
          (∑ j, (L * w j) * ‖v j‖ ^ 2 / w j) = L * ∑ j, ‖v j‖ ^ 2 := by
        calc
          (∑ j, (L * w j) * ‖v j‖ ^ 2 / w j) =
              ∑ j, L * ‖v j‖ ^ 2 := by
                apply Finset.sum_congr rfl
                intro j _
                field_simp [ne_of_gt (hw j)]
          _ = L * ∑ j, ‖v j‖ ^ 2 := by rw [Finset.mul_sum]
      calc
        L * ∑ j, (L * w j) * ‖v j‖ ^ 2 / w j =
            L * (L * ∑ j, ‖v j‖ ^ 2) := by rw [hcollapse]
        _ = _ := by ring

lemma lag_unit_small_perturbation {R : Type*} [Fintype R] [DecidableEq R]
    (B J M A : Matrix R R ℂ) (L K : ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hsmall : L * K < 1)
    (hupdate : A = B - J)
    (hMB : ∀ v i, (M *ᵥ (B *ᵥ v)) i = v i)
    (hMrow : ∀ i, ∑ j, ‖M i j‖ ≤ L)
    (hJrow : ∀ i, ∑ j, ‖J i j‖ ≤ K) :
    IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hMBmat : M * B = 1 := by
    ext i j
    have h := hMB (Pi.single j 1) i
    rw [Matrix.mulVec_mulVec] at h
    change (M * B) i j = if i = j then 1 else 0
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  intro v w hvw
  have hzero : A *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw]
    simp
  have hMA : M * A = 1 - M * J := by
    rw [hupdate, Matrix.mul_sub, hMBmat]
  have hAprod : (M * A) *ᵥ (v - w) = 0 := by
    calc
      (M * A) *ᵥ (v - w) = M *ᵥ (A *ᵥ (v - w)) := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hzero]; simp
  have hIminus : (1 - M * J) *ᵥ (v - w) = 0 := by rw [← hMA]; exact hAprod
  have hsubzero : (v - w) - (M * J) *ᵥ (v - w) = 0 := by
    simpa [Matrix.sub_mulVec] using hIminus
  have hdiff : v - w = M *ᵥ (J *ᵥ (v - w)) := by
    calc
      v - w = (M * J) *ᵥ (v - w) := sub_eq_zero.mp hsubzero
      _ = M *ᵥ (J *ᵥ (v - w)) := by rw [Matrix.mulVec_mulVec]
  have hJbound := matrix_pi_norm_mulVec_le J (v - w) K hK hJrow
  have hMbound := matrix_pi_norm_mulVec_le M (J *ᵥ (v - w)) L hL hMrow
  have hnorm : ‖v - w‖ ≤ L * K * ‖v - w‖ := by
    calc
      ‖v - w‖ = ‖M *ᵥ (J *ᵥ (v - w))‖ := by rw [← hdiff]
      _ ≤ L * ‖J *ᵥ (v - w)‖ := hMbound
      _ ≤ L * (K * ‖v - w‖) := mul_le_mul_of_nonneg_left hJbound hL
      _ = L * K * ‖v - w‖ := by ring
  have hzeroNorm : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  have hdiffZero : v - w = 0 := norm_eq_zero.mp hzeroNorm
  exact sub_eq_zero.mp hdiffZero

lemma sum_norm_add_sq_le {α : Type*} (s : Finset α)
    (u v : α → ℂ) :
    (∑ i ∈ s, ‖u i + v i‖ ^ 2) ≤
      2 * ∑ i ∈ s, ‖u i‖ ^ 2 + 2 * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  calc
    ∑ i ∈ s, ‖u i + v i‖ ^ 2 ≤ ∑ i ∈ s, (‖u i‖ + ‖v i‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (norm_add_le _ _)
    _ ≤ 2 * ∑ i ∈ s, ‖u i‖ ^ 2 + 2 * ∑ i ∈ s, ‖v i‖ ^ 2 := by
      calc
        ∑ i ∈ s, (‖u i‖ + ‖v i‖) ^ 2 ≤
            ∑ i ∈ s, (2 * ‖u i‖ ^ 2 + 2 * ‖v i‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro i hi
              nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]
        _ = 2 * ∑ i ∈ s, ‖u i‖ ^ 2 + 2 * ∑ i ∈ s, ‖v i‖ ^ 2 := by
              simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

lemma matrix_array_sq_le {P : Type*} [Fintype P]
    (S : Finset P) (A : AndersonAC.S45.CMat P) (Y : P → P → ℂ) (L B : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hA : ∀ i, ∑ j, ‖A i j‖ ≤ L)
    (hY : ∀ j, ∑ x ∈ S, ‖Y j x‖ ^ 2 ≤ B) :
    ∀ i, ∑ x ∈ S, ‖(A *ᵥ fun j => Y j x) i‖ ^ 2 ≤ L ^ 2 * B := by
  intro i
  let a : P → ℝ := fun j => ‖A i j‖
  have ha : ∀ j, 0 ≤ a j := fun j => norm_nonneg _
  have hrowA : ∑ j, a j ≤ L := by simpa [a] using hA i
  have hx : ∀ x, ‖(A *ᵥ fun j => Y j x) i‖ ^ 2 ≤
      L * ∑ j, a j * ‖Y j x‖ ^ 2 := by
    intro x
    change ‖∑ j, A i j * Y j x‖ ^ 2 ≤ _
    have hsum : ‖∑ j, A i j * Y j x‖ ≤ ∑ j, a j * ‖Y j x‖ := by
      calc
        ‖∑ j, A i j * Y j x‖ ≤ ∑ j, ‖A i j * Y j x‖ := norm_sum_le _ _
        _ = ∑ j, a j * ‖Y j x‖ := by simp [a]
    have hcs := weighted_sum_sq_le Finset.univ a (fun j => ‖Y j x‖)
      (fun j _ => ha j)
    have hnonneg : 0 ≤ ∑ j, a j * ‖Y j x‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (sq_nonneg _)
    have hsum' : (∑ j, a j * ‖Y j x‖) ^ 2 ≤
        L * ∑ j, a j * ‖Y j x‖ ^ 2 := by
      calc
        (∑ j, a j * ‖Y j x‖) ^ 2 ≤
            (∑ j, a j) * ∑ j, a j * ‖Y j x‖ ^ 2 := hcs
        _ ≤ L * ∑ j, a j * ‖Y j x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hrowA hnonneg
    have hwt : 0 ≤ ∑ j, a j * ‖Y j x‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (norm_nonneg _)
    have hsq := (sq_le_sq₀ (norm_nonneg _) hwt).2 hsum
    exact hsq.trans hsum'
  have hpoint : ∀ x, ‖(A *ᵥ fun j => Y j x) i‖ ^ 2 ≤
      L * ∑ j, a j * ‖Y j x‖ ^ 2 := hx
  calc
    ∑ x ∈ S, ‖(A *ᵥ fun j => Y j x) i‖ ^ 2 ≤
        ∑ x ∈ S, L * ∑ j, a j * ‖Y j x‖ ^ 2 := by
          exact Finset.sum_le_sum fun x hx => hpoint x
    _ = L * ∑ x ∈ S, ∑ j, a j * ‖Y j x‖ ^ 2 := by
          rw [← Finset.mul_sum]
    _ = L * ∑ j, a j * ∑ x ∈ S, ‖Y j x‖ ^ 2 := by
          rw [Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
    _ ≤ L * (L * B) := by
          apply mul_le_mul_of_nonneg_left _ hL
          calc
            ∑ j, a j * ∑ x ∈ S, ‖Y j x‖ ^ 2 ≤ ∑ j, a j * B := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hY j) (ha j)
            _ = (∑ j, a j) * B := by rw [← Finset.sum_mul]
            _ ≤ L * B := mul_le_mul_of_nonneg_right hrowA hB
    _ = L ^ 2 * B := by ring

lemma matrix_l2sq_mulVec_le {P : Type*} [Fintype P] [DecidableEq P]
    (A : AndersonAC.S45.CMat P) (v : P → ℂ) :
    (∑ i, ‖(A *ᵥ v) i‖ ^ 2) ≤ ‖A‖ ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
  let vE : EuclideanSpace ℂ P := (EuclideanSpace.equiv P ℂ).symm v
  have hnorm := A.l2_opNorm_mulVec vE
  have hnorm2 : ‖(EuclideanSpace.equiv P ℂ).symm (A *ᵥ vE)‖ ^ 2 ≤
      (‖A‖ * ‖vE‖) ^ 2 := by
    exact (sq_le_sq₀ (a := ‖(EuclideanSpace.equiv P ℂ).symm (A *ᵥ vE)‖)
      (b := ‖A‖ * ‖vE‖) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  have hin : ‖vE‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [vE]
  have hout : ‖(EuclideanSpace.equiv P ℂ).symm (A *ᵥ vE)‖ ^ 2 =
      ∑ i, ‖(A *ᵥ v) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [vE, EuclideanSpace.equiv, Matrix.mulVec]
  calc
    (∑ i, ‖(A *ᵥ v) i‖ ^ 2) = ‖(EuclideanSpace.equiv P ℂ).symm (A *ᵥ vE)‖ ^ 2 := hout.symm
    _ ≤ (‖A‖ * ‖vE‖) ^ 2 := hnorm2
    _ = ‖A‖ ^ 2 * ∑ j, ‖v j‖ ^ 2 := by rw [← hin]; ring

lemma diagonal_h_mulVec {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (u : P → ℂ) (i x : P) :
    (((diagonal (fun j => h i j) * h) *ᵥ (diagonal (fun j => h i j) *ᵥ u)) x) =
      h i x * ∑ j, h x j * h i j * u j := by
  have hdu (j : P) : (diagonal (fun k => h i k) *ᵥ u) j = h i j * u j := by
    rw [Matrix.mulVec_apply_eq_sum]
    simp [diagonal_apply]
  calc
    _ = ∑ j, ((diagonal (fun k => h i k) * h) x j) *
        (diagonal (fun k => h i k) *ᵥ u) j := by rfl
    _ = ∑ j, (h i x * h x j) * (h i j * u j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Matrix.mul_apply, diagonal_apply, hdu]
    _ = h i x * ∑ j, h x j * h i j * u j := by
      calc
        _ = ∑ j, h i x * (h x j * (h i j * u j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = h i x * ∑ j, h x j * h i j * u j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

lemma diagonal_mulVec_apply {P : Type*} [Fintype P] [DecidableEq P]
    (v u : P → ℂ) (i : P) : (diagonal v *ᵥ u) i = v i * u i := by
  rw [Matrix.mulVec_apply_eq_sum]
  simp [diagonal_apply]

lemma sum_subset_univ_le {P : Type*} [Fintype P]
    (S : Finset P) (f : P → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ S, f x) ≤ ∑ x, f x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun x hxS hxU => hf x)

def lagJLinear {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (c : P → ℂ) (W : P → P → ℂ)
    (i x : P) : ℂ :=
  if i = x then 0 else
    c x * h i x * ∑ j, (if j = x then 0 else h i j * h x j * W j x)

def lagJQuadratic {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (d : P → ℂ) (W : P → P → ℂ)
    (i x : P) : ℂ :=
  if i = x then 0 else
    d x * h i x ^ 2 * ∑ j, (if j = x then 0 else h x j ^ 2 * W j x)

def lagJApply {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (c d : P → ℂ) (W : P → P → ℂ)
    (i x : P) : ℂ :=
  lagJLinear h c W i x + lagJQuadratic h d W i x

lemma sum_ite_mul_left {P : Type*} [Fintype P] [DecidableEq P]
    (x : P) (a : ℂ) (f : P → ℂ) :
    (∑ j, (if j = x then (0 : ℂ) else a * f j)) =
      a * (∑ j, (if j = x then (0 : ℂ) else f j)) := by
  classical
  calc
    ∑ j, (if j = x then (0 : ℂ) else a * f j) =
        ∑ j, (a * (if j = x then (0 : ℂ) else f j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hjx : j = x <;> simp [hjx]
    _ = a * (∑ j, (if j = x then (0 : ℂ) else f j)) := by
      rw [← Finset.mul_sum]

lemma sum_ite_eq_sum_sub {P : Type*} [Fintype P] [DecidableEq P]
    (x : P) (f : P → ℂ) :
    (∑ j, (if j = x then (0 : ℂ) else f j)) = (∑ j, f j) - f x := by
  have hs : (∑ j, (if j = x then (0 : ℂ) else f j)) =
      ∑ j ∈ Finset.univ.erase x, f j := by
    calc
      _ = ∑ j, if j ∈ Finset.univ.erase x then f j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjx : j = x <;> simp [hjx]
      _ = ∑ j ∈ Finset.univ.erase x, f j := Finset.sum_ite_mem_eq _ _
  rw [hs, eq_sub_iff_add_eq]
  exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ x)

lemma lagJLinear_const_decomp {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (c : P → ℂ) (u : P → ℂ) (i x : P) :
    lagJLinear h c (fun j _ => u j) i x =
      if i = x then 0 else c x *
        ((((diagonal (fun j => h i j) * h) *ᵥ
          (diagonal (fun j => h i j) *ᵥ u)) x) - h i x ^ 2 * h x x * u x) := by
  by_cases hix : i = x
  · simp [lagJLinear, hix]
  · simp only [lagJLinear, hix]
    rw [sum_ite_eq_sum_sub, diagonal_h_mulVec]
    simp only [ite_false]
    have hsums : (∑ j, h i j * h x j * u j) =
        ∑ j, h x j * h i j * u j := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsums]
    ring

lemma diagonal_u_energy_le {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (u : P → ℂ) (R U : ℝ)
    (hR : 0 ≤ R) (hU : 0 ≤ U)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hu : ∀ j, ‖u j‖ ≤ U) (i : P) :
    ∑ j, ‖(diagonal (fun k => h i k) *ᵥ u) j‖ ^ 2 ≤ R * U ^ 2 := by
  calc
    ∑ j, ‖(diagonal (fun k => h i k) *ᵥ u) j‖ ^ 2 =
        ∑ j, ‖h i j‖ ^ 2 * ‖u j‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [diagonal_mulVec_apply, norm_mul]
          ring
    _ ≤ ∑ j, ‖h i j‖ ^ 2 * U ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left
            ((sq_le_sq₀ (norm_nonneg _) hU).mpr (hu j)) (sq_nonneg _)
    _ = (∑ j, ‖h i j‖ ^ 2) * U ^ 2 := by rw [← Finset.sum_mul]
    _ ≤ R * U ^ 2 := mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)

lemma diagonal_h_u_energy_le {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (u : P → ℂ) (R T U : ℝ)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hTstar : ∀ i, ‖diagonal (fun j => h i j) * h‖ ^ 2 ≤ T)
    (hu : ∀ j, ‖u j‖ ≤ U) (i : P) :
    ∑ x, ‖((diagonal (fun j => h i j) * h) *ᵥ
      (diagonal (fun j => h i j) *ᵥ u)) x‖ ^ 2 ≤ T * R * U ^ 2 := by
  have hdu := diagonal_u_energy_le h u R U hR hU hrow hu i
  calc
    ∑ x, ‖((diagonal (fun j => h i j) * h) *ᵥ
        (diagonal (fun j => h i j) *ᵥ u)) x‖ ^ 2 ≤
      ‖diagonal (fun j => h i j) * h‖ ^ 2 *
        ∑ j, ‖(diagonal (fun j => h i j) *ᵥ u) j‖ ^ 2 :=
      matrix_l2sq_mulVec_le _ _
    _ ≤ ‖diagonal (fun j => h i j) * h‖ ^ 2 * (R * U ^ 2) :=
      mul_le_mul_of_nonneg_left hdu (sq_nonneg _)
    _ ≤ T * (R * U ^ 2) :=
      mul_le_mul_of_nonneg_right (hTstar i) (mul_nonneg hR (sq_nonneg _))
    _ = T * R * U ^ 2 := by ring

lemma lagJLinear_const_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (c : P → ℂ) (u : P → ℂ)
    (R H T D U A : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hA : 0 ≤ A)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hfour : ∀ i, ∑ j, ‖h i j‖ ^ 4 ≤ H)
    (hTstar : ∀ i, ‖diagonal (fun j => h i j) * h‖ ^ 2 ≤ T)
    (hdiag : ∀ i, ‖h i i‖ ≤ D)
    (hu : ∀ j, ‖u j‖ ≤ U) (hcoef : ∀ x, ‖c x‖ ≤ A) :
    ∀ i, ∑ x ∈ S, ‖lagJLinear h c (fun j _ => u j) i x‖ ^ 2 ≤
      2 * A ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H) := by
  intro i
  let full : P → ℂ := fun x =>
    ((diagonal (fun j => h i j) * h) *ᵥ (diagonal (fun j => h i j) *ᵥ u)) x
  let rem : P → ℂ := fun x => h i x ^ 2 * h x x * u x
  have hfull : ∑ x, ‖full x‖ ^ 2 ≤ T * R * U ^ 2 := by
    simpa [full] using diagonal_h_u_energy_le h u R T U hR hT hU hrow hTstar hu i
  have hfullS : ∑ x ∈ S, ‖full x‖ ^ 2 ≤ T * R * U ^ 2 :=
    (sum_subset_univ_le S (fun x => ‖full x‖ ^ 2) (fun x => sq_nonneg _)).trans hfull
  have hremPoint : ∀ x, ‖rem x‖ ^ 2 ≤ D ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 := by
    intro x
    have hdiag2 : ‖h x x‖ ^ 2 ≤ D ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hD).mpr (hdiag x)
    have hu2 : ‖u x‖ ^ 2 ≤ U ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hU).mpr (hu x)
    have hval : ‖rem x‖ ^ 2 = ‖h i x‖ ^ 4 * ‖h x x‖ ^ 2 * ‖u x‖ ^ 2 := by
      change ‖h i x ^ 2 * h x x * u x‖ ^ 2 = _
      rw [norm_mul, norm_mul, norm_pow]
      ring
    rw [hval]
    calc
      ‖h i x‖ ^ 4 * ‖h x x‖ ^ 2 * ‖u x‖ ^ 2 ≤
          ‖h i x‖ ^ 4 * D ^ 2 * U ^ 2 := by
            gcongr
      _ = D ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 := by ring
  have hrem : ∑ x ∈ S, ‖rem x‖ ^ 2 ≤ D ^ 2 * U ^ 2 * H := by
    calc
      ∑ x ∈ S, ‖rem x‖ ^ 2 ≤ ∑ x ∈ S, D ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 :=
        Finset.sum_le_sum fun x hx => hremPoint x
      _ = D ^ 2 * U ^ 2 * ∑ x ∈ S, ‖h i x‖ ^ 4 := by rw [← Finset.mul_sum]
      _ ≤ D ^ 2 * U ^ 2 * H := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        exact (sum_subset_univ_le S (fun x => ‖h i x‖ ^ 4)
          (fun x => pow_nonneg (norm_nonneg _) _)).trans (hfour i)
  have hpoint : ∀ x, ‖lagJLinear h c (fun j _ => u j) i x‖ ^ 2 ≤
      2 * A ^ 2 * (‖full x‖ ^ 2 + ‖rem x‖ ^ 2) := by
    intro x
    have hnorm : ‖lagJLinear h c (fun j _ => u j) i x‖ ≤
        A * (‖full x‖ + ‖rem x‖) := by
      rw [lagJLinear_const_decomp]
      by_cases hix : i = x
      · simp [hix]
        positivity
      · simp only [hix, if_false]
        calc
          ‖c x * (full x - rem x)‖ = ‖c x‖ * ‖full x - rem x‖ := by rw [norm_mul]
          _ ≤ ‖c x‖ * (‖full x‖ + ‖rem x‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
          _ ≤ A * (‖((diagonal (fun j => h i j) * h) *ᵥ
                (diagonal (fun j => h i j) *ᵥ u)) x‖ + ‖h i x ^ 2 * h x x * u x‖) :=
            mul_le_mul_of_nonneg_right (hcoef x)
              (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have hnonneg : 0 ≤ ‖full x‖ + ‖rem x‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA hnonneg)).mpr hnorm
    nlinarith [sq_nonneg (‖full x‖ - ‖rem x‖)]
  calc
    ∑ x ∈ S, ‖lagJLinear h c (fun j _ => u j) i x‖ ^ 2 ≤
        ∑ x ∈ S, 2 * A ^ 2 * (‖full x‖ ^ 2 + ‖rem x‖ ^ 2) :=
      Finset.sum_le_sum fun x hx => hpoint x
    _ = 2 * A ^ 2 *
        (∑ x ∈ S, ‖full x‖ ^ 2 + ∑ x ∈ S, ‖rem x‖ ^ 2) := by
      calc
        ∑ x ∈ S, 2 * A ^ 2 * (‖full x‖ ^ 2 + ‖rem x‖ ^ 2) =
            ∑ x ∈ S, (2 * A ^ 2 * ‖full x‖ ^ 2 + 2 * A ^ 2 * ‖rem x‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
        _ = (∑ x ∈ S, 2 * A ^ 2 * ‖full x‖ ^ 2) +
            (∑ x ∈ S, 2 * A ^ 2 * ‖rem x‖ ^ 2) := Finset.sum_add_distrib
        _ = (2 * A ^ 2 * ∑ x ∈ S, ‖full x‖ ^ 2) +
            (2 * A ^ 2 * ∑ x ∈ S, ‖rem x‖ ^ 2) := by
              rw [Finset.mul_sum, Finset.mul_sum]
        _ = _ := by ring
    _ ≤ 2 * A ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hfullS hrem) (by positivity)

lemma lagJQuadratic_const_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (d : P → ℂ) (u : P → ℂ)
    (R H U B : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hfour : ∀ i, ∑ j, ‖h i j‖ ^ 4 ≤ H)
    (hu : ∀ j, ‖u j‖ ≤ U) (hcoef : ∀ x, ‖d x‖ ≤ B) :
    ∀ i, ∑ x ∈ S, ‖lagJQuadratic h d (fun j _ => u j) i x‖ ^ 2 ≤
      B ^ 2 * R ^ 2 * U ^ 2 * H := by
  intro i
  have hinner : ∀ x, ‖∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ≤ R * U := by
    intro x
    calc
      ‖∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ≤
          ∑ j, ‖if j = x then 0 else h x j ^ 2 * u j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖h x j‖ ^ 2 * U := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hjx : j = x
        · simp [hjx]
          positivity
        · calc
            ‖if j = x then (0 : ℂ) else h x j ^ 2 * u j‖ =
                ‖h x j‖ ^ 2 * ‖u j‖ := by simp [hjx, norm_mul, norm_pow]
            _ ≤ ‖h x j‖ ^ 2 * U :=
              mul_le_mul_of_nonneg_left (hu j) (sq_nonneg _)
      _ = (∑ j, ‖h x j‖ ^ 2) * U := by rw [Finset.sum_mul]
      _ ≤ R * U := mul_le_mul_of_nonneg_right (hrow x) hU
  have hpoint : ∀ x ∈ S, ‖lagJQuadratic h d (fun j _ => u j) i x‖ ^ 2 ≤
      B ^ 2 * R ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 := by
    intro x hx
    by_cases hix : i = x
    · simp [lagJQuadratic, hix]
      positivity
    · have hcoef2 : ‖d x‖ ^ 2 ≤ B ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hcoef x)
      have hinner2 : ‖∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ^ 2 ≤
          R ^ 2 * U ^ 2 := by
        have hn := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR hU)).mpr (hinner x)
        simpa [mul_pow] using hn
      have hval : ‖d x * h i x ^ 2 *
          ∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ^ 2 ≤
          B ^ 2 * R ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 := by
        calc
          _ = ‖d x‖ ^ 2 * ‖h i x‖ ^ 4 *
              ‖∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ^ 2 := by
                rw [norm_mul, norm_mul, norm_pow]
                ring
          _ ≤ B ^ 2 * R ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 := by
                calc
                  ‖d x‖ ^ 2 * ‖h i x‖ ^ 4 *
                      ‖∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ^ 2 =
                    ‖d x‖ ^ 2 * (‖h i x‖ ^ 4 *
                      ‖∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ^ 2) := by ring
                  _ ≤ B ^ 2 * (‖h i x‖ ^ 4 *
                      ‖∑ j, if j = x then 0 else h x j ^ 2 * u j‖ ^ 2) :=
                    mul_le_mul_of_nonneg_right hcoef2
                      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))
                  _ ≤ B ^ 2 * (‖h i x‖ ^ 4 * (R ^ 2 * U ^ 2)) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hinner2 (pow_nonneg (norm_nonneg _) _))
                      (sq_nonneg _)
                  _ = B ^ 2 * R ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 := by ring
      simpa [lagJQuadratic, hix] using hval
  have hcoefNonneg : 0 ≤ B ^ 2 * R ^ 2 * U ^ 2 := by positivity
  calc
    ∑ x ∈ S, ‖lagJQuadratic h d (fun j _ => u j) i x‖ ^ 2 ≤
        ∑ x ∈ S, B ^ 2 * R ^ 2 * U ^ 2 * ‖h i x‖ ^ 4 :=
      Finset.sum_le_sum fun x hx => hpoint x hx
    _ = B ^ 2 * R ^ 2 * U ^ 2 * ∑ x ∈ S, ‖h i x‖ ^ 4 := by rw [← Finset.mul_sum]
    _ ≤ B ^ 2 * R ^ 2 * U ^ 2 * H :=
      mul_le_mul_of_nonneg_left
        (sum_subset_univ_le S (fun x => ‖h i x‖ ^ 4)
          (fun x => pow_nonneg (norm_nonneg _) _)
          |>.trans (hfour i)) hcoefNonneg

lemma lagJApply_const_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (c d : P → ℂ) (u : P → ℂ)
    (R H T D U A B : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hfour : ∀ i, ∑ j, ‖h i j‖ ^ 4 ≤ H)
    (hTstar : ∀ i, ‖diagonal (fun j => h i j) * h‖ ^ 2 ≤ T)
    (hdiag : ∀ i, ‖h i i‖ ≤ D) (hu : ∀ j, ‖u j‖ ≤ U)
    (hcoef : ∀ x, ‖c x‖ ≤ A) (hcoef' : ∀ x, ‖d x‖ ≤ B) :
    ∀ i, ∑ x ∈ S, ‖lagJApply h c d (fun j _ => u j) i x‖ ^ 2 ≤
      4 * A ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H) +
        2 * B ^ 2 * R ^ 2 * U ^ 2 * H := by
  intro i
  have hlin := lagJLinear_const_array_sq_le S h c u R H T D U A
    hR hH hT hD hU hA hrow hfour hTstar hdiag hu hcoef i
  have hquad := lagJQuadratic_const_array_sq_le S h d u R H U B
    hR hH hU hB hrow hfour hu hcoef' i
  calc
    ∑ x ∈ S, ‖lagJApply h c d (fun j _ => u j) i x‖ ^ 2 ≤
        2 * ∑ x ∈ S, ‖lagJLinear h c (fun j _ => u j) i x‖ ^ 2 +
          2 * ∑ x ∈ S, ‖lagJQuadratic h d (fun j _ => u j) i x‖ ^ 2 := by
      simpa [lagJApply] using (sum_norm_add_sq_le S
        (lagJLinear h c (fun j _ => u j) i)
        (lagJQuadratic h d (fun j _ => u j) i))
    _ ≤ 2 * (2 * A ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H)) +
        2 * (B ^ 2 * R ^ 2 * U ^ 2 * H) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlin (by positivity))
        (mul_le_mul_of_nonneg_left hquad (by positivity))
    _ = 4 * A ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H) +
        2 * B ^ 2 * R ^ 2 * U ^ 2 * H := by ring

lemma lagDirect_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (α : P → ℂ)
    (H A t : ℝ) (ht : 0 < t) (hA : 0 ≤ A)
    (hfour : ∀ i, ∑ j, ‖h i j‖ ^ 4 ≤ H)
    (hα : ∀ x, ‖α x‖ ≤ A / Real.sqrt t) :
    ∀ i, ∑ x ∈ S, ‖if i = x then 0 else α x * h i x ^ 2‖ ^ 2 ≤ A ^ 2 / t * H := by
  intro i
  have hpoint : ∀ x ∈ S, ‖if i = x then (0 : ℂ) else α x * h i x ^ 2‖ ^ 2 ≤
      A ^ 2 / t * ‖h i x‖ ^ 4 := by
    intro x hx
    by_cases hix : i = x
    · simp [hix]
      positivity
    · have hα2 : ‖α x‖ ^ 2 ≤ (A / Real.sqrt t) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (div_nonneg hA (Real.sqrt_nonneg _))).mpr (hα x)
      calc
        ‖if i = x then (0 : ℂ) else α x * h i x ^ 2‖ ^ 2 =
            ‖α x‖ ^ 2 * ‖h i x‖ ^ 4 := by
              rw [if_neg hix, norm_mul, norm_pow]
              ring
        _ ≤ (A / Real.sqrt t) ^ 2 * ‖h i x‖ ^ 4 :=
          mul_le_mul_of_nonneg_right hα2 (pow_nonneg (norm_nonneg _) _)
        _ = A ^ 2 / t * ‖h i x‖ ^ 4 := by
          rw [div_pow, Real.sq_sqrt ht.le]
  calc
    ∑ x ∈ S, ‖if i = x then 0 else α x * h i x ^ 2‖ ^ 2 ≤
        ∑ x ∈ S, A ^ 2 / t * ‖h i x‖ ^ 4 :=
      Finset.sum_le_sum fun x hx => hpoint x hx
    _ = A ^ 2 / t * ∑ x ∈ S, ‖h i x‖ ^ 4 := by rw [← Finset.mul_sum]
    _ ≤ A ^ 2 / t * H :=
      mul_le_mul_of_nonneg_left
        (sum_subset_univ_le S (fun x => ‖h i x‖ ^ 4)
          (fun x => pow_nonneg (norm_nonneg _) _)
          |>.trans (hfour i)) (div_nonneg (sq_nonneg A) ht.le)

def lagDirectScaled {P : Type*} [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (z : P → ℝ) (i x : P) : ℂ :=
  if i = x then 0 else
    -((AndersonAC.S45.gamma t s x (z x) +
      s.z t x * (1 - s.K t x x)⁻¹) / (Real.sqrt t : ℂ)) * s.K t i x

def lagForcingScaled {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (z : P → ℝ) (i x : P) : ℂ :=
  lagDirectScaled t s z i x +
    lagJApply (s.h t)
      (fun x => -2 * AndersonAC.S45.gamma t s x (z x))
      (fun x => (AndersonAC.S45.gamma t s x (z x)) ^ 2 -
        (1 - s.K t x x)⁻¹)
      (fun j _ => s.lag t j) i x

lemma lagForcingScaled_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (t : ℝ) (s : AndersonAC.S45.State P) (z : P → ℝ)
    (R H T D U G I Z : ℝ)
    (ht : 0 < t) (htle : t ≤ 1)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hG : 0 ≤ G) (hI : 0 ≤ I) (hZ : 0 ≤ Z)
    (hrow : ∀ i, ∑ j, ‖s.h t i j‖ ^ 2 ≤ R)
    (hfour : ∀ i, ∑ j, ‖s.h t i j‖ ^ 4 ≤ H)
    (hTstar : ∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤ T)
    (hdiag : ∀ i, ‖s.h t i i‖ ≤ D)
    (hlag : ∀ i, ‖s.lag t i‖ ≤ U)
    (hgamma : ∀ x, ‖AndersonAC.S45.gamma t s x (z x)‖ ≤ G)
    (hinv : ∀ x, ‖(1 - s.K t x x)⁻¹‖ ≤ I)
    (hz : ∀ x, ‖s.z t x‖ ≤ Z * Real.sqrt t) :
    ∀ i, ∑ x ∈ S, ‖lagForcingScaled t s z i x‖ ^ 2 ≤
      2 * ((G + Z * I) ^ 2 / t * H) +
        2 * (4 * (2 * G) ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H) +
          2 * (G ^ 2 + I) ^ 2 * R ^ 2 * U ^ 2 * H) := by
  intro i
  let α : P → ℂ := fun x => -((AndersonAC.S45.gamma t s x (z x) +
    s.z t x * (1 - s.K t x x)⁻¹) / (Real.sqrt t : ℂ))
  let c : P → ℂ := fun x => -2 * AndersonAC.S45.gamma t s x (z x)
  let d : P → ℂ := fun x => (AndersonAC.S45.gamma t s x (z x)) ^ 2 -
    (1 - s.K t x x)⁻¹
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrt_le : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 htle
  have hA_nonneg : 0 ≤ G + Z * I := add_nonneg hG (mul_nonneg hZ hI)
  have hα : ∀ x, ‖α x‖ ≤ (G + Z * I) / Real.sqrt t := by
    intro x
    have hza : ‖s.z t x * (1 - s.K t x x)⁻¹‖ ≤ Z * I * Real.sqrt t := by
      calc
        _ = ‖s.z t x‖ * ‖(1 - s.K t x x)⁻¹‖ := norm_mul _ _
        _ ≤ (Z * Real.sqrt t) * I :=
          mul_le_mul (hz x) (hinv x) (norm_nonneg _) (mul_nonneg hZ (Real.sqrt_nonneg _))
        _ = Z * I * Real.sqrt t := by ring
    have hnum : ‖AndersonAC.S45.gamma t s x (z x) +
        s.z t x * (1 - s.K t x x)⁻¹‖ ≤ G + Z * I := by
      calc
        _ ≤ ‖AndersonAC.S45.gamma t s x (z x)‖ +
            ‖s.z t x * (1 - s.K t x x)⁻¹‖ := norm_add_le _ _
        _ ≤ G + Z * I * Real.sqrt t := add_le_add (hgamma x) hza
        _ ≤ G + Z * I := by
          have hmul := mul_le_mul_of_nonneg_right hsqrt_le (mul_nonneg hZ hI)
          nlinarith [hmul]
    change ‖-((AndersonAC.S45.gamma t s x (z x) +
      s.z t x * (1 - s.K t x x)⁻¹) / (Real.sqrt t : ℂ))‖ ≤ _
    rw [norm_neg, norm_div]
    have hdenom : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
      simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hdenom]
    exact div_le_div_of_nonneg_right hnum hsqrt.le
  have hcoeff : ∀ x, ‖c x‖ ≤ 2 * G := by
    intro x
    dsimp [c]
    simpa using (mul_le_mul_of_nonneg_left (hgamma x) (by norm_num : 0 ≤ (2 : ℝ)))
  have hcoeff' : ∀ x, ‖d x‖ ≤ G ^ 2 + I := by
    intro x
    dsimp [d]
    calc
      _ ≤ ‖AndersonAC.S45.gamma t s x (z x) ^ 2‖ +
          ‖(1 - s.K t x x)⁻¹‖ := norm_sub_le _ _
      _ = ‖AndersonAC.S45.gamma t s x (z x)‖ ^ 2 +
          ‖(1 - s.K t x x)⁻¹‖ := by rw [norm_pow]
      _ ≤ G ^ 2 + I := add_le_add (sq_le_sq₀ (norm_nonneg _) hG |>.mpr (hgamma x)) (hinv x)
  have hdirect : ∀ i, ∑ x ∈ S, ‖lagDirectScaled t s z i x‖ ^ 2 ≤
      (G + Z * I) ^ 2 / t * H := by
    have hK (i j : P) : s.K t i j = (s.h t i j) ^ 2 := rfl
    intro i
    simpa [lagDirectScaled, α, hK, mul_comm, mul_left_comm, mul_assoc] using
      (lagDirect_array_sq_le S (s.h t) α H (G + Z * I) t ht hA_nonneg hfour hα i)
  have hJ : ∀ i, ∑ x ∈ S,
      ‖lagJApply (s.h t) c d (fun j _ => s.lag t j) i x‖ ^ 2 ≤
        4 * (2 * G) ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H) +
          2 * (G ^ 2 + I) ^ 2 * R ^ 2 * U ^ 2 * H := by
    intro i
    exact lagJApply_const_array_sq_le S (s.h t) c d (fun j => s.lag t j)
      R H T D U (2 * G) (G ^ 2 + I) hR hH hT hD hU
      (mul_nonneg (by norm_num) hG) (add_nonneg (sq_nonneg G) hI)
      hrow hfour hTstar hdiag hlag hcoeff hcoeff' i
  calc
    ∑ x ∈ S, ‖lagForcingScaled t s z i x‖ ^ 2 ≤
        2 * ∑ x ∈ S, ‖lagDirectScaled t s z i x‖ ^ 2 +
          2 * ∑ x ∈ S, ‖lagJApply (s.h t) c d (fun j _ => s.lag t j) i x‖ ^ 2 := by
      simpa [lagForcingScaled, α, c, d] using
        (sum_norm_add_sq_le S (lagDirectScaled t s z i)
          (lagJApply (s.h t) c d (fun j _ => s.lag t j) i))
    _ ≤ 2 * ((G + Z * I) ^ 2 / t * H) +
        2 * (4 * (2 * G) ^ 2 * (T * R * U ^ 2 + D ^ 2 * U ^ 2 * H) +
          2 * (G ^ 2 + I) ^ 2 * R ^ 2 * U ^ 2 * H) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hdirect i) (by positivity))
        (mul_le_mul_of_nonneg_left (hJ i) (by positivity))

lemma lag_scalarSchur_mulVec_eq {P : Type*} [Fintype P] [DecidableEq P]
    (A : AndersonAC.S45.CMat P) (x : P) (u z : P → ℂ) (hAu : A *ᵥ u = z)
    (ha : A x x ≠ 0) :
    ∀ i : AndersonAC.S45.survivors x,
      (AndersonAC.S45.scalarSchur A x *ᵥ (fun j => u j.val)) i =
        z i.val - A i.val x * (A x x)⁻¹ * z x := by
  let Rset := AndersonAC.S45.survivors x
  let R : Type _ := (↑Rset : Type _)
  have hattach (f : P → ℂ) : (∑ j : R, f j.val) = ∑ j ∈ Rset, f j := by
    simpa [R, Rset] using (Finset.sum_attach (s := Rset) (f := f))
  have hsplit (f : P → ℂ) :
      (∑ j : P, f j) = (∑ j : R, f j.val) + f x := by
    rw [← Finset.univ.sum_erase_add f (Finset.mem_univ x)]
    simpa [Rset, AndersonAC.S45.survivors] using
      congrArg (fun a : ℂ => a + f x) (hattach f).symm
  intro i
  have hrowi : (∑ j : P, A i.val j * u j) = z i.val := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hAu i.val
  have hrowx : (∑ j : P, A x j * u j) = z x := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hAu x
  have hsplit_i := hsplit (fun j => A i.val j * u j)
  have hsplit_x := hsplit (fun j => A x j * u j)
  rw [hrowi] at hsplit_i
  rw [hrowx] at hsplit_x
  have hsum_i : (∑ j : R, A i.val j.val * u j.val) =
      z i.val - A i.val x * u x := by
    calc
      (∑ j : R, A i.val j.val * u j.val) =
          ((∑ j : R, A i.val j.val * u j.val) + A i.val x * u x) -
            A i.val x * u x := by ring
      _ = z i.val - A i.val x * u x := by rw [← hsplit_i]
  have hsum_x : (∑ j : R, A x j.val * u j.val) = z x - A x x * u x := by
    calc
      (∑ j : R, A x j.val * u j.val) =
          ((∑ j : R, A x j.val * u j.val) + A x x * u x) - A x x * u x := by ring
      _ = z x - A x x * u x := by rw [← hsplit_x]
  have hfact :
      (∑ j : R, (A i.val x * (A x x)⁻¹ * A x j.val) * u j.val) =
        A i.val x * (A x x)⁻¹ * (∑ j : R, A x j.val * u j.val) := by
    calc
      _ = ∑ j : R, (A i.val x * (A x x)⁻¹) * (A x j.val * u j.val) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [← Finset.mul_sum]
  calc
    (AndersonAC.S45.scalarSchur A x *ᵥ (fun j => u j.val)) i =
        (∑ j : R, A i.val j.val * u j.val) -
          A i.val x * (A x x)⁻¹ * (∑ j : R, A x j.val * u j.val) := by
      simp only [AndersonAC.S45.scalarSchur, Matrix.mulVec, dotProduct]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, hfact]
    _ = z i.val - A i.val x * (A x x)⁻¹ * z x := by
      rw [hsum_i, hsum_x]
      field_simp [ha]
      ring

lemma lag_restrict_mulVec_apply {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (M : AndersonAC.S45.CMat P) (v : S → ℂ) (i : S) :
    (AndersonAC.S45.restrict M S *ᵥ v) i =
      (M *ᵥ fun j => if hj : j ∈ S then v ⟨j, hj⟩ else 0) i.val := by
  classical
  let f : P → ℂ := fun j => if hj : j ∈ S then M i.val j * v ⟨j, hj⟩ else 0
  have hsub : (∑ j ∈ S, f j) = ∑ j, f j := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j hj hjnot
    simp [f, hjnot]
  have hattach : (∑ j : S, M i.val j.val * v j) = ∑ j ∈ S, f j := by
    calc
      ∑ j : S, M i.val j.val * v j = ∑ j : S, f j.val := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [f, j.property]
      _ = ∑ j ∈ S, f j := Finset.sum_attach (s := S) (f := f)
  calc
    (AndersonAC.S45.restrict M S *ᵥ v) i =
        ∑ j : S, M i.val j.val * v j := by
          simp [Matrix.mulVec, dotProduct, AndersonAC.S45.restrict]
    _ = ∑ j ∈ S, f j := hattach
    _ = ∑ j, f j := hsub
    _ = (M *ᵥ fun j => if hj : j ∈ S then v ⟨j, hj⟩ else 0) i.val := by
          simp [Matrix.mulVec, dotProduct, f]

lemma lag_sum_univ_split {P : Type*} [Fintype P] [DecidableEq P]
    (x : P) (f : P → ℂ) :
    (∑ j : P, f j) = (∑ j : AndersonAC.S45.survivors x, f j.val) + f x := by
  let S := AndersonAC.S45.survivors x
  let R : Type _ := (↑S : Type _)
  have hattach : (∑ j : R, f j.val) = ∑ j ∈ S, f j := by
    simpa [R, S] using (Finset.sum_attach (s := S) (f := f))
  rw [← Finset.univ.sum_erase_add f (Finset.mem_univ x)]
  simpa [R, S, AndersonAC.S45.survivors] using
    congrArg (fun a : ℂ => a + f x) hattach.symm

lemma lag_restrict_scalarSchur_left_inv {P : Type*} [Fintype P] [DecidableEq P]
    (A : AndersonAC.S45.CMat P) (x : P) (hA : IsUnit A) (ha : A x x ≠ 0) :
    ∀ (v : AndersonAC.S45.survivors x → ℂ) (i : AndersonAC.S45.survivors x),
      (AndersonAC.S45.restrict A⁻¹ (AndersonAC.S45.survivors x) *ᵥ
        (AndersonAC.S45.scalarSchur A x *ᵥ v)) i = v i := by
  classical
  intro v i
  let S := AndersonAC.S45.survivors x
  let R : Type _ := (↑S : Type _)
  let B := AndersonAC.S45.scalarSchur A x
  let q : ℂ := ∑ j : R, A x j.val * v j
  let u : P → ℂ := fun j =>
    if hj : j = x then -(A x x)⁻¹ * q else v ⟨j, by simpa [S, AndersonAC.S45.survivors] using hj⟩
  let z : P → ℂ := A *ᵥ u
  have huR : ∀ j : R, u j.val = v j := by
    intro j
    have hjx : j.val ≠ x := by simpa [S, AndersonAC.S45.survivors] using j.property
    simp [u, hjx]
  have hux : u x = -(A x x)⁻¹ * q := by simp [u]
  have hzx : z x = 0 := by
    dsimp [z]
    rw [Matrix.mulVec_apply_eq_sum, lag_sum_univ_split x (fun j => A x j * u j)]
    have hsumR : (∑ j : R, A x j.val * u j.val) = q := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [q, huR j]
    rw [hsumR, hux]
    field_simp [ha]
    ring
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hPA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hPz : A⁻¹ *ᵥ z = u := by
    calc
      A⁻¹ *ᵥ z = A⁻¹ *ᵥ (A *ᵥ u) := rfl
      _ = (A⁻¹ * A) *ᵥ u := by rw [← Matrix.mulVec_mulVec]
      _ = u := by rw [hPA]; simp
  have hsch := lag_scalarSchur_mulVec_eq A x u z (by rfl) ha
  have hvec : (fun j : R => u j.val) = v := funext huR
  have hBz : B *ᵥ v = fun j : R => z j.val := by
    funext j
    have hj := hsch j
    rw [hvec, hzx] at hj
    simp only [mul_zero, sub_zero] at hj
    change (AndersonAC.S45.scalarSchur A x *ᵥ v) j = z j.val
    simpa [B] using hj
  have hfull : (fun j : P => if hj : j ∈ S then (B *ᵥ v) ⟨j, hj⟩ else 0) = z := by
    funext j
    by_cases hj : j ∈ S
    · simp [hBz, hj]
    · have hjx : j = x := by simpa [S, AndersonAC.S45.survivors] using hj
      subst j
      simp [hzx, hj]
  calc
    (AndersonAC.S45.restrict A⁻¹ S *ᵥ (B *ᵥ v)) i =
        (A⁻¹ *ᵥ (fun j : P => if hj : j ∈ S then (B *ᵥ v) ⟨j, hj⟩ else 0)) i.val :=
      lag_restrict_mulVec_apply S A⁻¹ (B *ᵥ v) i
    _ = (A⁻¹ *ᵥ z) i.val := by rw [hfull]
    _ = u i.val := by rw [hPz]
    _ = v i := huR i

theorem lag_delete_A_update {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (ha : 1 - s.K t x x ≠ 0)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    1 - (AndersonAC.S45.deleteState t s x ξ).K t =
      AndersonAC.S45.scalarSchur (1 - s.K t) x -
        AndersonAC.S45.restrict (AndersonAC.S45.Jinc t s x ξ)
          (AndersonAC.S45.survivors x) := by
  let α : ℂ := (Real.sqrt t : ℂ)
  let c : ℂ := (ξ : ℂ) + t * s.r x
  let d : ℂ := 1 + c * s.g x x
  let a : ℂ := 1 - α ^ 2 * s.g x x ^ 2
  let A : AndersonAC.S45.CMat P := 1 - s.K t
  have hα : α ≠ 0 := by
    dsimp [α]
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hd : d ≠ 0 := by simpa [d, c] using hden
  have hKentry (u v : P) : s.K t u v = α ^ 2 * s.g u v ^ 2 := by
    simp [AndersonAC.S45.State.K, AndersonAC.S45.State.h,
      AndersonAC.Blueprint.entrywiseSquare, Pi.smul_apply, smul_eq_mul, α]
    ring
  have hh (u v : P) : s.h t u v = α * s.g u v := by
    simp [AndersonAC.S45.State.h, Pi.smul_apply, smul_eq_mul, α]
  have hAentry (u v : P) : A u v = (if u = v then 1 else 0) - α ^ 2 * s.g u v ^ 2 := by
    simp [A, Matrix.sub_apply, Matrix.one_apply, hKentry]
  have hAxx : A x x = a := by simp [a, hAentry]
  have haA : A x x ≠ 0 := by simpa [A, Matrix.one_apply] using ha
  have ha' : a ≠ 0 := by simpa [hAxx] using haA
  ext i j
  have hix : (i.val : P) ≠ x := by simpa [AndersonAC.S45.survivors] using i.property
  have hxj : x ≠ (j.val : P) := by
    have hjx : (j.val : P) ≠ x := by simpa [AndersonAC.S45.survivors] using j.property
    exact hjx.symm
  let δ : ℂ := if i.val = j.val then 1 else 0
  have hAij : A i.val j.val = δ - α ^ 2 * s.g i.val j.val ^ 2 := by
    simpa [δ] using hAentry i.val j.val
  have hAix : A i.val x = -(α ^ 2 * s.g i.val x ^ 2) := by
    rw [hAentry]
    simp [hix]
  have hAxj : A x j.val = -(α ^ 2 * s.g x j.val ^ 2) := by
    rw [hAentry]
    simp [hxj]
  have hQ : AndersonAC.S45.scalarSchur A x i j =
      δ - α ^ 2 * s.g i.val j.val ^ 2 -
        α ^ 4 * s.g i.val x ^ 2 * s.g x j.val ^ 2 / a := by
    unfold AndersonAC.S45.scalarSchur
    rw [hAij, hAix, hAxx, hAxj]
    dsimp [δ]
    ring
  have hJ : (AndersonAC.S45.restrict (AndersonAC.S45.Jinc t s x ξ)
      (AndersonAC.S45.survivors x)) i j =
      -2 * AndersonAC.S45.gamma t s x ξ * (α * s.g i.val x) *
          (α * s.g i.val j.val) * (α * s.g x j.val) +
        (AndersonAC.S45.gamma t s x ξ ^ 2 - a⁻¹) *
          (α ^ 2 * s.g i.val x ^ 2) * (α ^ 2 * s.g x j.val ^ 2) := by
    change AndersonAC.S45.Jinc t s x ξ i.val j.val = _
    simp only [AndersonAC.S45.Jinc, AndersonAC.S45.pad, i.property, j.property]
    rw [hh i.val x, hh i.val j.val, hh x j.val,
      hKentry i.val x, hKentry x j.val, hKentry x x]
    simp [a]
  have hKnew : (AndersonAC.S45.deleteState t s x ξ).K t i j =
      α ^ 2 * (s.g i.val j.val - c * s.g i.val x * s.g x j.val / d) ^ 2 := by
    change ((Real.sqrt t : ℂ) * (AndersonAC.S45.deleteState t s x ξ).g i j) ^ 2 = _
    simp [AndersonAC.S45.deleteState, α, c, d]
    ring
  have hden' : α * d ≠ 0 := mul_ne_zero hα hd
  calc
    (1 - (AndersonAC.S45.deleteState t s x ξ).K t) i j =
        δ - α ^ 2 * (s.g i.val j.val - c * s.g i.val x * s.g x j.val / d) ^ 2 := by
          simp [Matrix.sub_apply, Matrix.one_apply, hKnew, δ]
    _ = (AndersonAC.S45.scalarSchur A x i j) -
        (AndersonAC.S45.restrict (AndersonAC.S45.Jinc t s x ξ)
          (AndersonAC.S45.survivors x) i j) := by
          rw [hQ, hJ]
          dsimp [AndersonAC.S45.gamma, c, d, a, α]
          have hroot : (Real.sqrt t : ℂ) ≠ 0 := by simpa [α] using hα
          have hγden : (Real.sqrt t : ℂ) *
              (1 + ((ξ : ℂ) + t * s.r x) * s.g x x) ≠ 0 := mul_ne_zero hroot hden
          field_simp [hd, ha', hroot, hγden]
          ring
    _ = (AndersonAC.S45.scalarSchur A x -
        AndersonAC.S45.restrict (AndersonAC.S45.Jinc t s x ξ)
          (AndersonAC.S45.survivors x)) i j := by
          simp [Matrix.sub_apply]

lemma lagJinc_rowSum_bound {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (x : P) (ξ : ℝ)
    (R M G I : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (hG : 0 ≤ G) (hI : 0 ≤ I)
    (hrow : ∀ i, ∑ j, ‖s.h t i j‖ ^ 2 ≤ R)
    (hmax : ∀ i j, ‖s.h t i j‖ ≤ M)
    (hgamma : ‖AndersonAC.S45.gamma t s x ξ‖ ≤ G)
    (hinv : ‖(1 - s.K t x x)⁻¹‖ ≤ I) :
    ∀ i, ∑ j ∈ AndersonAC.S45.survivors x, ‖AndersonAC.S45.Jinc t s x ξ i j‖ ≤
      2 * G * M * R + (G ^ 2 + I) * M ^ 2 * R := by
  have hη : ‖(AndersonAC.S45.gamma t s x ξ) ^ 2 -
      (1 - s.K t x x)⁻¹‖ ≤ G ^ 2 + I := by
    calc
      _ ≤ ‖(AndersonAC.S45.gamma t s x ξ) ^ 2‖ +
          ‖(1 - s.K t x x)⁻¹‖ := norm_sub_le _ _
      _ = ‖AndersonAC.S45.gamma t s x ξ‖ ^ 2 +
          ‖(1 - s.K t x x)⁻¹‖ := by rw [norm_pow]
      _ ≤ G ^ 2 + I := add_le_add
        ((sq_le_sq₀ (norm_nonneg _) hG).mpr hgamma) hinv
  intro i
  have hCS : ∑ j, ‖s.h t i j‖ * ‖s.h t x j‖ ≤ R := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => ‖s.h t i j‖) (fun j => ‖s.h t x j‖)
    have hsq : (∑ j, ‖s.h t i j‖ * ‖s.h t x j‖) ^ 2 ≤ R ^ 2 := by
      calc
        _ ≤ (∑ j, ‖s.h t i j‖ ^ 2) * ∑ j, ‖s.h t x j‖ ^ 2 := hcs
        _ ≤ R * R := mul_le_mul (hrow i) (hrow x)
          (Finset.sum_nonneg fun j _ => sq_nonneg _) hR
        _ = R ^ 2 := by ring
    have hsumNonneg : 0 ≤ ∑ j, ‖s.h t i j‖ * ‖s.h t x j‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact (sq_le_sq₀ hsumNonneg hR).mp hsq
  have hKi : ‖s.K t i x‖ ≤ M ^ 2 := by
    simp [AndersonAC.S45.State.K, AndersonAC.Blueprint.entrywiseSquare, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmax i x) 2
  have hKxj : ∀ j, ‖s.K t x j‖ ≤ ‖s.h t x j‖ ^ 2 := by
    intro j
    simp [AndersonAC.S45.State.K, AndersonAC.Blueprint.entrywiseSquare, norm_pow]
  have hlinCoeff : ‖(-2 : ℂ) * AndersonAC.S45.gamma t s x ξ‖ ≤ 2 * G := by
    simpa using (mul_le_mul_of_nonneg_left hgamma (by norm_num : 0 ≤ (2 : ℝ)))
  by_cases hix : i = x
  · simp [AndersonAC.S45.Jinc, AndersonAC.S45.pad,
      AndersonAC.S45.survivors, hix]
    positivity
  · have hJformula : ∀ j ∈ AndersonAC.S45.survivors x,
        AndersonAC.S45.Jinc t s x ξ i j =
          (-2 * AndersonAC.S45.gamma t s x ξ) * s.h t i x * s.h t i j * s.h t x j +
          ((AndersonAC.S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) *
            s.K t i x * s.K t x j := by
      intro j hj
      have hjx : j ≠ x := by simpa [AndersonAC.S45.survivors] using hj
      simp [AndersonAC.S45.Jinc, AndersonAC.S45.pad,
        AndersonAC.S45.survivors, hix, hjx]
    have hpoint : ∀ j ∈ AndersonAC.S45.survivors x,
        ‖AndersonAC.S45.Jinc t s x ξ i j‖ ≤
          (2 * G) * M * (‖s.h t i j‖ * ‖s.h t x j‖) +
            (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2 := by
      intro j hj
      have hformula := hJformula j hj
      have hlin : ‖(-2 : ℂ) * AndersonAC.S45.gamma t s x ξ‖ *
          ‖s.h t i x‖ * ‖s.h t i j‖ * ‖s.h t x j‖ ≤
          (2 * G) * M * (‖s.h t i j‖ * ‖s.h t x j‖) := by
        have hmain : ‖(-2 : ℂ) * AndersonAC.S45.gamma t s x ξ‖ *
            ‖s.h t i x‖ ≤ 2 * G * M := by
          calc
            _ ≤ (2 * G) * ‖s.h t i x‖ :=
              mul_le_mul_of_nonneg_right hlinCoeff (norm_nonneg _)
            _ ≤ 2 * G * M := mul_le_mul_of_nonneg_left (hmax i x) (by positivity)
        calc
          _ = (‖(-2 : ℂ) * AndersonAC.S45.gamma t s x ξ‖ * ‖s.h t i x‖) *
              (‖s.h t i j‖ * ‖s.h t x j‖) := by ring
          _ ≤ ((2 * G) * M) * (‖s.h t i j‖ * ‖s.h t x j‖) :=
            mul_le_mul_of_nonneg_right hmain
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = _ := by ring
      have hquad : ‖(AndersonAC.S45.gamma t s x ξ) ^ 2 -
          (1 - s.K t x x)⁻¹‖ * ‖s.K t i x‖ * ‖s.K t x j‖ ≤
          (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2 := by
        have hηKi : ‖(AndersonAC.S45.gamma t s x ξ) ^ 2 -
            (1 - s.K t x x)⁻¹‖ * ‖s.K t i x‖ ≤ (G ^ 2 + I) * M ^ 2 := by
          calc
            _ ≤ (G ^ 2 + I) * ‖s.K t i x‖ :=
              mul_le_mul_of_nonneg_right hη (norm_nonneg _)
            _ ≤ (G ^ 2 + I) * M ^ 2 :=
              mul_le_mul_of_nonneg_left hKi (add_nonneg (sq_nonneg G) hI)
        calc
          _ ≤ ((G ^ 2 + I) * M ^ 2) * ‖s.K t x j‖ :=
            mul_le_mul_of_nonneg_right hηKi (norm_nonneg _)
          _ ≤ (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (hKxj j)
              (mul_nonneg (add_nonneg (sq_nonneg G) hI) (sq_nonneg M))
      calc
        ‖AndersonAC.S45.Jinc t s x ξ i j‖ ≤
            ‖(-2 : ℂ) * AndersonAC.S45.gamma t s x ξ‖ * ‖s.h t i x‖ *
              ‖s.h t i j‖ * ‖s.h t x j‖ +
            ‖(AndersonAC.S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹‖ *
              ‖s.K t i x‖ * ‖s.K t x j‖ := by
          rw [hformula]
          calc
            ‖(-2 * AndersonAC.S45.gamma t s x ξ) * s.h t i x * s.h t i j * s.h t x j +
                ((AndersonAC.S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) *
                  s.K t i x * s.K t x j‖ ≤
              ‖(-2 * AndersonAC.S45.gamma t s x ξ) * s.h t i x * s.h t i j * s.h t x j‖ +
                ‖((AndersonAC.S45.gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) *
                  s.K t i x * s.K t x j‖ := norm_add_le _ _
            _ = _ := by simp [mul_assoc]
        _ ≤ _ := add_le_add hlin hquad
    have hSubRows :
        (∑ j ∈ AndersonAC.S45.survivors x,
          ((2 * G) * M * (‖s.h t i j‖ * ‖s.h t x j‖) +
            (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2)) ≤
        ∑ j, ((2 * G) * M * (‖s.h t i j‖ * ‖s.h t x j‖) +
          (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2) :=
      sum_subset_univ_le (AndersonAC.S45.survivors x) _ (fun j => by positivity)
    calc
      ∑ j ∈ AndersonAC.S45.survivors x, ‖AndersonAC.S45.Jinc t s x ξ i j‖ ≤
          ∑ j ∈ AndersonAC.S45.survivors x,
            ((2 * G) * M * (‖s.h t i j‖ * ‖s.h t x j‖) +
              (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2) :=
        Finset.sum_le_sum fun j hj => hpoint j hj
      _ ≤ ∑ j, ((2 * G) * M * (‖s.h t i j‖ * ‖s.h t x j‖) +
          (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2) := hSubRows
      _ = (∑ j, (2 * G) * M * (‖s.h t i j‖ * ‖s.h t x j‖)) +
          ∑ j, (G ^ 2 + I) * M ^ 2 * ‖s.h t x j‖ ^ 2 := Finset.sum_add_distrib
      _ ≤ 2 * G * M * R + (G ^ 2 + I) * M ^ 2 * R := by
        apply add_le_add
        · calc
            _ = (2 * G * M) * ∑ j, ‖s.h t i j‖ * ‖s.h t x j‖ := by rw [← Finset.mul_sum]
            _ ≤ (2 * G * M) * R :=
              mul_le_mul_of_nonneg_left hCS (mul_nonneg (by positivity) hM)
            _ = 2 * G * M * R := by ring
        · calc
            _ = ((G ^ 2 + I) * M ^ 2) * ∑ j, ‖s.h t x j‖ ^ 2 := by rw [← Finset.mul_sum]
            _ ≤ ((G ^ 2 + I) * M ^ 2) * R :=
              mul_le_mul_of_nonneg_left (hrow x)
                (mul_nonneg (add_nonneg (sq_nonneg G) hI) (sq_nonneg M))
            _ = (G ^ 2 + I) * M ^ 2 * R := by ring

lemma lagJApply_eq_Jinc {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (x : P) (ξ : ℝ)
    (W : P → P → ℂ) (i : P) :
    (AndersonAC.S45.Jinc t s x ξ *ᵥ fun j => W j x) i =
      lagJApply (s.h t)
        (fun _ => -2 * AndersonAC.S45.gamma t s x ξ)
        (fun _ => (AndersonAC.S45.gamma t s x ξ) ^ 2 -
          (1 - s.K t x x)⁻¹) W i x := by
  classical
  change (∑ j, AndersonAC.S45.Jinc t s x ξ i j * W j x) = _
  by_cases hi : i = x
  · simp [lagJApply, lagJLinear, lagJQuadratic, AndersonAC.S45.Jinc,
      AndersonAC.S45.pad, AndersonAC.S45.survivors, AndersonAC.S45.State.K,
      AndersonAC.Blueprint.entrywiseSquare, hi]
  · simp [lagJApply, lagJLinear, lagJQuadratic, AndersonAC.S45.Jinc,
      AndersonAC.S45.pad, AndersonAC.S45.survivors, AndersonAC.S45.State.K,
      AndersonAC.Blueprint.entrywiseSquare, hi]
    have hdist :
        (∑ j, if j = x then 0 else W j x *
          (-2 * (AndersonAC.S45.gamma t s x ξ *
            (s.h t x j * (s.h t i x * s.h t i j))) +
          (AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
            (s.h t x j ^ 2 * s.h t i x ^ 2))) =
        (∑ j, if j = x then 0 else W j x *
          (-2 * (AndersonAC.S45.gamma t s x ξ *
            (s.h t x j * (s.h t i x * s.h t i j))))) +
        (∑ j, if j = x then 0 else W j x *
          ((AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
            (s.h t x j ^ 2 * s.h t i x ^ 2))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjx : j = x <;> simp [hjx, mul_add]
    have hlin :
        (∑ j, if j = x then 0 else W j x *
          (-2 * (AndersonAC.S45.gamma t s x ξ *
            (s.h t x j * (s.h t i x * s.h t i j))))) =
        -2 * (AndersonAC.S45.gamma t s x ξ *
          (s.h t i x * ∑ j, if j = x then 0 else
            W j x * (s.h t x j * s.h t i j))) := by
      calc
        _ = ∑ j, if j = x then 0 else
            (-2 * (AndersonAC.S45.gamma t s x ξ * s.h t i x)) *
              (W j x * (s.h t x j * s.h t i j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hjx : j = x <;> simp [hjx] <;> ring
        _ = (-2 * (AndersonAC.S45.gamma t s x ξ * s.h t i x)) *
            ∑ j, if j = x then 0 else W j x * (s.h t x j * s.h t i j) :=
              sum_ite_mul_left x _ _
        _ = _ := by ring
    have hquad :
        (∑ j, if j = x then 0 else W j x *
          ((AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
            (s.h t x j ^ 2 * s.h t i x ^ 2))) =
        (AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
          (s.h t i x ^ 2 * ∑ j, if j = x then 0 else W j x * s.h t x j ^ 2) := by
      calc
        _ = ∑ j, if j = x then 0 else
            ((AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
              s.h t i x ^ 2) * (W j x * s.h t x j ^ 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hjx : j = x <;> simp [hjx] <;> ring
        _ = ((AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
            s.h t i x ^ 2) * ∑ j, if j = x then 0 else W j x * s.h t x j ^ 2 :=
              sum_ite_mul_left x _ _
        _ = _ := by ring
    have hlinOrder :
        (∑ j, if j = x then 0 else W j x *
          (s.h t x j * s.h t i j)) =
        ∑ j, if j = x then 0 else s.h t i j * s.h t x j * W j x := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjx : j = x <;> simp [hjx] <;> ring
    have hquadOrder :
        (∑ j, if j = x then 0 else W j x * s.h t x j ^ 2) =
        ∑ j, if j = x then 0 else s.h t x j ^ 2 * W j x := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjx : j = x <;> simp [hjx] <;> ring
    calc
      (∑ x_1,
        if x_1 = x then 0 else
          (-(2 * AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t i x_1 * s.h t x x_1) +
            (AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
              s.h t i x ^ 2 * s.h t x x_1 ^ 2) * W x_1 x) =
        ∑ j, if j = x then 0 else W j x *
          (-2 * (AndersonAC.S45.gamma t s x ξ *
            (s.h t x j * (s.h t i x * s.h t i j))) +
          (AndersonAC.S45.gamma t s x ξ ^ 2 - (1 - s.h t x x ^ 2)⁻¹) *
            (s.h t x j ^ 2 * s.h t i x ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjx : j = x
        · simp [hjx]
        · simp [hjx]
          ring
      _ = _ := hdist
      _ = _ := by rw [hlin, hquad, hlinOrder, hquadOrder]; ring

lemma lagJ_inner_linear_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (h : AndersonAC.S45.CMat P) (W : P → P → ℂ) (R : ℝ) (i x : P)
    (hrow : ∀ k, ∑ j, ‖h k j‖ ^ 2 ≤ R) :
    ‖∑ j, (if j = x then 0 else h i j * h x j * W j x)‖ ^ 2 ≤
      R * ∑ j, ‖h i j‖ ^ 2 * ‖W j x‖ ^ 2 := by
  let f : P → ℝ := fun j => ‖h x j‖
  let g : P → ℝ := fun j => ‖h i j‖ * ‖W j x‖
  have hterms : ∀ j, ‖if j = x then (0 : ℂ) else h i j * h x j * W j x‖ ≤
      f j * g j := by
    intro j
    by_cases hj : j = x
    · simp [hj]
      positivity
    · calc
        ‖if j = x then (0 : ℂ) else h i j * h x j * W j x‖ = f j * g j := by
          simp [hj, f, g]
          ring
        _ ≤ _ := le_rfl
  have hsum : ‖∑ j, (if j = x then 0 else h i j * h x j * W j x)‖ ≤
      ∑ j, f j * g j := by
    calc
      _ ≤ ∑ j, ‖if j = x then (0 : ℂ) else h i j * h x j * W j x‖ := norm_sum_le _ _
      _ ≤ ∑ j, f j * g j := Finset.sum_le_sum fun j _ => hterms j
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hf : ∑ j, f j ^ 2 ≤ R := by simpa [f] using hrow x
  have hgsq : ∑ j, g j ^ 2 = ∑ j, ‖h i j‖ ^ 2 * ‖W j x‖ ^ 2 := by
    simp [g, mul_pow]
  have hgnonneg : 0 ≤ ∑ j, g j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcs' : (∑ j, f j * g j) ^ 2 ≤
      R * ∑ j, ‖h i j‖ ^ 2 * ‖W j x‖ ^ 2 := by
    calc
      (∑ j, f j * g j) ^ 2 ≤ (∑ j, f j ^ 2) * ∑ j, g j ^ 2 := hcs
      _ ≤ R * ∑ j, g j ^ 2 := mul_le_mul_of_nonneg_right hf hgnonneg
      _ = R * ∑ j, ‖h i j‖ ^ 2 * ‖W j x‖ ^ 2 := by rw [hgsq]
  have hsumNonneg : 0 ≤ ∑ j, f j * g j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact ((sq_le_sq₀ (norm_nonneg _) hsumNonneg).mpr hsum).trans hcs'

lemma lagJLinear_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (c : P → ℂ)
    (W : P → P → ℂ) (R M D A : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hmax : ∀ i j, ‖h i j‖ ^ 2 ≤ M)
    (hcoef : ∀ x, ‖c x‖ ≤ A)
    (hW : ∀ j, ∑ x ∈ S, ‖W j x‖ ^ 2 ≤ D) :
    ∀ i, ∑ x ∈ S, ‖lagJLinear h c W i x‖ ^ 2 ≤ A ^ 2 * M * R ^ 2 * D := by
  intro i
  let F : P → P → ℝ := fun k j => ‖h k j‖ ^ 2
  have hlinear : ∀ x ∈ S, ‖lagJLinear h c W i x‖ ^ 2 ≤
      A ^ 2 * M * R * ∑ j, F i j * ‖W j x‖ ^ 2 := by
    intro x hx
    by_cases hix : i = x
    · simp [lagJLinear, hix]
      positivity
    · have hinner := lagJ_inner_linear_sq_le h W R i x hrow
      have hc2 : ‖c x‖ ^ 2 ≤ A ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hA).mpr (hcoef x)
      have hix2 : ‖h i x‖ ^ 2 ≤ M := hmax i x
      have hval : ‖c x * h i x *
          (∑ j, if j = x then 0 else h i j * h x j * W j x)‖ ^ 2 ≤
          A ^ 2 * M * (R * ∑ j, ‖h i j‖ ^ 2 * ‖W j x‖ ^ 2) := by
        calc
          _ = ‖c x‖ ^ 2 * ‖h i x‖ ^ 2 *
              ‖∑ j, if j = x then 0 else h i j * h x j * W j x‖ ^ 2 := by
                rw [norm_mul, norm_mul]
                ring
          _ ≤ A ^ 2 * M *
              (R * ∑ j, ‖h i j‖ ^ 2 * ‖W j x‖ ^ 2) := by
                gcongr
      simpa [lagJLinear, hix, F, mul_assoc] using hval
  have hcoefNonneg : 0 ≤ A ^ 2 * M * R := by positivity
  calc
    ∑ x ∈ S, ‖lagJLinear h c W i x‖ ^ 2 ≤
        ∑ x ∈ S, A ^ 2 * M * R * ∑ j, F i j * ‖W j x‖ ^ 2 :=
      Finset.sum_le_sum fun x hx => hlinear x hx
    _ = A ^ 2 * M * R * ∑ j, F i j * ∑ x ∈ S, ‖W j x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
    _ ≤ A ^ 2 * M * R * (R * D) := by
      apply mul_le_mul_of_nonneg_left _ hcoefNonneg
      calc
        ∑ j, F i j * ∑ x ∈ S, ‖W j x‖ ^ 2 ≤ ∑ j, F i j * D := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hW j) (sq_nonneg _)
        _ = (∑ j, F i j) * D := by rw [← Finset.sum_mul]
        _ ≤ R * D := mul_le_mul_of_nonneg_right (hrow i) hD
    _ = A ^ 2 * M * R ^ 2 * D := by ring

lemma lagJQuadratic_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (d : P → ℂ)
    (W : P → P → ℂ) (R H D B : ℝ)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hfour : ∀ i, ∑ j, ‖h i j‖ ^ 4 ≤ H)
    (hcoef : ∀ x, ‖d x‖ ≤ B)
    (hW : ∀ j, ∑ x ∈ S, ‖W j x‖ ^ 2 ≤ D) :
    ∀ i, ∑ x ∈ S, ‖lagJQuadratic h d W i x‖ ^ 2 ≤ B ^ 2 * R ^ 2 * H * D := by
  intro i
  let F : P → P → ℝ := fun k j => ‖h k j‖ ^ 2
  have hWpoint : ∀ j x, x ∈ S → ‖W j x‖ ≤ Real.sqrt D := by
    intro j x hx
    have hs : ‖W j x‖ ^ 2 ≤ D := (Finset.single_le_sum
      (fun y hy => sq_nonneg (‖W j y‖)) hx).trans (hW j)
    have hs' : ‖W j x‖ ^ 2 ≤ (Real.sqrt D) ^ 2 := by
      rw [Real.sq_sqrt hD]
      exact hs
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hs'
  have hinner : ∀ x ∈ S,
      ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ≤ R * Real.sqrt D := by
    intro x hx
    calc
      ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ≤
          ∑ j, ‖if j = x then 0 else h x j ^ 2 * W j x‖ := norm_sum_le _ _
      _ ≤ ∑ j, F x j * Real.sqrt D := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hjx : j = x
        · simp [hjx]
          positivity
        · calc
            ‖if j = x then (0 : ℂ) else h x j ^ 2 * W j x‖ =
                F x j * ‖W j x‖ := by
              simp [hjx, F, pow_two]
            _ ≤ F x j * Real.sqrt D :=
              mul_le_mul_of_nonneg_left (hWpoint j x hx) (sq_nonneg _)
      _ = (∑ j, F x j) * Real.sqrt D := by rw [Finset.sum_mul]
      _ ≤ R * Real.sqrt D :=
        mul_le_mul_of_nonneg_right (hrow x) (Real.sqrt_nonneg _)
  have hpoint : ∀ x ∈ S, ‖lagJQuadratic h d W i x‖ ^ 2 ≤
      B ^ 2 * R ^ 2 * D * ‖h i x‖ ^ 4 := by
    intro x hx
    by_cases hix : i = x
    · simp [lagJQuadratic, hix]
      positivity
    · have hd2 : ‖d x‖ ^ 2 ≤ B ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hcoef x)
      have hinner2 : ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ^ 2 ≤
          R ^ 2 * D := by
        have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (Real.sqrt_nonneg _))).mpr (hinner x hx)
        rw [mul_pow, Real.sq_sqrt hD] at hsq
        exact hsq
      have hval : ‖d x * h i x ^ 2 *
          (∑ j, if j = x then 0 else h x j ^ 2 * W j x)‖ ^ 2 ≤
          B ^ 2 * R ^ 2 * D * ‖h i x‖ ^ 4 := by
        calc
          _ = ‖d x‖ ^ 2 * ‖h i x‖ ^ 4 *
              ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ^ 2 := by
                rw [norm_mul, norm_mul, norm_pow]
                ring
          _ ≤ B ^ 2 * R ^ 2 * D * ‖h i x‖ ^ 4 := by
                calc
                  ‖d x‖ ^ 2 * ‖h i x‖ ^ 4 *
                      ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ^ 2 =
                    ‖d x‖ ^ 2 *
                      (‖h i x‖ ^ 4 *
                        ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ^ 2) := by ring
                  _ ≤ B ^ 2 *
                      (‖h i x‖ ^ 4 *
                        ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ^ 2) :=
                    mul_le_mul_of_nonneg_right hd2
                      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))
                  _ ≤ B ^ 2 * (‖h i x‖ ^ 4 * (R ^ 2 * D)) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hinner2 (pow_nonneg (norm_nonneg _) _))
                      (sq_nonneg _)
                  _ = B ^ 2 * R ^ 2 * D * ‖h i x‖ ^ 4 := by ring
      simpa [lagJQuadratic, hix] using hval
  have hcoefNonneg : 0 ≤ B ^ 2 * R ^ 2 * D := by positivity
  calc
    ∑ x ∈ S, ‖lagJQuadratic h d W i x‖ ^ 2 ≤
        ∑ x ∈ S, B ^ 2 * R ^ 2 * D * ‖h i x‖ ^ 4 :=
      Finset.sum_le_sum fun x hx => hpoint x hx
    _ = B ^ 2 * R ^ 2 * D * ∑ x ∈ S, ‖h i x‖ ^ 4 := by rw [← Finset.mul_sum]
    _ ≤ B ^ 2 * R ^ 2 * D * H := by
      apply mul_le_mul_of_nonneg_left _ hcoefNonneg
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => by positivity)).trans (hfour i)
    _ = B ^ 2 * R ^ 2 * H * D := by ring

lemma lagJApply_array_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (c d : P → ℂ)
    (W : P → P → ℂ) (R H M D A B : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hfour : ∀ i, ∑ j, ‖h i j‖ ^ 4 ≤ H)
    (hmax : ∀ i j, ‖h i j‖ ^ 2 ≤ M)
    (hcoef : ∀ x, ‖c x‖ ≤ A) (hcoef' : ∀ x, ‖d x‖ ≤ B)
    (hW : ∀ j, ∑ x ∈ S, ‖W j x‖ ^ 2 ≤ D) :
    ∀ i, ∑ x ∈ S, ‖lagJApply h c d W i x‖ ^ 2 ≤
      (2 * A ^ 2 * M * R ^ 2 + 2 * B ^ 2 * R ^ 2 * H) * D := by
  intro i
  have hlin := lagJLinear_array_sq_le S h c W R M D A hR hM hD hA hrow hmax hcoef hW i
  have hquad := lagJQuadratic_array_sq_le S h d W R H D B hR hD hB
    hrow hfour hcoef' hW i
  calc
    ∑ x ∈ S, ‖lagJApply h c d W i x‖ ^ 2 ≤
        2 * ∑ x ∈ S, ‖lagJLinear h c W i x‖ ^ 2 +
          2 * ∑ x ∈ S, ‖lagJQuadratic h d W i x‖ ^ 2 := by
      simpa [lagJApply] using
        (sum_norm_add_sq_le S (lagJLinear h c W i) (lagJQuadratic h d W i))
    _ ≤ 2 * (A ^ 2 * M * R ^ 2 * D) + 2 * (B ^ 2 * R ^ 2 * H * D) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlin (by positivity))
        (mul_le_mul_of_nonneg_left hquad (by positivity))
    _ = (2 * A ^ 2 * M * R ^ 2 + 2 * B ^ 2 * R ^ 2 * H) * D := by ring

lemma lagJLinear_array_sum_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (c : P → ℂ)
    (W : P → P → ℂ) (R D A : ℝ)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hcoef : ∀ x, ‖c x‖ ≤ A)
    (hW : ∀ j, ∑ x ∈ S, ‖W j x‖ ^ 2 ≤ D) :
    ∀ i, (∑ x ∈ S, ‖lagJLinear h c W i x‖) ^ 2 ≤ A ^ 2 * R ^ 3 * D := by
  intro i
  let f : P × P → ℝ := fun p => ‖h i p.1‖ * ‖h p.1 p.2‖
  let g : P × P → ℝ := fun p => ‖h i p.2‖ * ‖W p.2 p.1‖
  let T : Finset (P × P) := S ×ˢ Finset.univ
  have hf_nonneg : ∀ p, 0 ≤ f p := fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hg_nonneg : ∀ p, 0 ≤ g p := fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpoint : ∀ x ∈ S, ‖lagJLinear h c W i x‖ ≤
      A * ∑ j, ‖h i x‖ * ‖h x j‖ * ‖h i j‖ * ‖W j x‖ := by
    intro x hx
    by_cases hix : i = x
    · simp [lagJLinear, hix]
      positivity
    · have hinner : ‖∑ j, if j = x then 0 else h i j * h x j * W j x‖ ≤
        ∑ j, ‖h i j‖ * ‖h x j‖ * ‖W j x‖ := by
        calc
          _ ≤ ∑ j, ‖if j = x then (0 : ℂ) else h i j * h x j * W j x‖ := norm_sum_le _ _
          _ ≤ ∑ j, ‖h i j‖ * ‖h x j‖ * ‖W j x‖ := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hjx : j = x
            · simp [hjx]
              positivity
            · simp [hjx, norm_mul, mul_assoc, mul_left_comm, mul_comm]
      calc
        ‖lagJLinear h c W i x‖ =
            ‖c x * h i x * ∑ j, if j = x then 0 else h i j * h x j * W j x‖ := by
              simp [lagJLinear, hix]
        _ ≤ ‖c x‖ * ‖h i x‖ *
            ‖∑ j, if j = x then 0 else h i j * h x j * W j x‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ A * ‖h i x‖ *
            ∑ j, ‖h i j‖ * ‖h x j‖ * ‖W j x‖ := by
              calc
                ‖c x‖ * ‖h i x‖ *
                    ‖∑ j, if j = x then 0 else h i j * h x j * W j x‖ ≤
                  A * ‖h i x‖ *
                    ‖∑ j, if j = x then 0 else h i j * h x j * W j x‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (hcoef x) (norm_nonneg _)) (norm_nonneg _)
                _ ≤ A * ‖h i x‖ *
                    ∑ j, ‖h i j‖ * ‖h x j‖ * ‖W j x‖ :=
                  mul_le_mul_of_nonneg_left hinner (mul_nonneg hA (norm_nonneg _))
        _ = A * ∑ j, ‖h i x‖ * ‖h x j‖ * ‖h i j‖ * ‖W j x‖ := by
              calc
                A * ‖h i x‖ * ∑ j, ‖h i j‖ * ‖h x j‖ * ‖W j x‖ =
                    A * (‖h i x‖ * ∑ j, ‖h i j‖ * ‖h x j‖ * ‖W j x‖) := by ring
                _ = A * ∑ j, ‖h i x‖ * (‖h i j‖ * ‖h x j‖ * ‖W j x‖) := by
                    rw [Finset.mul_sum]
                _ = A * ∑ j, ‖h i x‖ * ‖h x j‖ * ‖h i j‖ * ‖W j x‖ := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
  have hsumPoint : ∑ x ∈ S, ‖lagJLinear h c W i x‖ ≤
      A * ∑ p ∈ T, f p * g p := by
    calc
      ∑ x ∈ S, ‖lagJLinear h c W i x‖ ≤
          ∑ x ∈ S, A * ∑ j, ‖h i x‖ * ‖h x j‖ * ‖h i j‖ * ‖W j x‖ :=
        Finset.sum_le_sum fun x hx => hpoint x hx
      _ = A * ∑ x ∈ S, ∑ j, ‖h i x‖ * ‖h x j‖ * ‖h i j‖ * ‖W j x‖ := by
        rw [← Finset.mul_sum]
      _ = A * ∑ p ∈ T, f p * g p := by
        congr 1
        dsimp [T]
        rw [← Finset.sum_product']
        apply Finset.sum_congr rfl
        intro p hp
        rcases p with ⟨x, j⟩
        simp [f, g]
        ring
  have hsum_f_sq : ∑ p ∈ T, f p ^ 2 ≤ R ^ 2 := by
    dsimp [T]
    rw [Finset.sum_product]
    calc
      ∑ x ∈ S, ∑ j, f (x, j) ^ 2 ≤ ∑ x ∈ S, ‖h i x‖ ^ 2 * R := by
        apply Finset.sum_le_sum
        intro x hx
        calc
          ∑ j, f (x, j) ^ 2 = ‖h i x‖ ^ 2 * ∑ j, ‖h x j‖ ^ 2 := by
            simp [f, mul_pow, Finset.mul_sum]
          _ ≤ ‖h i x‖ ^ 2 * R :=
            mul_le_mul_of_nonneg_left (hrow x) (sq_nonneg _)
      _ = (∑ x ∈ S, ‖h i x‖ ^ 2) * R := by rw [Finset.sum_mul]
      _ ≤ R ^ 2 := by
        have hsub : ∑ x ∈ S, ‖h i x‖ ^ 2 ≤ R :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun _ _ _ => by positivity)).trans (hrow i)
        nlinarith [hR]
  have hsum_g_sq : ∑ p ∈ T, g p ^ 2 ≤ R * D := by
    dsimp [T]
    rw [Finset.sum_product_right]
    calc
      ∑ j, ∑ x ∈ S, g (x, j) ^ 2 ≤ ∑ j, ‖h i j‖ ^ 2 * D := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ∑ x ∈ S, g (x, j) ^ 2 = ‖h i j‖ ^ 2 * ∑ x ∈ S, ‖W j x‖ ^ 2 := by
            simp [g, mul_pow, Finset.mul_sum]
          _ ≤ ‖h i j‖ ^ 2 * D :=
            mul_le_mul_of_nonneg_left (hW j) (sq_nonneg _)
      _ = (∑ j, ‖h i j‖ ^ 2) * D := by rw [Finset.sum_mul]
      _ ≤ R * D := mul_le_mul_of_nonneg_right (hrow i) hD
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T f g
  have hsumfg_nonneg : 0 ≤ ∑ p ∈ T, f p * g p :=
    Finset.sum_nonneg fun p hp => mul_nonneg (hf_nonneg p) (hg_nonneg p)
  have hcs' : (∑ p ∈ T, f p * g p) ^ 2 ≤ R ^ 3 * D := by
    calc
      _ ≤ (∑ p ∈ T, f p ^ 2) * ∑ p ∈ T, g p ^ 2 := hcs
      _ ≤ R ^ 2 * (R * D) :=
        mul_le_mul hsum_f_sq hsum_g_sq (Finset.sum_nonneg fun p hp => sq_nonneg (g p))
          (pow_nonneg hR _)
      _ = R ^ 3 * D := by ring
  have hsumlin_nonneg : 0 ≤ ∑ x ∈ S, ‖lagJLinear h c W i x‖ :=
    Finset.sum_nonneg fun x hx => norm_nonneg _
  have hsumfgSq : (∑ p ∈ T, f p * g p) ^ 2 ≤ R ^ 3 * D := hcs'
  calc
    (∑ x ∈ S, ‖lagJLinear h c W i x‖) ^ 2 ≤
        (A * ∑ p ∈ T, f p * g p) ^ 2 :=
      (sq_le_sq₀ hsumlin_nonneg (mul_nonneg hA hsumfg_nonneg)).mpr hsumPoint
    _ ≤ A ^ 2 * R ^ 3 * D := by
      calc
        (A * ∑ p ∈ T, f p * g p) ^ 2 = A ^ 2 * (∑ p ∈ T, f p * g p) ^ 2 := by ring
        _ ≤ A ^ 2 * (R ^ 3 * D) := mul_le_mul_of_nonneg_left hsumfgSq (sq_nonneg A)
        _ = A ^ 2 * R ^ 3 * D := by ring

lemma lagJQuadratic_array_sum_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (d : P → ℂ)
    (W : P → P → ℂ) (R D B : ℝ)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hcoef : ∀ x, ‖d x‖ ≤ B)
    (hW : ∀ j, ∑ x ∈ S, ‖W j x‖ ^ 2 ≤ D) :
    ∀ i, (∑ x ∈ S, ‖lagJQuadratic h d W i x‖) ^ 2 ≤ B ^ 2 * R ^ 4 * D := by
  intro i
  let F : P → P → ℝ := fun k j => ‖h k j‖ ^ 2
  have hWpoint : ∀ j x, x ∈ S → ‖W j x‖ ≤ Real.sqrt D := by
    intro j x hx
    have hs : ‖W j x‖ ^ 2 ≤ D := (Finset.single_le_sum
      (fun y hy => sq_nonneg (‖W j y‖)) hx).trans (hW j)
    have hs' : ‖W j x‖ ^ 2 ≤ (Real.sqrt D) ^ 2 := by
      rw [Real.sq_sqrt hD]
      exact hs
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hs'
  have hinner : ∀ x ∈ S,
      ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ≤ R * Real.sqrt D := by
    intro x hx
    calc
      ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ≤
          ∑ j, ‖if j = x then 0 else h x j ^ 2 * W j x‖ := norm_sum_le _ _
      _ ≤ ∑ j, F x j * Real.sqrt D := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hjx : j = x
        · simp [hjx]
          positivity
        · calc
            ‖if j = x then (0 : ℂ) else h x j ^ 2 * W j x‖ =
                F x j * ‖W j x‖ := by simp [hjx, F, pow_two]
            _ ≤ F x j * Real.sqrt D :=
              mul_le_mul_of_nonneg_left (hWpoint j x hx) (sq_nonneg _)
      _ = (∑ j, F x j) * Real.sqrt D := by rw [Finset.sum_mul]
      _ ≤ R * Real.sqrt D :=
        mul_le_mul_of_nonneg_right (hrow x) (Real.sqrt_nonneg _)
  have hpoint : ∀ x ∈ S, ‖lagJQuadratic h d W i x‖ ≤
      B * ‖h i x‖ ^ 2 * (R * Real.sqrt D) := by
    intro x hx
    by_cases hix : i = x
    · simp [lagJQuadratic, hix]
      positivity
    · calc
        ‖lagJQuadratic h d W i x‖ =
            ‖d x * h i x ^ 2 * ∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ := by
              simp [lagJQuadratic, hix]
        _ = ‖d x‖ * ‖h i x‖ ^ 2 *
            ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ := by
              rw [norm_mul, norm_mul, norm_pow]
        _ ≤ B * ‖h i x‖ ^ 2 * (R * Real.sqrt D) := by
              calc
                ‖d x‖ * ‖h i x‖ ^ 2 *
                    ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ ≤
                  B * ‖h i x‖ ^ 2 *
                    ‖∑ j, if j = x then 0 else h x j ^ 2 * W j x‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (hcoef x) (sq_nonneg _)) (norm_nonneg _)
                _ ≤ B * ‖h i x‖ ^ 2 * (R * Real.sqrt D) :=
                  mul_le_mul_of_nonneg_left (hinner x hx)
                    (mul_nonneg hB (sq_nonneg _))
  have hfactor : 0 ≤ B * R * Real.sqrt D :=
    mul_nonneg (mul_nonneg hB hR) (Real.sqrt_nonneg _)
  have hsubset : ∑ x ∈ S, ‖h i x‖ ^ 2 ≤ R :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun _ _ _ => by positivity)).trans (hrow i)
  have hsum : ∑ x ∈ S, ‖lagJQuadratic h d W i x‖ ≤
      B * R ^ 2 * Real.sqrt D := by
    calc
      ∑ x ∈ S, ‖lagJQuadratic h d W i x‖ ≤
          ∑ x ∈ S, (B * R * Real.sqrt D) * ‖h i x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        calc
          ‖lagJQuadratic h d W i x‖ ≤ B * ‖h i x‖ ^ 2 * (R * Real.sqrt D) := hpoint x hx
          _ = (B * R * Real.sqrt D) * ‖h i x‖ ^ 2 := by ring
      _ = (B * R * Real.sqrt D) * ∑ x ∈ S, ‖h i x‖ ^ 2 := by
        rw [← Finset.mul_sum]
      _ ≤ (B * R * Real.sqrt D) * R :=
        mul_le_mul_of_nonneg_left hsubset hfactor
      _ = B * R ^ 2 * Real.sqrt D := by ring
  have hsumNonneg : 0 ≤ ∑ x ∈ S, ‖lagJQuadratic h d W i x‖ :=
    Finset.sum_nonneg fun x hx => norm_nonneg _
  have hrightNonneg : 0 ≤ B * R ^ 2 * Real.sqrt D :=
    mul_nonneg (mul_nonneg hB (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hsumSq := (sq_le_sq₀ hsumNonneg hrightNonneg).mpr hsum
  calc
    (∑ x ∈ S, ‖lagJQuadratic h d W i x‖) ^ 2 ≤
        (B * R ^ 2 * Real.sqrt D) ^ 2 := hsumSq
    _ = B ^ 2 * R ^ 4 * D := by
      calc
        (B * R ^ 2 * Real.sqrt D) ^ 2 = B ^ 2 * R ^ 4 * (Real.sqrt D) ^ 2 := by ring
        _ = B ^ 2 * R ^ 4 * D := by rw [Real.sq_sqrt hD]

lemma lagJApply_array_sum_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (h : AndersonAC.S45.CMat P) (c d : P → ℂ)
    (W : P → P → ℂ) (R D A B : ℝ)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖h i j‖ ^ 2 ≤ R)
    (hcoef : ∀ x, ‖c x‖ ≤ A) (hcoef' : ∀ x, ‖d x‖ ≤ B)
    (hW : ∀ j, ∑ x ∈ S, ‖W j x‖ ^ 2 ≤ D) :
    ∀ i, (∑ x ∈ S, ‖lagJApply h c d W i x‖) ^ 2 ≤
      (2 * A ^ 2 * R ^ 3 + 2 * B ^ 2 * R ^ 4) * D := by
  intro i
  have hlin := lagJLinear_array_sum_sq_le S h c W R D A hR hD hA hrow hcoef hW i
  have hquad := lagJQuadratic_array_sum_sq_le S h d W R D B hR hD hB hrow hcoef' hW i
  have hsumtriangle : ∑ x ∈ S, ‖lagJApply h c d W i x‖ ≤
      (∑ x ∈ S, ‖lagJLinear h c W i x‖) +
        (∑ x ∈ S, ‖lagJQuadratic h d W i x‖) := by
    calc
      ∑ x ∈ S, ‖lagJApply h c d W i x‖ ≤
          ∑ x ∈ S, (‖lagJLinear h c W i x‖ + ‖lagJQuadratic h d W i x‖) := by
        apply Finset.sum_le_sum
        intro x hx
        exact norm_add_le _ _
      _ = (∑ x ∈ S, ‖lagJLinear h c W i x‖) +
          (∑ x ∈ S, ‖lagJQuadratic h d W i x‖) := Finset.sum_add_distrib
  have hsumLinNonneg : 0 ≤ ∑ x ∈ S, ‖lagJLinear h c W i x‖ :=
    Finset.sum_nonneg fun x hx => norm_nonneg _
  have hsumQuadNonneg : 0 ≤ ∑ x ∈ S, ‖lagJQuadratic h d W i x‖ :=
    Finset.sum_nonneg fun x hx => norm_nonneg _
  have hsq : (∑ x ∈ S, ‖lagJApply h c d W i x‖) ^ 2 ≤
      2 * (∑ x ∈ S, ‖lagJLinear h c W i x‖) ^ 2 +
        2 * (∑ x ∈ S, ‖lagJQuadratic h d W i x‖) ^ 2 := by
    have hsq' := (sq_le_sq₀ (Finset.sum_nonneg fun x hx => norm_nonneg _)
      (add_nonneg hsumLinNonneg hsumQuadNonneg)).mpr hsumtriangle
    nlinarith [sq_nonneg ((∑ x ∈ S, ‖lagJLinear h c W i x‖) -
      (∑ x ∈ S, ‖lagJQuadratic h d W i x‖))]
  calc
    (∑ x ∈ S, ‖lagJApply h c d W i x‖) ^ 2 ≤
        2 * (∑ x ∈ S, ‖lagJLinear h c W i x‖) ^ 2 +
          2 * (∑ x ∈ S, ‖lagJQuadratic h d W i x‖) ^ 2 := hsq
    _ ≤ 2 * (A ^ 2 * R ^ 3 * D) + 2 * (B ^ 2 * R ^ 4 * D) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlin (by positivity))
        (mul_le_mul_of_nonneg_left hquad (by positivity))
    _ = (2 * A ^ 2 * R ^ 3 + 2 * B ^ 2 * R ^ 4) * D := by ring

lemma lag_state_U_apply {P : Type*} [Fintype P] [DecidableEq P]
    (s : AndersonAC.S45.State P) (t : ℝ) :
    s.U t = (Real.sqrt t : ℂ) • s.lag t := by
  ext i
  have h := congrFun (show s.U t = (Real.sqrt t : ℂ) • s.lag t from by
    ext j
    simp [AndersonAC.S45.State.U, AndersonAC.S45.State.z,
      AndersonAC.S45.State.lag, AndersonAC.S45.State.P, Matrix.mulVec_smul]) i
  simpa [Pi.smul_apply, smul_eq_mul] using h

def lagRawForcingScaled {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (z : P → ℝ) (i x : P) : ℂ :=
  lagDirectScaled t s z i x +
    (AndersonAC.S45.Jinc t s x (z x) *ᵥ fun j => s.lag t j) i

lemma lagRawForcingScaled_eq {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (z : P → ℝ) (i x : P) :
    lagRawForcingScaled t s z i x = lagForcingScaled t s z i x := by
  unfold lagRawForcingScaled lagForcingScaled
  congr 1
  exact lagJApply_eq_Jinc t s x (z x) (fun j _ => s.lag t j) i

lemma matrix_family_array_sq_le {P : Type*} [Fintype P]
    (S : Finset P) (A : P → AndersonAC.S45.CMat P)
    (A0 : AndersonAC.S45.CMat P) (Y : P → P → ℂ) (L B : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hA : ∀ x i j, ‖A x i j‖ ≤ ‖A0 i j‖)
    (hA0 : ∀ i, ∑ j, ‖A0 i j‖ ≤ L)
    (hY : ∀ j, ∑ x ∈ S, ‖Y j x‖ ^ 2 ≤ B) :
    ∀ i, ∑ x ∈ S, ‖(A x *ᵥ fun j => Y j x) i‖ ^ 2 ≤ L ^ 2 * B := by
  intro i
  let a : P → P → ℝ := fun x j => ‖A x i j‖
  let b : P → ℝ := fun j => ‖A0 i j‖
  have hab : ∀ x j, 0 ≤ a x j := fun _ _ => norm_nonneg _
  have hrow : ∀ x, ∑ j, a x j ≤ L := by
    intro x
    calc
      ∑ j, a x j ≤ ∑ j, b j := Finset.sum_le_sum fun j _ => hA x i j
      _ ≤ L := by simpa [b] using hA0 i
  have hpoint : ∀ x, ‖(A x *ᵥ fun j => Y j x) i‖ ^ 2 ≤
      L * ∑ j, b j * ‖Y j x‖ ^ 2 := by
    intro x
    have hsum : ‖(A x *ᵥ fun j => Y j x) i‖ ≤
        ∑ j, a x j * ‖Y j x‖ := by
      change ‖∑ j, A x i j * Y j x‖ ≤ _
      calc
        ‖∑ j, A x i j * Y j x‖ ≤ ∑ j, ‖A x i j * Y j x‖ := norm_sum_le _ _
        _ = ∑ j, a x j * ‖Y j x‖ := by simp [a]
    have hcs := weighted_sum_sq_le Finset.univ (a x) (fun j => ‖Y j x‖)
      (fun j _ => hab x j)
    have hweighted : 0 ≤ ∑ j, a x j * ‖Y j x‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hab x j) (sq_nonneg _)
    have hcs' : (∑ j, a x j * ‖Y j x‖) ^ 2 ≤
        L * ∑ j, a x j * ‖Y j x‖ ^ 2 := by
      calc
        _ ≤ (∑ j, a x j) * ∑ j, a x j * ‖Y j x‖ ^ 2 := hcs
        _ ≤ L * ∑ j, a x j * ‖Y j x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow x) hweighted
    have hnormnonneg : 0 ≤ ∑ j, a x j * ‖Y j x‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hab x j) (norm_nonneg _)
    have hnormsq := (sq_le_sq₀ (norm_nonneg _) hnormnonneg).mpr hsum
    have hfirst : ‖(A x *ᵥ fun j => Y j x) i‖ ^ 2 ≤
        L * ∑ j, a x j * ‖Y j x‖ ^ 2 := hnormsq.trans hcs'
    calc
      _ ≤ L * ∑ j, a x j * ‖Y j x‖ ^ 2 := hfirst
      _ ≤ L * ∑ j, b j * ‖Y j x‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hL
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hA x i j) (sq_nonneg _)
  calc
    ∑ x ∈ S, ‖(A x *ᵥ fun j => Y j x) i‖ ^ 2 ≤
        ∑ x ∈ S, L * ∑ j, b j * ‖Y j x‖ ^ 2 :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = L * ∑ x ∈ S, ∑ j, b j * ‖Y j x‖ ^ 2 := by
      rw [← Finset.mul_sum]
    _ = L * ∑ j, ∑ x ∈ S, b j * ‖Y j x‖ ^ 2 := by
      congr 1
      rw [Finset.sum_comm]
    _ = L * ∑ j, b j * ∑ x ∈ S, ‖Y j x‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
    _ ≤ L * (L * B) := by
      apply mul_le_mul_of_nonneg_left _ hL
      calc
        ∑ j, b j * ∑ x ∈ S, ‖Y j x‖ ^ 2 ≤ ∑ j, b j * B :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hY j) (norm_nonneg _)
        _ = (∑ j, b j) * B := by rw [← Finset.sum_mul]
        _ ≤ L * B := mul_le_mul_of_nonneg_right (by simpa [b] using hA0 i) hB
    _ = L ^ 2 * B := by ring

lemma lag_recurrence_array_absorb {P : Type*} [Fintype P]
    (S : Finset P) (M : P → AndersonAC.S45.CMat P) (M0 : AndersonAC.S45.CMat P)
    (J : P → AndersonAC.S45.CMat P) (F Y : P → P → ℂ)
    (L η E : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hE : 0 ≤ E)
    (hsmall : 2 * L ^ 2 * η ≤ 1 / 2)
    (hrec : ∀ i x, x ∈ S → Y i x =
      (M x *ᵥ (fun j => F j x + (J x *ᵥ fun k => Y k x) j)) i)
    (hM : ∀ x i j, ‖M x i j‖ ≤ ‖M0 i j‖)
    (hM0 : ∀ i, ∑ j, ‖M0 i j‖ ≤ L)
    (hF : ∀ i, ∑ x ∈ S, ‖F i x‖ ^ 2 ≤ E)
    (hJ : ∀ i, ∑ x ∈ S, ‖(J x *ᵥ fun k => Y k x) i‖ ^ 2 ≤
      η * AndersonAC.S45.arrayA2sq S Y) :
    AndersonAC.S45.arrayA2sq S Y ≤ 4 * L ^ 2 * E := by
  let V : P → P → ℂ := fun j x => F j x + (J x *ᵥ fun k => Y k x) j
  let D := AndersonAC.S45.arrayA2sq S Y
  have hD : 0 ≤ D := norm_nonneg _
  have hV : ∀ i, ∑ x ∈ S, ‖V i x‖ ^ 2 ≤ 2 * E + 2 * η * D := by
    intro i
    have h := sum_norm_add_sq_le S (fun x => F i x)
      (fun x => (J x *ᵥ fun k => Y k x) i)
    calc
      ∑ x ∈ S, ‖V i x‖ ^ 2 ≤
          2 * ∑ x ∈ S, ‖F i x‖ ^ 2 +
            2 * ∑ x ∈ S, ‖(J x *ᵥ fun k => Y k x) i‖ ^ 2 := by
              simpa [V] using h
      _ ≤ 2 * E + 2 * η * D := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hF i) (by positivity))
          (by simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left (hJ i) (by norm_num : 0 ≤ (2 : ℝ))))
  have hVnonneg : 0 ≤ 2 * E + 2 * η * D := by positivity
  have hrows : ∀ i, ∑ x ∈ S, ‖Y i x‖ ^ 2 ≤ L ^ 2 * (2 * E + 2 * η * D) := by
    intro i
    calc
      ∑ x ∈ S, ‖Y i x‖ ^ 2 =
          ∑ x ∈ S, ‖(M x *ᵥ fun j => V j x) i‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hrec i x hx]
      _ ≤ L ^ 2 * (2 * E + 2 * η * D) :=
          matrix_family_array_sq_le S M M0 V L (2 * E + 2 * η * D)
            hL hVnonneg hM hM0 hV i
  have hbound : D ≤ L ^ 2 * (2 * E + 2 * η * D) :=
    (arrayA2sq_le_of_rows S Y _ (by positivity) hrows)
  have hmul : 2 * L ^ 2 * η * D ≤ D / 2 := by
    have := mul_le_mul_of_nonneg_right hsmall hD
    nlinarith
  have hbound' : D ≤ 2 * L ^ 2 * E + D / 2 := by
    nlinarith [hbound, hmul]
  nlinarith

lemma lag_exact_recurrence {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (x : P) (z : P → ℝ)
    (ht : 0 < t) (hsym : s.g.IsSymm) (hA : IsUnit (1 - s.K t))
    (ha : 1 - s.K t x x ≠ 0)
    (hden : 1 + ((z x : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hnew : IsUnit (1 - (AndersonAC.S45.deleteState t s x (z x)).K t)) :
    ∀ i (hi : i ∈ AndersonAC.S45.survivors x),
    AndersonAC.S45.lagInc t s x (z x) i =
        (AndersonAC.S45.restrict (1 - s.K t)⁻¹ (AndersonAC.S45.survivors x) *ᵥ
          ((fun j => lagRawForcingScaled t s z j.val x) +
            AndersonAC.S45.restrict (AndersonAC.S45.Jinc t s x (z x))
              (AndersonAC.S45.survivors x) *ᵥ
              (fun k => AndersonAC.S45.lagInc t s x (z x) k.val))) ⟨i, hi⟩ := by
  classical
  let S := AndersonAC.S45.survivors x
  let oldA : AndersonAC.S45.CMat P := 1 - s.K t
  let B : Matrix S S ℂ := AndersonAC.S45.scalarSchur oldA x
  let J : Matrix S S ℂ := AndersonAC.S45.restrict
    (AndersonAC.S45.Jinc t s x (z x)) S
  let M : Matrix S S ℂ := AndersonAC.S45.restrict oldA⁻¹ S
  let Anew : Matrix S S ℂ := 1 - (AndersonAC.S45.deleteState t s x (z x)).K t
  let root : ℂ := Real.sqrt t
  let inc : S → ℂ := fun j => AndersonAC.S45.lagInc t s x (z x) j.val
  let scaledForce : S → ℂ := fun j => lagRawForcingScaled t s z j.val x
  let force : S → ℂ := fun j => AndersonAC.S45.forcing t s x (z x) j.val
  let u : S → ℂ := fun j => root * inc j
  have hroot : root ≠ 0 := by
    dsimp [root]
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hnewdet : IsUnit Anew.det := by
    apply (Matrix.isUnit_iff_isUnit_det Anew).mp
    simpa [Anew] using hnew
  have hexact (j : S) : u j = (Anew⁻¹ *ᵥ force) j := by
    have h := AndersonAC.AgentS45.lag_exact_proof t s x (z x) ht hsym hA ha hden hnew j.val j.property
    simpa [u, inc, force, Anew, root, AndersonAC.S45.State.P] using h
  have hu : u = Anew⁻¹ *ᵥ force := funext hexact
  have hsys : Anew *ᵥ u = force := by
    calc
      Anew *ᵥ u = Anew *ᵥ (Anew⁻¹ *ᵥ force) := by rw [hu]
      _ = (Anew * Anew⁻¹) *ᵥ force := by rw [← Matrix.mulVec_mulVec]
      _ = force := by rw [Matrix.mul_nonsing_inv Anew hnewdet]; simp
  have hupdate : Anew = B - J := by
    dsimp [Anew, B, J, oldA, S]
    exact lag_delete_A_update t s x (z x) ht ha hden
  have haA : oldA x x ≠ 0 := by
    simpa [oldA, Matrix.one_apply] using ha
  have hMB := lag_restrict_scalarSchur_left_inv oldA x hA haA
  have hMBu : M *ᵥ (B *ᵥ u) = u := by
    funext j
    simpa [M, B, oldA, S] using hMB u j
  have hsys' : (B - J) *ᵥ u = force := by rw [← hupdate]; exact hsys
  have hsysM : M *ᵥ (B *ᵥ u) - M *ᵥ (J *ᵥ u) = M *ᵥ force := by
    calc
      M *ᵥ (B *ᵥ u) - M *ᵥ (J *ᵥ u) = M *ᵥ (B *ᵥ u - J *ᵥ u) := by
        rw [Matrix.mulVec_sub]
      _ = M *ᵥ ((B - J) *ᵥ u) := by rw [Matrix.sub_mulVec]
      _ = M *ᵥ force := by rw [← hsys']
  have hforce (j : S) : force j = root * scaledForce j := by
    have hjx : j.val ≠ x := by simpa [S, AndersonAC.S45.survivors] using j.property
    have hU := lag_state_U_apply s t
    have hJscale :
        (AndersonAC.S45.Jinc t s x (z x) *ᵥ s.U t) j.val =
          Real.sqrt t * (AndersonAC.S45.Jinc t s x (z x) *ᵥ
            (fun k => s.lag t k)) j.val := by
      calc
        _ = (AndersonAC.S45.Jinc t s x (z x) *ᵥ
            ((Real.sqrt t : ℂ) • s.lag t)) j.val := by rw [hU]
        _ = ((Real.sqrt t : ℂ) •
            (AndersonAC.S45.Jinc t s x (z x) *ᵥ s.lag t)) j.val := by
              rw [Matrix.mulVec_smul]
        _ = _ := rfl
    have hdirect :
        -(AndersonAC.S45.gamma t s x (z x) + s.z t x /
          (1 - s.K t x x)) * s.K t j.val x =
        (Real.sqrt t : ℂ) *
          (-((AndersonAC.S45.gamma t s x (z x) +
              s.z t x * (1 - s.K t x x)⁻¹) / (Real.sqrt t : ℂ)) *
            s.K t j.val x) := by
      rw [div_eq_mul_inv]
      field_simp [hroot, ha]
    change AndersonAC.S45.forcing t s x (z x) j.val =
      (Real.sqrt t : ℂ) * lagRawForcingScaled t s z j.val x
    rw [AndersonAC.S45.forcing]
    simp only [hjx, if_false]
    rw [lagRawForcingScaled, hJscale, hdirect]
    rw [lagDirectScaled]
    simp only [hjx, if_false]
    field_simp [hroot, ha]
  have hscaled : force = root • scaledForce := by
    funext j
    simpa [Pi.smul_apply, smul_eq_mul] using hforce j
  have hsysM' : u - M *ᵥ (J *ᵥ u) = M *ᵥ force := by
    simpa only [hMBu] using hsysM
  have hJu : J *ᵥ u = root • (J *ᵥ inc) := by
    have hu' : u = root • inc := by
      funext j
      simp [u, Pi.smul_apply, smul_eq_mul]
    rw [hu', Matrix.mulVec_smul]
  have hMf : M *ᵥ force = root • (M *ᵥ scaledForce) := by
    rw [hscaled, Matrix.mulVec_smul]
  intro i hi
  have hcoord := congrFun hsysM' ⟨i, hi⟩
  have hrootEq : root * inc ⟨i, hi⟩ - root * (M *ᵥ (J *ᵥ inc)) ⟨i, hi⟩ =
      root * (M *ᵥ scaledForce) ⟨i, hi⟩ := by
    rw [hJu, Matrix.mulVec_smul, hMf] at hcoord
    simpa [u, inc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hcoord
  have hcancel : inc ⟨i, hi⟩ - (M *ᵥ (J *ᵥ inc)) ⟨i, hi⟩ =
      (M *ᵥ scaledForce) ⟨i, hi⟩ := by
    have h := congrArg (fun a : ℂ => root⁻¹ * a) hrootEq
    simpa [mul_sub, mul_assoc, hroot] using h
  have hfinal : inc ⟨i, hi⟩ = (M *ᵥ (scaledForce + J *ᵥ inc)) ⟨i, hi⟩ := by
    calc
      inc ⟨i, hi⟩ = (M *ᵥ scaledForce) ⟨i, hi⟩ +
          (M *ᵥ (J *ᵥ inc)) ⟨i, hi⟩ := eq_add_of_sub_eq hcancel
      _ = (M *ᵥ (scaledForce + J *ᵥ inc)) ⟨i, hi⟩ := by
        rw [Matrix.mulVec_add]
        simp only [Pi.add_apply]
  simpa [inc, scaledForce, M, J, S, lagRawForcingScaled] using hfinal

lemma lag_pad_mulVec_apply {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (B : Matrix S S ℂ) (u : P → ℂ) (i : S) :
    (AndersonAC.S45.pad S B *ᵥ u) i.val = (B *ᵥ (fun j : S => u j.val)) i := by
  classical
  let f : P → ℂ := fun x => if hx : x ∈ S then B i ⟨x, hx⟩ * u x else 0
  have hsubset : (∑ x ∈ S, f x) = ∑ x : P, f x := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro x hx hxnot
    simp [f, hxnot]
  have hattach : (∑ x ∈ S, f x) = ∑ x ∈ S.attach, f x :=
    (Finset.sum_attach (s := S) (f := f)).symm
  calc
    (AndersonAC.S45.pad S B *ᵥ u) i.val = ∑ x : P, f x := by
      simp [Matrix.mulVec, dotProduct, AndersonAC.S45.pad, f, i.property]
    _ = ∑ x ∈ S, f x := hsubset.symm
    _ = ∑ x ∈ S.attach, f x := hattach
    _ = (B *ᵥ (fun j : S => u j.val)) i := by simp [Matrix.mulVec, dotProduct, f]

lemma lag_exact_recurrence_full {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (t : ℝ) (s : AndersonAC.S45.State P) (z : P → ℝ)
    (ht : 0 < t) (hsym : s.g.IsSymm) (hA : IsUnit (1 - s.K t))
    (hlocal : ∀ x ∈ S,
      (1 - s.K t x x ≠ 0) ∧
      (1 + ((z x : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧
      IsUnit (1 - (AndersonAC.S45.deleteState t s x (z x)).K t)) :
    ∀ x ∈ S, ∀ i,
      AndersonAC.S45.lagInc t s x (z x) i =
        Matrix.mulVec
          (AndersonAC.S45.pad (AndersonAC.S45.survivors x)
            (AndersonAC.S45.restrict (1 - s.K t)⁻¹
              (AndersonAC.S45.survivors x)))
          (fun j => lagRawForcingScaled t s z j x +
            Matrix.mulVec (AndersonAC.S45.Jinc t s x (z x))
              (fun k => AndersonAC.S45.lagInc t s x (z x) k) j) i := by
  classical
  intro x hxS i
  let T := AndersonAC.S45.survivors x
  let Mr := AndersonAC.S45.restrict (1 - s.K t)⁻¹ T
  let Jr := AndersonAC.S45.restrict (AndersonAC.S45.Jinc t s x (z x)) T
  let inc : T → ℂ := fun j => AndersonAC.S45.lagInc t s x (z x) j.val
  let fullY : P → ℂ := fun j => AndersonAC.S45.lagInc t s x (z x) j
  let fullInput : P → ℂ := fun j => lagRawForcingScaled t s z j x +
    (AndersonAC.S45.Jinc t s x (z x) *ᵥ fullY) j
  have hYsupport : ∀ j : P,
      (fun k => if hk : k ∈ T then inc ⟨k, hk⟩ else 0) j = fullY j := by
    intro j
    by_cases hj : j ∈ T
    · simp [fullY, inc, hj]
    · have hj' : j ∉ AndersonAC.S45.survivors x := by simpa [T] using hj
      have hzero : fullY j = 0 := by
        change AndersonAC.S45.lagInc t s x (z x) j = 0
        simp [AndersonAC.S45.lagInc, hj']
      simp [hj, hzero]
  have hYsupportFun :
      (fun k => if hk : k ∈ T then inc ⟨k, hk⟩ else 0) = fullY := funext hYsupport
  have hJrestrict : ∀ j : T,
      (Jr *ᵥ inc) j =
        (AndersonAC.S45.Jinc t s x (z x) *ᵥ fullY) j.val := by
    intro j
    rw [lag_restrict_mulVec_apply T (AndersonAC.S45.Jinc t s x (z x)) inc j]
    rw [hYsupportFun]
  have hrec := lag_exact_recurrence t s x z ht hsym hA
    (hlocal x hxS).1 (hlocal x hxS).2.1 (hlocal x hxS).2.2
  by_cases hi : i ∈ T
  · let u : T → ℂ := fun j => lagRawForcingScaled t s z j.val x + (Jr *ᵥ inc) j
    have hinput : u = fun j : T => fullInput j.val := by
      funext j
      simp [u, fullInput, lagRawForcingScaled, hJrestrict j]
    have h := hrec i hi
    change AndersonAC.S45.lagInc t s x (z x) i =
      (Mr *ᵥ (fun j : T => lagRawForcingScaled t s z j.val x + (Jr *ᵥ inc) j)) ⟨i, hi⟩ at h
    calc
      AndersonAC.S45.lagInc t s x (z x) i = (Mr *ᵥ u) ⟨i, hi⟩ := by
        simpa [u] using h
      _ = (AndersonAC.S45.pad T Mr *ᵥ fullInput) i := by
        calc
          _ = (Mr *ᵥ (fun j : T => fullInput j.val)) ⟨i, hi⟩ := by rw [hinput]
          _ = (AndersonAC.S45.pad T Mr *ᵥ fullInput) i :=
            (lag_pad_mulVec_apply T Mr fullInput ⟨i, hi⟩).symm
  · have hzero : AndersonAC.S45.lagInc t s x (z x) i = 0 := by
      have hi' : i ∉ AndersonAC.S45.survivors x := by simpa [T] using hi
      change (if h : i ∈ AndersonAC.S45.survivors x then _ else 0) = 0
      simp [hi']
    have hpad :
        (AndersonAC.S45.pad T Mr *ᵥ fullInput) i = 0 := by
      rw [Matrix.mulVec_apply_eq_sum]
      simp [AndersonAC.S45.pad, hi]
    rw [hzero, hpad]

lemma lag_prestate_basic_bounds {P : Type*} [Fintype P] [DecidableEq P]
    (C t : ℝ) (s : AndersonAC.S45.State P)
    (Λplus Wstar : AndersonAC.S45.Form P)
    (hC : 1 ≤ C) (ht : 0 < t)
    (hpre : AndersonAC.S45.Prestate t C Λplus Wstar s)
    (hsmall : C * AndersonAC.S45.power t AndersonAC.S45.beta ≤ 1 / 2) :
    ∀ i, ‖s.rawLag i‖ ≤
        2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2) ∧
      |s.q i - s.p i| ≤ 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2) ∧
      (∑ j, ‖s.h t i j‖ ^ 2) ≤
        C * (C + 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2)) ∧
      ‖s.h t i i‖ ≤ Real.sqrt t *
        (C + 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2)) := by
  intro i
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hcp : 0 < 1 / C := by positivity
  have hsmall' : AndersonAC.S45.power t AndersonAC.S45.beta / (1 / C) ≤ 1 / 2 := by
    calc
      AndersonAC.S45.power t AndersonAC.S45.beta / (1 / C) =
          C * AndersonAC.S45.power t AndersonAC.S45.beta := by
            field_simp [ne_of_gt hCpos]
      _ ≤ 1 / 2 := hsmall
  have hraw := AgentS45.diag_from_lag s t (AndersonAC.S45.power t AndersonAC.S45.beta)
    (1 / C) C hpre.ward hpre.invertible hpre.lag_cap hcp
    (fun j => (hpre.broad j).2.1) (fun j => (hpre.broad j).1)
    (Real.rpow_nonneg ht.le _) hsmall' i
  have hraw' : ‖s.rawLag i‖ ≤
      2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2) := by
    simpa [pow_two] using hraw
  have hqd : s.q i - s.p i = (s.rawLag i).im := by
    simp [AndersonAC.S45.State.q, AndersonAC.S45.State.p,
      AndersonAC.S45.State.rawLag]
  have hqpRaw : |s.q i - s.p i| ≤ ‖s.rawLag i‖ := by
    rw [hqd]
    exact Complex.abs_im_le_norm _
  have hqp : |s.q i - s.p i| ≤
      2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2) := by
    exact hqpRaw.trans hraw'
  have hqle : s.q i ≤ C + ‖s.rawLag i‖ := by
    have := abs_le.mp hqpRaw
    linarith [(hpre.broad i).2.2]
  have hrowraw : (∑ j, ‖s.h t i j‖ ^ 2) ≤
      (C + ‖s.rawLag i‖) / (1 / C) := by
    apply (le_div_iff₀ hcp).2
    calc
      (∑ j, ‖s.h t i j‖ ^ 2) * (1 / C) =
          ∑ j, (1 / C) * ‖s.h t i j‖ ^ 2 := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j, s.p j * ‖s.h t i j‖ ^ 2 :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (hpre.broad j).2.1 (sq_nonneg _)
      _ = s.q i := by simpa [AndersonAC.S45.State.q] using
          AgentS45.ward_row hpre.ward i
      _ ≤ C + ‖s.rawLag i‖ := hqle
  have hrow : (∑ j, ‖s.h t i j‖ ^ 2) ≤
      C * (C + 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2)) := by
    have hratio : (C + ‖s.rawLag i‖) / (1 / C) ≤
        C * (C + 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2)) := by
      calc
        (C + ‖s.rawLag i‖) / (1 / C) = C * (C + ‖s.rawLag i‖) := by
          field_simp [ne_of_gt hCpos]
        _ ≤ C * (C + 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith [hraw']) hCpos.le
    exact hrowraw.trans hratio
  have hgi : ‖s.g i i‖ ≤ C + ‖s.rawLag i‖ := by
    have heq : s.g i i = s.r i + s.rawLag i := by
      simp [AndersonAC.S45.State.rawLag]
    rw [heq]
    calc
      ‖s.r i + s.rawLag i‖ ≤ ‖s.r i‖ + ‖s.rawLag i‖ := norm_add_le _ _
      _ ≤ C + ‖s.rawLag i‖ := by linarith [(hpre.broad i).1]
  have hdiag : ‖s.h t i i‖ ≤ Real.sqrt t *
      (C + 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2)) := by
    calc
      ‖s.h t i i‖ = Real.sqrt t * ‖s.g i i‖ := by
        simp [AndersonAC.S45.State.h, Pi.smul_apply, smul_eq_mul,
          norm_mul, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt t * (C + ‖s.rawLag i‖) :=
        mul_le_mul_of_nonneg_left hgi (Real.sqrt_nonneg _)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        linarith
  exact ⟨hraw', hqp, hrow, hdiag⟩

lemma lag_gamma_bounds_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (C t : ℝ) (s : AndersonAC.S45.State P) (Λplus Wstar : AndersonAC.S45.Form P)
    (S : Finset P) (z : P → ℝ) (hC : 1 ≤ C) (ht : 0 < t) (htle : t ≤ 1)
    (hpre : AndersonAC.S45.Prestate t C Λplus Wstar s)
    (hsmall : C * AndersonAC.S45.power t AndersonAC.S45.beta ≤ 1 / 2)
    (hepssmall : Real.sqrt t < (4 * (2 * C + 2 * (1 + C ^ 2)) ^ 2)⁻¹)
    (hz : ∀ x ∈ S, |z x| ≤ C * Real.sqrt t) :
    ∀ x ∈ S,
      (1 + ((z x : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧
      ‖AndersonAC.S45.gamma t s x (z x)‖ ≤ 4 * (2 * C + 2 * (1 + C ^ 2)) := by
  intro x hx
  have hb := lag_prestate_basic_bounds C t s Λplus Wstar hC ht hpre hsmall x
  have hβnonneg : 0 ≤ AndersonAC.S45.beta := by norm_num [AndersonAC.S45.beta,
    AndersonAC.S45.delta]
  have hpw : AndersonAC.S45.power t AndersonAC.S45.beta ≤ 1 := by
    exact Real.rpow_le_one ht.le htle hβnonneg
  have hrawsmall : ‖s.rawLag x‖ ≤ 2 * (1 + C ^ 2) := by
    calc
      ‖s.rawLag x‖ ≤ 2 * AndersonAC.S45.power t AndersonAC.S45.beta * (1 + C ^ 2) := hb.1
      _ ≤ 2 * (1 + C ^ 2) := by nlinarith [hpw, sq_nonneg C]
  have hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ 2 * C + 2 * (1 + C ^ 2) := by
    have hgeq : s.g x x = s.r x + s.rawLag x := by
      simp [AndersonAC.S45.State.rawLag]
    have hg : ‖s.g x x‖ ≤ C + ‖s.rawLag x‖ := by
      rw [hgeq]
      calc
        ‖s.r x + s.rawLag x‖ ≤ ‖s.r x‖ + ‖s.rawLag x‖ := norm_add_le _ _
        _ ≤ C + ‖s.rawLag x‖ := by linarith [(hpre.broad x).1]
    have hr := (hpre.broad x).1
    linarith
  have hCstate : 1 ≤ 2 * C + 2 * (1 + C ^ 2) := by nlinarith [hC]
  let eps : ℝ := Real.sqrt t
  let eta : ℝ := z x / Real.sqrt t
  have hepspos : 0 < eps := by simp [eps, ht]
  have hepsle : eps ≤ 1 := by simpa [eps] using (Real.sqrt_le_one.mpr htle)
  have hepssq : eps ^ 2 = t := by simp [eps, Real.sq_sqrt ht.le]
  have heta : eps * eta = z x := by
    dsimp [eps, eta]
    field_simp [ne_of_gt (Real.sqrt_pos.2 ht)]
  have hetaBound : |eta| ≤ C := by
    dsimp [eta]
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 ht)]
    exact (div_le_iff₀ (Real.sqrt_pos.2 ht)).2 (hz x hx)
  have hetaBound' : |eta| ≤ 2 * C + 2 * (1 + C ^ 2) := by
    exact hetaBound.trans (by nlinarith [hC, sq_nonneg C])
  have hg := AgentS45.gamma_pointwise_bounds
    (2 * C + 2 * (1 + C ^ 2)) t eps eta (z x) s x hCstate ht
    hepspos hepsle hepssmall hepssq heta hetaBound' hstate
  exact ⟨hg.1, hg.2.1⟩

lemma lag_restrict_row_sum_le {P : Type*} [Fintype P] [DecidableEq P]
    (A : AndersonAC.S45.CMat P) (S : Finset P) (i : S) :
    (∑ j : S, ‖AndersonAC.S45.restrict A S i j‖) ≤
      AndersonAC.S45.rowNorm A := by
  have hattach :
      (∑ j : S, ‖A i.val j.val‖) = ∑ j ∈ S, ‖A i.val j‖ := by
    simpa using (Finset.sum_attach (s := S) (f := fun j => ‖A i.val j‖))
  calc
    (∑ j : S, ‖AndersonAC.S45.restrict A S i j‖) =
        ∑ j : S, ‖A i.val j.val‖ := by rfl
    _ = ∑ j ∈ S, ‖A i.val j‖ := hattach
    _ ≤ ∑ j, ‖A i.val j‖ :=
      sum_subset_univ_le S (fun j => ‖A i.val j‖) (fun _ => norm_nonneg _)
    _ ≤ AndersonAC.S45.rowNorm A := rowSum_le_rowNorm A i.val

lemma lag_poststate_caps_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (C t : ℝ) (s : AndersonAC.S45.State P) (Λplus Wstar : AndersonAC.S45.Form P)
    (S : Finset P) (z : P → ℝ) (R M G L : ℝ)
    (hC : 1 ≤ C) (ht : 0 < t) (hpre : AndersonAC.S45.Prestate t C Λplus Wstar s)
    (hrow : ∀ i, ∑ j, ‖s.h t i j‖ ^ 2 ≤ R) (hR : 0 ≤ R)
    (hmax : ∀ i j, ‖s.h t i j‖ ≤ M) (hM : 0 ≤ M)
    (hgamma : ∀ x ∈ S, ‖AndersonAC.S45.gamma t s x (z x)‖ ≤ G)
    (hden : ∀ x ∈ S, 1 + ((z x : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hG : 0 ≤ G) (hProw : AndersonAC.S45.rowNorm (s.P t) ≤ L) (hL : 0 ≤ L)
    (hsmall : L * (2 * G * M * R + (G ^ 2 + 2) * M ^ 2 * R) < 1) :
    ∀ x ∈ S,
      (1 - s.K t x x ≠ 0) ∧
      (‖(1 - s.K t x x)⁻¹‖ ≤ 2) ∧
      IsUnit (1 - (AndersonAC.S45.deleteState t s x (z x)).K t) := by
  intro x hxS
  have hKxx : ‖s.K t x x‖ ≤ 1 / 2 := by
    exact (lag_matrix_entry_norm_le (s.K t) x x).trans hpre.K_cap
  have ha : 1 - s.K t x x ≠ 0 := by
    intro heq
    have hKone : s.K t x x = 1 := by
      calc
        s.K t x x = 1 - (1 - s.K t x x) := by ring
        _ = 1 := by rw [heq]; ring
    have hnorm : ‖s.K t x x‖ = 1 := by
      simpa using congrArg norm hKone
    linarith
  have hdenNorm : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - s.K t x x‖ := by
    have htriangle : (1 : ℝ) ≤ ‖(1 : ℂ) - s.K t x x‖ + ‖s.K t x x‖ := by
      calc
        1 = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖((1 : ℂ) - s.K t x x) + s.K t x x‖ := by congr 1 <;> ring
        _ ≤ ‖(1 : ℂ) - s.K t x x‖ + ‖s.K t x x‖ := norm_add_le _ _
    linarith
  have hinv : ‖(1 - s.K t x x)⁻¹‖ ≤ 2 := by
    have hpos : 0 < ‖(1 : ℂ) - s.K t x x‖ := lt_of_lt_of_le (by norm_num) hdenNorm
    rw [norm_inv]
    rw [← one_div]
    apply (div_le_iff₀ hpos).2
    nlinarith
  let T := AndersonAC.S45.survivors x
  let oldA : AndersonAC.S45.CMat P := 1 - s.K t
  let Jfull := AndersonAC.S45.Jinc t s x (z x)
  let Jr := AndersonAC.S45.restrict Jfull T
  let Mr := AndersonAC.S45.restrict oldA⁻¹ T
  let B := AndersonAC.S45.scalarSchur oldA x
  have hJrows : ∀ i : T,
      ∑ j : T, ‖Jr i j‖ ≤ 2 * G * M * R + (G ^ 2 + 2) * M ^ 2 * R := by
    have hJ := lagJinc_rowSum_bound t s x (z x) R M G 2 hR hM hG (by norm_num)
      hrow hmax (hgamma x hxS) hinv
    intro i
    have hattach : (∑ j : T, ‖Jr i j‖) =
        ∑ j ∈ T, ‖Jfull i.val j‖ := by
      simpa [Jr, AndersonAC.S45.restrict, Jfull] using
        (Finset.sum_attach (s := T) (f := fun j => ‖Jfull i.val j‖))
    rw [hattach]
    simpa [T] using hJ i.val
  have hMrows : ∀ i : T, ∑ j : T, ‖Mr i j‖ ≤ L := by
    intro i
    exact (lag_restrict_row_sum_le oldA⁻¹ T i).trans (by
      simpa [oldA, AndersonAC.S45.State.P] using hProw)
  have hupdate :
      (1 - (AndersonAC.S45.deleteState t s x (z x)).K t) = B - Jr := by
    dsimp [B, Jr, Jfull, Mr, oldA, T]
    exact lag_delete_A_update t s x (z x) ht ha (hden x hxS)
  have haA : oldA x x ≠ 0 := by simpa [oldA, Matrix.one_apply] using ha
  have hMB := lag_restrict_scalarSchur_left_inv oldA x hpre.invertible haA
  have hMB' : ∀ v : T → ℂ, ∀ i : T, (Mr *ᵥ (B *ᵥ v)) i = v i := by
    intro v i
    simpa [Mr, B, oldA, T] using hMB v i
  have hnew := lag_unit_small_perturbation B Jr Mr
    (1 - (AndersonAC.S45.deleteState t s x (z x)).K t) L
    (2 * G * M * R + (G ^ 2 + 2) * M ^ 2 * R)
    hL (by positivity) hsmall hupdate hMB' hMrows hJrows
  exact ⟨ha, hinv, hnew⟩

lemma lag_logFactor_mul_power_bound {e t : ℝ} (he : 0 < e)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    logFactor t * power t e ≤ 1 + 1 / e := by
  have hy : 0 < power t e := Real.rpow_pos_of_pos ht _
  have hy1 : power t e ≤ 1 := Real.rpow_le_one ht.le ht1 he.le
  have hlog : Real.log (1 / t) ≤ (1 / t) ^ e / e :=
    Real.log_le_rpow_div (by positivity) he
  have hrecip : (1 / t) ^ e = (power t e)⁻¹ := by
    rw [one_div]
    exact Real.inv_rpow ht.le e
  have hinv : (1 / t) ^ e * power t e = 1 := by
    rw [hrecip]
    exact inv_mul_cancel₀ (ne_of_gt hy)
  unfold logFactor
  calc
    (1 + Real.log (1 / t)) * power t e ≤
        (1 + (1 / t) ^ e / e) * power t e :=
      mul_le_mul_of_nonneg_right (by linarith) hy.le
    _ = power t e + 1 / e := by
      calc
        (1 + (1 / t) ^ e / e) * power t e =
            power t e + ((1 / t) ^ e * power t e) / e := by ring
        _ = power t e + 1 / e := by rw [hinv]
    _ ≤ 1 + 1 / e := by linarith

lemma lag_logFactor_sq_power_small {e a : ℝ} (he : 0 < e) (ha : 0 < a) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 → logFactor t ^ 2 * power t e < a := by
  let f : ℝ := e / 4
  let M : ℝ := 1 + 1 / f
  have hf : 0 < f := by dsimp [f]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hsmallExp : 0 < e / 2 := by linarith
  have hsmallVal : 0 < a / M ^ 2 := by positivity
  obtain ⟨t1, ht1, hpowerSmall⟩ := power_small hsmallExp hsmallVal
  let t0 := min t1 1
  refine ⟨t0, lt_min ht1 zero_lt_one, ?_⟩
  intro t ht htt
  have htt1 : t ≤ 1 := (lt_of_lt_of_le htt (min_le_right _ _)).le
  have httt1 : t < t1 := lt_of_lt_of_le htt (min_le_left _ _)
  have hlog := lag_logFactor_mul_power_bound hf ht htt1
  have hpower := hpowerSmall t ht httt1
  have hbase : 0 ≤ logFactor t * power t f := by
    unfold logFactor
    have harg : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    have hlog0 : 0 ≤ Real.log (1 / t) := Real.log_nonneg harg
    exact mul_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos ht f))
  have hM0 : 0 ≤ M := hM.le
  have hbaseSq : (logFactor t * power t f) ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ hbase hM0).2 hlog
  have hpowEq : (power t f) ^ 2 = power t (e / 2) := by
    change Real.rpow t (e / 4) ^ 2 = Real.rpow t (e / 2)
    calc
      Real.rpow t (e / 4) ^ 2 = Real.rpow t ((e / 4) * 2) :=
        (Real.rpow_mul_natCast ht.le (e / 4) 2).symm
      _ = Real.rpow t (e / 2) := by congr 1 <;> ring
  have hsplit : power t e = power t (e / 2) * power t (e / 2) := by
    change Real.rpow t e = Real.rpow t (e / 2) * Real.rpow t (e / 2)
    calc
      Real.rpow t e = Real.rpow t (e / 2 + e / 2) := by congr 1 <;> ring
      _ = Real.rpow t (e / 2) * Real.rpow t (e / 2) := Real.rpow_add ht _ _
  have heq : logFactor t ^ 2 * power t e =
      (logFactor t * power t f) ^ 2 * power t (e / 2) := by
    rw [hsplit, mul_pow, hpowEq]
    ring
  calc
    logFactor t ^ 2 * power t e =
        (logFactor t * power t f) ^ 2 * power t (e / 2) := heq
    _ ≤ M ^ 2 * power t (e / 2) :=
      mul_le_mul_of_nonneg_right hbaseSq (Real.rpow_nonneg ht.le _)
    _ < M ^ 2 * (a / M ^ 2) :=
      mul_lt_mul_of_pos_left hpower (by positivity)
    _ = a := by field_simp [ne_of_gt hM]

lemma lag_power_sq_eq {t e : ℝ} (ht : 0 < t) :
    power t e ^ 2 = power t (2 * e) := by
  change Real.rpow t e ^ 2 = Real.rpow t (2 * e)
  calc
    Real.rpow t e ^ 2 = Real.rpow t (e * 2) :=
      (Real.rpow_mul_natCast ht.le e 2).symm
    _ = Real.rpow t (2 * e) := by congr 1 <;> ring

lemma lag_power_mul_eq {t a b : ℝ} (ht : 0 < t) :
    power t a * power t b = power t (a + b) := by
  change Real.rpow t a * Real.rpow t b = Real.rpow t (a + b)
  exact (Real.rpow_add ht a b).symm

def lagGammaBound (C : ℝ) : ℝ := 4 * (2 * C + 2 * (1 + C ^ 2))

def lagPerturbBound (C A : ℝ) : ℝ :=
  A * (2 * lagGammaBound C + (lagGammaBound C ^ 2 + 2))

def lagContractionBound (C A : ℝ) : ℝ :=
  2 * (2 * lagGammaBound C) ^ 2 * A ^ 2 +
    2 * (lagGammaBound C ^ 2 + 2) ^ 2 * A ^ 2

def lagForcingBound (C A : ℝ) : ℝ :=
  2 * (lagGammaBound C + 2 * A) ^ 2 +
    16 * (2 * lagGammaBound C) ^ 2 * A ^ 2 +
    4 * (lagGammaBound C ^ 2 + 2) ^ 2 * A ^ 2

lemma lag_pivot_inverse_bound {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (hK : ‖s.K t‖ ≤ 1 / 2) :
    ∀ x, 1 - s.K t x x ≠ 0 ∧ ‖(1 - s.K t x x)⁻¹‖ ≤ 2 := by
  intro x
  have hKxx : ‖s.K t x x‖ ≤ 1 / 2 :=
    (lag_matrix_entry_norm_le (s.K t) x x).trans hK
  have hnonzero : 1 - s.K t x x ≠ 0 := by
    intro heq
    have hEq : s.K t x x = 1 := by
      calc
        s.K t x x = 1 - (1 - s.K t x x) := by ring
        _ = 1 := by rw [heq]; ring
    have hnorm : ‖s.K t x x‖ = 1 := by simpa [hEq]
    linarith
  have hden : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - s.K t x x‖ := by
    have htri : (1 : ℝ) ≤ ‖(1 : ℂ) - s.K t x x‖ + ‖s.K t x x‖ := by
      calc
        1 = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖((1 : ℂ) - s.K t x x) + s.K t x x‖ := by congr 1 <;> ring
        _ ≤ ‖(1 : ℂ) - s.K t x x‖ + ‖s.K t x x‖ := norm_add_le _ _
    linarith
  have hinv : ‖(1 - s.K t x x)⁻¹‖ ≤ 2 := by
    rw [norm_inv, ← one_div]
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).2
    nlinarith
  exact ⟨hnonzero, hinv⟩

end AndersonAC.AgentS45.LagSupport
