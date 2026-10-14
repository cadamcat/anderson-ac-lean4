import AndersonAC.S78SurvivorTail.Basic
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.AssemblyForms

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.S78SurvivorTail
open AndersonAC.S78
open AndersonAC.SolS78

/-- Far pairs are exactly those with an endpoint outside the 100 Ds cube. -/
theorem far_outside_cube {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k)
    (q : Torus d m × Torus d m)
    (hq : q ∈ (I.state a.succ).active.product (I.state a.succ).active \
      (assemblyNearSites I a).product (assemblyNearSites I a)) :
    q.1 ∉ cube d m (I.anchor a) (100 * I.Ds) ∨
      q.2 ∉ cube d m (I.anchor a) (100 * I.Ds) := by
  classical
  have hmem := (Finset.mem_sdiff.mp hq).1
  have hnot := (Finset.mem_sdiff.mp hq).2
  have hm := Finset.mem_product.mp hmem
  -- hm : q.1 ∈ A ∧ q.2 ∈ A
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  apply hnot
  have h1 : q.1 ∈ assemblyNearSites I a := Finset.mem_inter.mpr ⟨hc1, hm.1⟩
  have h2 : q.2 ∈ assemblyNearSites I a := Finset.mem_inter.mpr ⟨hc2, hm.2⟩
  exact Finset.mem_product.mpr ⟨h1, h2⟩

/-- Crude old-kernel bound from resolvent decay (exponential dropped). -/
theorem old_entry_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (i j : Torus d m)
    (ht : 0 < t) :
    ‖normalizedInverse (I.state a.castSucc) t i j‖ ≤ I.C / Real.sqrt t := by
  have hcpos : 0 < I.c := I.positive.2.2.2.2.1
  have hCnonneg : (0 : ℝ) ≤ I.C := by linarith [I.positive.2.2.2.2.2.1]
  have hdec := I.resolventDecay a.castSucc i j
  have hexp : Real.exp (-I.c * t *
      max (physicalDistance d m i j / 2 - t ^ (-1.03 : ℝ)) 0) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnn : 0 ≤ max (physicalDistance d m i j / 2 - t ^ (-1.03 : ℝ)) 0 :=
      le_max_right _ _
    have hct : 0 ≤ I.c * t := mul_nonneg hcpos.le ht.le
    nlinarith [mul_nonneg hct hnn]
  calc ‖normalizedInverse (I.state a.castSucc) t i j‖
      ≤ I.C / Real.sqrt t *
        Real.exp (-I.c * t * max (physicalDistance d m i j / 2 - t ^ (-1.03 : ℝ)) 0) := hdec
    _ ≤ I.C / Real.sqrt t * 1 := by
        apply mul_le_mul_of_nonneg_left hexp
        exact div_nonneg hCnonneg (Real.sqrt_nonneg _)
    _ = I.C / Real.sqrt t := mul_one _

/-- On retained pairs the new kernel is old plus the survivor difference. -/
theorem new_eq_old_add_diff {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (i j : Torus d m)
    (hi : i ∈ (I.state a.succ).active) (hj : j ∈ (I.state a.succ).active) :
    normalizedInverse (I.state a.succ) t i j =
      normalizedInverse (I.state a.castSucc) t i j +
        survivorDifference (I.state a.castSucc) (I.state a.succ) t i j := by
  have hB : (I.state a.succ).active ⊆ (I.state a.succ).active := Finset.Subset.refl _
  have h := survivor_difference_identity (I.state a.castSucc) (I.state a.succ) t
    (I.state a.succ).active hB i hi j hj
  rw [Matrix.add_apply] at h
  exact h

/-- Kernel square difference from the cross term plus square. -/
theorem kernel_diff_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (i j : Torus d m)
    (hi : i ∈ (I.state a.succ).active) (hj : j ∈ (I.state a.succ).active) :
    |‖normalizedInverse (I.state a.succ) t i j‖ ^ 2 -
      ‖normalizedInverse (I.state a.castSucc) t i j‖ ^ 2| ≤
      2 * ‖normalizedInverse (I.state a.castSucc) t i j‖ *
        ‖survivorDifference (I.state a.castSucc) (I.state a.succ) t i j‖ +
      ‖survivorDifference (I.state a.castSucc) (I.state a.succ) t i j‖ ^ 2 := by
  have heq := new_eq_old_add_diff I a i j hi hj
  rw [heq]
  exact normSq_sub_le _ _

/-- Pure-real estimate combining a crude old bound with an exponential
difference bound; the squared exponential is absorbed since it is ≤ 1. -/
theorem pair_kernel_exp_le (oldN D : ℂ) (Csqrt rP E0 E : ℝ)
    (hOld : ‖oldN‖ ≤ Csqrt) (hD : ‖D‖ ≤ rP * E0 * E)
    (hCsqrt : 0 ≤ Csqrt) (hrP : 0 ≤ rP)
    (hE0nn : 0 ≤ E0) (hE0le : E0 ≤ 1) (hEnn : 0 ≤ E) (hEle : E ≤ 1) :
    |‖oldN + D‖ ^ 2 - ‖oldN‖ ^ 2| ≤ (2 * Csqrt * rP + rP * rP) * E0 * E := by
  have hEE : 0 ≤ E0 * E := mul_nonneg hE0nn hEnn
  have hEEle : E0 * E ≤ 1 := by
    calc E0 * E ≤ 1 * 1 := mul_le_mul hE0le hEle hEnn (by norm_num)
      _ = 1 := mul_one _
  have hDnn : 0 ≤ ‖D‖ := norm_nonneg _
  have hbase := normSq_sub_le oldN D
  have h1 : 2 * ‖oldN‖ * ‖D‖ ≤ 2 * Csqrt * rP * E0 * E := by
    calc 2 * ‖oldN‖ * ‖D‖ ≤ 2 * Csqrt * (rP * E0 * E) :=
          mul_le_mul (by linarith [hOld, hCsqrt]) hD (by positivity) (by positivity)
      _ = 2 * Csqrt * rP * E0 * E := by ring
  have h2 : ‖D‖ ^ 2 ≤ rP * rP * E0 * E := by
    have hD2 : ‖D‖ ^ 2 ≤ (rP * E0 * E) ^ 2 := by
      apply pow_le_pow_left₀ hDnn hD 2
    have hsq : (rP * E0 * E) ^ 2 = (rP * rP) * ((E0 * E) ^ 2) := by ring
    have hEE2 : (E0 * E) ^ 2 ≤ E0 * E := by
      calc (E0 * E) ^ 2 = (E0 * E) * (E0 * E) := pow_two _
        _ ≤ 1 * (E0 * E) := mul_le_mul_of_nonneg_right hEEle hEE
        _ = E0 * E := one_mul _
    calc ‖D‖ ^ 2 ≤ (rP * E0 * E) ^ 2 := hD2
      _ = (rP * rP) * ((E0 * E) ^ 2) := hsq
      _ ≤ (rP * rP) * (E0 * E) :=
          mul_le_mul_of_nonneg_left hEE2 (by positivity)
      _ = rP * rP * E0 * E := by ring
  calc |‖oldN + D‖ ^ 2 - ‖oldN‖ ^ 2|
      ≤ 2 * ‖oldN‖ * ‖D‖ + ‖D‖ ^ 2 := hbase
    _ ≤ (2 * Csqrt * rP * E0 * E) + (rP * rP * E0 * E) := add_le_add h1 h2
    _ = (2 * Csqrt * rP + rP * rP) * E0 * E := by ring

/-- Absolute survivor tail by the far-pair absolute sum. -/
theorem tail_abs_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) :
    |assemblySurvivorTail I a f| ≤ (I.C ^ 2 / 2) *
      ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
      |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
        (f q.1 - f q.2) ^ 2 := by
  classical
  have hcpos : 0 < I.c := I.positive.2.2.2.2.1
  have hC1 : (1 : ℝ) ≤ I.C := I.positive.2.2.2.2.2.1
  have hCnonneg : (0 : ℝ) ≤ I.C := by linarith
  have hp_nonneg : ∀ i : Torus d m, 0 ≤ (r i).im := fun i =>
    le_trans hcpos.le (I.damping i).1
  have hp_le : ∀ i : Torus d m, (r i).im ≤ I.C := fun i => (I.damping i).2.1
  have hpp_le : ∀ i j : Torus d m, (r i).im * (r j).im ≤ I.C ^ 2 := by
    intro i j
    calc (r i).im * (r j).im ≤ I.C * I.C :=
          mul_le_mul (hp_le i) (hp_le j) (hp_nonneg j) hCnonneg
      _ = I.C ^ 2 := (pow_two _).symm
  rw [tail_eq_far_sum I a f]
  have hhalf : |(1 / 2 : ℝ) *
      ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
      (r q.1).im * (r q.2).im *
        (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) *
        (f q.1 - f q.2) ^ 2| =
      (1 / 2 : ℝ) * |∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
      (r q.1).im * (r q.2).im *
        (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) *
        (f q.1 - f q.2) ^ 2| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hhalf]
  have hR : (I.C ^ 2 / 2) *
      ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
      |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
        (f q.1 - f q.2) ^ 2 =
      (1 / 2 : ℝ) * (I.C ^ 2 * ∑ q ∈ ((I.state a.succ).active.product
        (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
      |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
        (f q.1 - f q.2) ^ 2) := by ring
  rw [hR]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have htri := norm_sum_le
    (s := (I.state a.succ).active.product (I.state a.succ).active \
      (assemblyNearSites I a).product (assemblyNearSites I a))
    (f := fun q : Torus d m × Torus d m => (r q.1).im * (r q.2).im *
      (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) *
      (f q.1 - f q.2) ^ 2)
  simp only [Real.norm_eq_abs] at htri
  refine htri.trans ?_
  have hterm : ∀ q : Torus d m × Torus d m,
      |(r q.1).im * (r q.2).im *
        (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) *
        (f q.1 - f q.2) ^ 2| ≤
      I.C ^ 2 * (|‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
        (f q.1 - f q.2) ^ 2) := by
    intro q
    have hsq : (0 : ℝ) ≤ (f q.1 - f q.2) ^ 2 := sq_nonneg _
    have habs : (0 : ℝ) ≤ |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| := abs_nonneg _
    calc |(r q.1).im * (r q.2).im *
          (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) *
          (f q.1 - f q.2) ^ 2|
        = ((r q.1).im * (r q.2).im) *
          (|‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
          (f q.1 - f q.2) ^ 2) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hsq,
            abs_of_nonneg (mul_nonneg (hp_nonneg q.1) (hp_nonneg q.2))]
          ring
      _ ≤ I.C ^ 2 *
          (|‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
          (f q.1 - f q.2) ^ 2) :=
        mul_le_mul_of_nonneg_right (hpp_le q.1 q.2) (mul_nonneg habs hsq)
  calc ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
        |(r q.1).im * (r q.2).im *
          (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) *
          (f q.1 - f q.2) ^ 2|
      ≤ ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
        I.C ^ 2 * (|‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
          (f q.1 - f q.2) ^ 2) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = I.C ^ 2 * ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
        |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
          (f q.1 - f q.2) ^ 2 := by rw [Finset.mul_sum]

end AndersonAC.S78SurvivorTail
