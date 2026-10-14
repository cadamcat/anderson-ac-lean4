import AndersonAC.S78SurvivorTail.Bound
import AndersonAC.S78.TailEnergy
import AndersonAC.S78.AssemblySummation

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.S78SurvivorTail
open AndersonAC.S78
open AndersonAC.SolS78

/-- Zero-extended mass agrees with the initial active mass. -/
theorem zeroExtend_mass {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (α : Torus d m → ℝ) :
    let αt : Torus d m → ℝ := fun i => if i ∈ (I.state 0).active then α i else 0
    (∑ i, (αt i) ^ 2) = ∑ i ∈ (I.state 0).active, (α i) ^ 2 := by
  classical
  simp only
  have hsub : (I.state 0).active ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ i ∈ (Finset.univ : Finset (Torus d m)), i ∉ (I.state 0).active →
      ((if i ∈ (I.state 0).active then α i else 0) ^ 2) = 0 := by
    intro i _ hni
    simp [hni]
  have hsplit := Finset.sum_subset hsub hzero
  have hagree : ∀ i ∈ (I.state 0).active,
      ((if i ∈ (I.state 0).active then α i else 0) ^ 2) = (α i) ^ 2 := by
    intro i hi
    simp [hi]
  calc ∑ i, ((if i ∈ (I.state 0).active then α i else 0) ^ 2)
      = ∑ i ∈ (I.state 0).active, ((if i ∈ (I.state 0).active then α i else 0) ^ 2) := hsplit.symm
    _ = ∑ i ∈ (I.state 0).active, (α i) ^ 2 := Finset.sum_congr rfl hagree

/-- On initial active sites the zero extension agrees. -/
theorem zeroExtend_agree {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (α : Torus d m → ℝ) (i : Torus d m)
    (hi : i ∈ (I.state 0).active) :
    (if i ∈ (I.state 0).active then α i else 0) = α i := by
  simp [hi]

/-- Global split is nonnegative. -/
theorem globalSplit_nonneg {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (α v : Torus d m → ℝ)
    (hb : 0 < b) :
    0 ≤ assemblyGlobalSplit I α v := by
  unfold assemblyGlobalSplit
  have hmass : 0 ≤ ∑ i ∈ (I.state 0).active, (α i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgrad : 0 ≤ gradientEnergy (nnGraph d m) v :=
    gradient_energy_nonneg _ _
  have hbnn : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  linarith [mul_nonneg hbnn hgrad]

/-- Mass plus gradient is controlled by the global split when b ≤ 1. -/
theorem mass_grad_le_globalSplit {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (αt v : Torus d m → ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hmass : (∑ i, (αt i) ^ 2) = ∑ i ∈ (I.state 0).active, (αt i) ^ 2) :
    (∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v ≤
      assemblyGlobalSplit I αt v := by
  unfold assemblyGlobalSplit
  rw [← hmass]
  have hgrad : 0 ≤ gradientEnergy (nnGraph d m) v :=
    gradient_energy_nonneg _ _
  have hbE : b * gradientEnergy (nnGraph d m) v ≤ gradientEnergy (nnGraph d m) v := by
    calc b * gradientEnergy (nnGraph d m) v ≤ 1 * gradientEnergy (nnGraph d m) v :=
          mul_le_mul_of_nonneg_right hb1 hgrad
      _ = gradientEnergy (nnGraph d m) v := one_mul _
  have hEb : gradientEnergy (nnGraph d m) v ≤
      b⁻¹ * gradientEnergy (nnGraph d m) v := by
    have hbnn : (0 : ℝ) ≤ b⁻¹ := inv_nonneg.mpr hb.le
    have hcancel : b⁻¹ * (b * gradientEnergy (nnGraph d m) v) =
        gradientEnergy (nnGraph d m) v := by
      rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
    calc gradientEnergy (nnGraph d m) v = b⁻¹ * (b * gradientEnergy (nnGraph d m) v) := hcancel.symm
      _ ≤ b⁻¹ * gradientEnergy (nnGraph d m) v :=
          mul_le_mul_of_nonneg_left hbE hbnn
  linarith

/-- Summation of far exponential weights through distinct anchors and the
global split energy. The anchor and split bounds enter as hypotheses. -/
theorem sum_far_exp_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (S : Finset (Fin k))
    (αt v : Torus d m → ℝ) (c C_anch C_split : ℝ)
    (hAnch : ∀ i j : Torus d m,
      (∑ a : Fin k, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a)))) ≤
      C_anch * t ^ (-(d : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i j))
    (hSplit : (∑ i, ∑ j, Real.exp (-(c / 8) * t * physicalDistance d m i j) *
        (((αt i + v i) - (αt j + v j)) ^ 2)) ≤
      C_split * t ^ (-(d : ℝ) - 2) * ((∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v))
    (hCanch : 0 ≤ C_anch) (_hCsplit : 0 ≤ C_split)
    (ht : 0 < t) :
    (∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
      (assemblyNearSites I a).product (assemblyNearSites I a)),
      Real.exp (-(c / 4) * t *
        (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
        (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) ≤
    C_anch * t ^ (-(d : ℝ)) * (C_split * t ^ (-(d : ℝ) - 2) *
      ((∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v)) := by
  classical
  -- nonnegativity of each summand
  have hEDnn : ∀ (a : Fin k) (q : Torus d m × Torus d m),
      0 ≤ Real.exp (-(c / 4) * t *
        (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
        (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2) := by
    intro a q
    exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hDnn : ∀ i j : Torus d m,
      0 ≤ (((αt i + v i) - (αt j + v j)) ^ 2) := fun i j => sq_nonneg _
  -- each far set lies in the full product
  have hfar_sub : ∀ a : Fin k,
      ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)) ⊆
      Finset.univ.product Finset.univ :=
    fun a => Finset.Subset.trans Finset.sdiff_subset
      (Finset.product_subset_product (Finset.subset_univ _) (Finset.subset_univ _))
  -- enlarge each far sum to the full product
  have henlarge : ∀ a : Fin k,
      (∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
        Real.exp (-(c / 4) * t *
          (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
          (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) ≤
      ∑ q ∈ (Finset.univ.product Finset.univ : Finset (Torus d m × Torus d m)),
        Real.exp (-(c / 4) * t *
          (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
          (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2) := by
    intro a
    exact Finset.sum_le_sum_of_subset_of_nonneg (hfar_sub a)
      (fun q _ _ => hEDnn a q)
  -- convert full product sums to double sums
  have hprod : ∀ a : Fin k,
      (∑ q ∈ (Finset.univ.product Finset.univ : Finset (Torus d m × Torus d m)),
        Real.exp (-(c / 4) * t *
          (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
          (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) =
      ∑ i, ∑ j, Real.exp (-(c / 4) * t *
          (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a))) *
          (((αt i + v i) - (αt j + v j)) ^ 2) := by
    intro a
    exact Finset.sum_product' Finset.univ Finset.univ
      (fun i j => Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a))) *
        (((αt i + v i) - (αt j + v j)) ^ 2))
  -- chain enlargements
  have hstep1 : (∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
      (assemblyNearSites I a).product (assemblyNearSites I a)),
      Real.exp (-(c / 4) * t *
        (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
        (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) ≤
      ∑ a ∈ S, (∑ i, ∑ j, Real.exp (-(c / 4) * t *
          (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a))) *
          (((αt i + v i) - (αt j + v j)) ^ 2)) :=
    Finset.sum_le_sum fun a _ => (henlarge a).trans_eq (hprod a)
  -- swap sums to bring the anchor sum inside
  have hswap : (∑ a ∈ S, (∑ i, ∑ j, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a))) *
        (((αt i + v i) - (αt j + v j)) ^ 2))) =
      ∑ i, ∑ j, (∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a))) *
        (((αt i + v i) - (αt j + v j)) ^ 2)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hswap] at hstep1
  -- factor the i,j difference out of the anchor sum
  have hfactor : ∀ i j : Torus d m,
      (∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a))) *
        (((αt i + v i) - (αt j + v j)) ^ 2)) =
      (∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a)))) *
        (((αt i + v i) - (αt j + v j)) ^ 2) := by
    intro i j
    rw [Finset.sum_mul]
  have hstep2 : (∑ i, ∑ j, (∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a))) *
        (((αt i + v i) - (αt j + v j)) ^ 2))) =
      ∑ i, ∑ j, ((∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a)))) *
        (((αt i + v i) - (αt j + v j)) ^ 2)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfactor i j
  rw [hstep2] at hstep1
  -- bound the inner anchor sums by the anchored estimate
  have hSle : ∀ i j : Torus d m,
      (∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a)))) ≤
      C_anch * t ^ (-(d : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i j) := by
    intro i j
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun a _ _ => (Real.exp_pos _).le)).trans ?_
    exact hAnch i j
  have hinner : ∀ i j : Torus d m,
      ((∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a)))) *
        (((αt i + v i) - (αt j + v j)) ^ 2)) ≤
      (C_anch * t ^ (-(d : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i j)) *
        (((αt i + v i) - (αt j + v j)) ^ 2) :=
    fun i j => mul_le_mul_of_nonneg_right (hSle i j) (hDnn i j)
  have hstep3 : (∑ i, ∑ j, ((∑ a ∈ S, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a)))) *
        (((αt i + v i) - (αt j + v j)) ^ 2))) ≤
      ∑ i, ∑ j, (C_anch * t ^ (-(d : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i j)) *
        (((αt i + v i) - (αt j + v j)) ^ 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hinner i j
  have hpull : (∑ i, ∑ j, (C_anch * t ^ (-(d : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i j)) *
        (((αt i + v i) - (αt j + v j)) ^ 2)) =
      C_anch * t ^ (-(d : ℝ)) * ∑ i, ∑ j, Real.exp (-(c / 8) * t * physicalDistance d m i j) *
        (((αt i + v i) - (αt j + v j)) ^ 2) := by
    simp only [mul_assoc, ← Finset.mul_sum]
  have hstep4 := hstep1.trans (hstep3.trans_eq hpull)
  -- apply the split-energy bound
  have htpow_nn : (0 : ℝ) ≤ C_anch * t ^ (-(d : ℝ)) :=
    mul_nonneg hCanch (Real.rpow_nonneg ht.le _)
  calc (∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
        Real.exp (-(c / 4) * t *
          (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
          (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2))
      ≤ C_anch * t ^ (-(d : ℝ)) * ∑ i, ∑ j, Real.exp (-(c / 8) * t * physicalDistance d m i j) *
          (((αt i + v i) - (αt j + v j)) ^ 2) := hstep4
    _ ≤ C_anch * t ^ (-(d : ℝ)) * (C_split * t ^ (-(d : ℝ) - 2) *
        ((∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v)) :=
        mul_le_mul_of_nonneg_left hSplit htpow_nn
    _ = _ := by ring

end AndersonAC.S78SurvivorTail
