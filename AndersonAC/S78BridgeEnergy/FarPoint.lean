import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.EnergyInputs
import AndersonAC.S78.AssemblyForms
import AndersonAC.S78.AssemblySummation
import AndersonAC.S78Moment.Moments
import AndersonAC.S78Moment.Translation
import AndersonAC.S78AnchorTail.Geometry
import AndersonAC.S78BridgeEnergy.Basic
import AndersonAC.S78BridgeEnergy.Weights
import AndersonAC.S78BridgeEnergy.FarWeight
import AndersonAC.S78BridgeEnergy.Near
import AndersonAC.S78BridgeEnergy.Far

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- Far point-to-mean energy via the deviation input and halo overlap. -/
theorem term_point_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C c Cdev Cmom0 : ℝ) (hC : 1 ≤ C) (hc : 0 < c) (hCdev : 0 ≤ Cdev)
    (hM0 : 0 ≤ Cmom0)
    (hIC : I.C = C) (hIc : I.c = c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C)
    (hmom0 : ∀ x : Torus d m,
      (∑ y, Real.exp (-(c / 16) * t * physicalDistance d m x y) *
        physicalDistance d m x y ^ (0 : ℕ)) ≤
        Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))
    (hdevAll : ∀ (m : ℕ) (z : Torus d m) (R Lmax Ltotal : ℝ) (l v : Torus d m → ℝ),
      1 ≤ R → 4 * R < (OAI.Anderson.sideLength m : ℝ) → 0 ≤ Lmax → 0 ≤ Ltotal →
      (∀ i, 0 ≤ l i ∧ l i ≤ Lmax) → (∀ i, i ∉ cube d m z R → l i = 0) →
      (∑ i, l i) ≤ Ltotal →
      (∑ i, l i * (v i - localCubeMean d m z R v) ^ 2 ≤
        Cdev * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
          cubeGradient d m (cube d m z (2 * R)) v ∧
        (v z - localCubeMean d m z R v) ^ 2 ≤
          Cdev * R ^ 2 * cubeGradient d m (cube d m z (2 * R)) v))
    (hmov : ∀ x, ((overlap (fun a => cube d m (I.anchor a) (200 * I.Ds)) x : ℕ) : ℝ) ≤
      C * t ^ (-(d : ℝ) * nu d))
    (hR : 1 ≤ 100 * I.Ds)
    (hside : 4 * (100 * I.Ds) < (OAI.Anderson.sideLength m : ℝ))
    (S : Finset (Fin k)) (v : Torus d m → ℝ) :
    ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 ≤
      (C ^ 5 * t ^ (-2 - heatExponent) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
        (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))) *
        gradientEnergy (nnGraph d m) v := by
  classical
  have hKwE0nn : 0 ≤ (C ^ 5 * t ^ (-2 - heatExponent)) *
      Real.exp (-(c / 8) * t * (50 * I.Ds)) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)) (Real.exp_pos _).le
  have hKwM0nn : 0 ≤ C ^ 5 * t ^ (-2 - heatExponent) *
      Real.exp (-(c / 8) * t * (50 * I.Ds)) *
      (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) :=
    mul_nonneg hKwE0nn (mul_nonneg hM0 (Real.rpow_nonneg ht.le _))
  have hDsR : I.Ds ≤ C * t ^ (-8 - nu d) := by
    rw [← hIC]
    exact I.scaleRadius.2
  have hDsnn : 0 ≤ (100 : ℝ) * I.Ds := by
    have hpos : 0 < I.Ds :=
      (Real.rpow_pos_of_pos ht _).trans_le I.scaleRadius.1
    positivity
  have hR2 : ((100 : ℝ) * I.Ds) ^ 2 ≤ (100 * C) ^ 2 * t ^ (-16 - 2 * nu d) := by
    have hbase : (100 : ℝ) * I.Ds ≤ (100 * C) * t ^ (-8 - nu d) := by
      calc (100 : ℝ) * I.Ds ≤ 100 * (C * t ^ (-8 - nu d)) :=
            mul_le_mul_of_nonneg_left hDsR (by norm_num)
        _ = (100 * C) * t ^ (-8 - nu d) := by ring
    have hsq := pow_le_pow_left₀ hDsnn hbase 2
    have eSq : (((100 * C)) * t ^ (-8 - nu d)) ^ 2 =
        (100 * C) ^ 2 * t ^ (-16 - 2 * nu d) := by
      have hexp : (-8 - nu d) + (-8 - nu d) = -16 - 2 * nu d := by ring
      calc (((100 * C)) * t ^ (-8 - nu d)) ^ 2
          = (100 * C) ^ 2 * (t ^ (-8 - nu d) * t ^ (-8 - nu d)) := by ring
        _ = (100 * C) ^ 2 * t ^ (-16 - 2 * nu d) := by
            rw [← Real.rpow_add ht, hexp]
    exact hsq.trans eSq.le
  -- Total far weight per operation.
  have hwt : ∀ a ∈ S,
      (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2)) ≤
      ((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) := by
    intro a _
    have hper : ∀ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) ≤
        ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by
      intro i hi
      have hiQ : i ∉ cube d m (I.anchor a) (100 * I.Ds) :=
        (Finset.mem_filter.mp hi).2
      exact far_weight_split I C c hC hc hIC hIc ht ht1 hdamp a i hiQ
    have hswap : (∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          ((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds))) *
            Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) ≤
        ∑ i, ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      apply mul_nonneg _ (Real.exp_pos _).le
      exact hKwE0nn
    have hfac : (∑ i, ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) =
        ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          (∑ i, Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) := by
      rw [Finset.mul_sum]
    have hconv : (∑ i, Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) =
        ∑ y, Real.exp (-(c / 16) * t * physicalDistance d m (I.anchor a) y) *
          physicalDistance d m (I.anchor a) y ^ (0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [physicalDistance_comm d m y (I.anchor a), pow_zero, mul_one]
    calc (∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2))
        ≤ ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds))) *
            Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) :=
          Finset.sum_le_sum fun i hi => hper i hi
      _ ≤ ∑ i, (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) := hswap
      _ = ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          (∑ i, Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) := by
          rw [hfac]
      _ = ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          (∑ y, Real.exp (-(c / 16) * t * physicalDistance d m (I.anchor a) y) *
            physicalDistance d m (I.anchor a) y ^ (0 : ℕ)) := by
          rw [hconv]
      _ ≤ ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hmom0 (I.anchor a)) hKwE0nn
  -- Pointwise deviation via the zero-weight input.
  have hpt : ∀ a : Fin k,
      (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 ≤
        Cdev * ((100 * I.Ds) ^ 2) *
          cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v := by
    intro a
    obtain ⟨_, hpoint⟩ := hdevAll m (I.anchor a) (100 * I.Ds) 0 0
      (fun _ => (0 : ℝ)) v hR hside le_rfl le_rfl
      (fun i => ⟨le_rfl, le_rfl⟩) (fun i _ => rfl) (by simp)
    have hQR : (2 : ℝ) * (100 * I.Ds) = 200 * I.Ds := by ring
    have hgrad_eq : cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v =
        cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v := by rw [hQR]
    rw [hgrad_eq] at hpoint
    have hassoc : Cdev * (100 * I.Ds) ^ 2 *
        cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v =
        Cdev * ((100 * I.Ds) ^ 2) *
          cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v := by ring
    rw [hassoc]
    exact hpoint
  -- Combine over operations with halo overlap.
  have hhalo : (∑ a : Fin k, cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) ≤
      (C * t ^ (-(d : ℝ) * nu d)) * gradientEnergy (nnGraph d m) v :=
    AndersonAC.SolS78.sum_cube_gradients_overlap d m
      (fun a => cube d m (I.anchor a) (200 * I.Ds)) v _ hmov
  have hA : Cdev * ((100 : ℝ) * I.Ds) ^ 2 ≤
      Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) :=
    mul_le_mul_of_nonneg_left hR2 hCdev
  have hBnn : 0 ≤ ∑ a : Fin k,
      cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v :=
    Finset.sum_nonneg fun a _ => cubeGradient_nonneg _ _ _ _
  have hbnn : 0 ≤ Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) := by
    apply mul_nonneg hCdev
    apply mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)
  have hAB : (Cdev * ((100 : ℝ) * I.Ds) ^ 2) *
      (∑ a : Fin k, cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) ≤
      (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d))) *
        ((C * t ^ (-(d : ℝ) * nu d)) * gradientEnergy (nnGraph d m) v) :=
    mul_le_mul hA hhalo hBnn hbnn
  calc ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2
      ≤ ∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2)) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        rw [Finset.sum_mul]
      _ ≤ ∑ a ∈ S, ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
        (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        apply mul_le_mul_of_nonneg_right (hwt a ha) (sq_nonneg _)
      _ = ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
        (∑ a ∈ S, (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
        (∑ a : Fin k, (Cdev * ((100 * I.Ds) ^ 2) *
          cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v)) := by
        apply mul_le_mul_of_nonneg_left _ hKwM0nn
        calc (∑ a ∈ S, (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)
            ≤ ∑ a ∈ S, (Cdev * ((100 * I.Ds) ^ 2) *
              cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) :=
              Finset.sum_le_sum fun a _ => hpt a
          _ ≤ ∑ a : Fin k, (Cdev * ((100 * I.Ds) ^ 2) *
              cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
                (fun a _ _ => mul_nonneg (mul_nonneg hCdev (sq_nonneg _))
                  (cubeGradient_nonneg _ _ _ _))
      _ ≤ ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
        ((Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d))) *
          gradientEnergy (nnGraph d m) v) := by
        apply mul_le_mul_of_nonneg_left _ hKwM0nn
        calc (∑ a : Fin k, (Cdev * ((100 * I.Ds) ^ 2) *
            cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v))
            = (Cdev * ((100 * I.Ds) ^ 2)) *
              (∑ a : Fin k, cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) := by
              rw [Finset.mul_sum]
          _ ≤ (Cdev * (((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)))) *
              ((C * t ^ (-(d : ℝ) * nu d)) * gradientEnergy (nnGraph d m) v) :=
              hAB
          _ = (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d))) *
              gradientEnergy (nnGraph d m) v := by ring
      _ = (C ^ 5 * t ^ (-2 - heatExponent) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
        (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))) *
        gradientEnergy (nnGraph d m) v := by ring

end AndersonAC.S78BridgeEnergy
