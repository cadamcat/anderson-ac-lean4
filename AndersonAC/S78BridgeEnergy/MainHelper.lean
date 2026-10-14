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
import AndersonAC.S78BridgeEnergy.NearMain
import AndersonAC.S78BridgeEnergy.Far
import AndersonAC.S78BridgeEnergy.FarPoint
import AndersonAC.S78BridgeEnergy.FarMain
import AndersonAC.S78BridgeEnergy.Ward

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- `1 ≤ 100 * Ds` from the scale radius and `t ≤ 1`. -/
theorem Ds_R_ge_one {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (ht : 0 < t) (ht1 : t ≤ 1) :
    1 ≤ 100 * I.Ds := by
  classical
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have hle : (-8 - nu d) ≤ (0 : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ t ^ (-8 - nu d) := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 hle
    simpa only [Real.rpow_zero] using h
  have hDs : t ^ (-8 - nu d) ≤ I.Ds := I.scaleRadius.1
  have h1Ds : (1 : ℝ) ≤ I.Ds := h1.trans hDs
  have hpos : 0 ≤ I.Ds := by linarith
  nlinarith

/-- The lag exponent is nonnegative. -/
theorem lag_exp_nonneg {d : ℕ} (hd : 3 ≤ d) :
    0 ≤ 0.42 * delta - (d : ℝ) * nu d := by
  have hdpos : 0 < (d : ℝ) := by
    have : 0 < d := by omega
    exact Nat.cast_pos.mpr this
  unfold nu delta
  have h : (d : ℝ) * (1 / 100 / (100000 * (d : ℝ))) = 1 / 100 / 100000 := by
    field_simp
  rw [h]
  norm_num

/-- `t * Ds` dominates `t ^ (-7 - ν)`. -/
theorem tDs_ge {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (ht : 0 < t) :
    t ^ (-7 - nu d) ≤ t * I.Ds := by
  have hDs : t ^ (-8 - nu d) ≤ I.Ds := I.scaleRadius.1
  have h1 : t * t ^ (-8 - nu d) = t ^ (-7 - nu d) := by
    have h : t ^ (1 : ℝ) * t ^ (-8 - nu d) = t ^ (-7 - nu d) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rwa [Real.rpow_one] at h
  rw [← h1]
  exact mul_le_mul_of_nonneg_left hDs ht.le

/-- Far exponential is dominated by the `t ^ (-7 - ν)` rate. -/
theorem far_exp_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (c : ℝ) (hc : 0 < c) (ht : 0 < t) :
    Real.exp (-(c / 8) * t * (50 * I.Ds)) ≤
      Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) := by
  have hbase : t ^ (-7 - nu d) ≤ t * I.Ds := tDs_ge I ht
  have h50 : (50 : ℝ) * t ^ (-7 - nu d) ≤ t * (50 * I.Ds) := by
    calc (50 : ℝ) * t ^ (-7 - nu d) ≤ 50 * (t * I.Ds) :=
          mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = t * (50 * I.Ds) := by ring
  have hK : 0 ≤ (c / 8) := by positivity
  have hle : -(c / 8) * t * (50 * I.Ds) ≤ -((c / 8) * 50) * t ^ (-7 - nu d) := by
    have heq1 : -(c / 8) * t * (50 * I.Ds) = -((c / 8) * (t * (50 * I.Ds))) := by ring
    have heq2 : -((c / 8) * 50) * t ^ (-7 - nu d) = -((c / 8) * ((50 : ℝ) * t ^ (-7 - nu d))) := by ring
    rw [heq1, heq2]
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left h50 hK
  exact Real.exp_le_exp.mpr hle

/-- Global split dominates the `α` mass. -/
theorem alpha_le_global {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (α v : Torus d m → ℝ) :
    ∑ i ∈ (I.state 0).active, (α i) ^ 2 ≤ assemblyGlobalSplit I α v := by
  classical
  unfold assemblyGlobalSplit
  have hnn : 0 ≤ b⁻¹ * gradientEnergy (nnGraph d m) v :=
    mul_nonneg (inv_nonneg.mpr I.positive.2.2.1.le) (gradient_energy_nonneg _ _)
  linarith

/-- Global split dominates the gradient energy when `b ≤ 1`. -/
theorem grad_le_global {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (hb1 : b ≤ 1)
    (α v : Torus d m → ℝ) :
    gradientEnergy (nnGraph d m) v ≤ assemblyGlobalSplit I α v := by
  classical
  unfold assemblyGlobalSplit
  have hG : 0 ≤ gradientEnergy (nnGraph d m) v := gradient_energy_nonneg _ _
  have hA : 0 ≤ ∑ i ∈ (I.state 0).active, (α i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbpos : 0 < b := I.positive.2.2.1
  have hbinv : 1 ≤ b⁻¹ := (one_le_inv_iff₀).mpr ⟨hbpos, hb1⟩
  have hle : gradientEnergy (nnGraph d m) v ≤ b⁻¹ * gradientEnergy (nnGraph d m) v := by
    calc gradientEnergy (nnGraph d m) v = 1 * gradientEnergy (nnGraph d m) v := by ring
      _ ≤ b⁻¹ * gradientEnergy (nnGraph d m) v :=
        mul_le_mul_of_nonneg_right hbinv hG
  linarith

end AndersonAC.S78BridgeEnergy
