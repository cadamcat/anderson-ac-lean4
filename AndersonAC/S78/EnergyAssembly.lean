import AndersonAC.S78.NearEnergy
import AndersonAC.S78.EnergyClosure
import AndersonAC.S78.CommittedAssembly
import AndersonAC.S78FiniteForm.Proof
import AndersonAC.S78AnchorTail.Proof

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

theorem assembly_bridge_nonneg {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) :
    0 ≤ assemblyBridge I a f :=
  schur_ward_bridge_nonneg (I.state a.succ).active (I.state a.castSucc).active
    (I.nested a) _ _ f (fun i _ => I.positive.2.2.2.2.1.le.trans (I.damping i).1)

theorem assembly_global_split_nonneg {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (α v : Torus d m → ℝ) :
    0 ≤ assemblyGlobalSplit I α v :=
  add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg (inv_nonneg.mpr I.positive.2.2.1.le) (gradient_energy_nonneg _ _))

theorem assembly_prefix_split_overlap {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (S : Finset (Fin k)) (α v : Torus d m → ℝ) :
    (∑ a ∈ S, assemblyLocalSplit I a α v) ≤
      I.C * t ^ (-(d : ℝ) * nu d) * assemblyGlobalSplit I α v := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
    intro a _ _
    exact assembly_local_split_nonneg I a α v)).trans (assembly_split_overlap I α v)

theorem operation_energy_split {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) :
    operationEnergyError I a f =
      assemblyNearChange I a f + assemblySurvivorTail I a f - assemblyBridge I a f := by
  unfold operationEnergyError assemblySurvivorTail assemblyBridge
  ring

/-- This join is conditional only on the four pending analytic inputs.
Finite Schur/spatial forms, cube deviations and anchor tails are proved
dependencies. Earlier-prefix comparisons suffice for the near old factor. -/
theorem assemblyEnergyBounds_of_local_inputs (hmat : AssemblyMatrixBounds)
    (hcut : LocalCutoffInput) (htail : AssemblySurvivorTailBounds)
    (hbridge : AssemblyBridgeBounds) : AssemblyEnergyBounds := by
  intro d hd C c P hC hc hP
  obtain ⟨Cnear, hCnear, hnear⟩ := assembly_near_change_bound hcut d hd C hC
  obtain ⟨tT, htT, hT⟩ := htail assemblyAnchorTailInput_proof d hd C c P hC hc hP
  obtain ⟨Cbridge, tB, hCbridge, htB, hB⟩ :=
    hbridge hmat localDeviationInput_proof d hd C c P hC hc hP
  let K := (Cnear + Cbridge) * C
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨tS, htS, hS⟩ := assembly_error_smallness d hd (K / 2) (c / 2)
    (by positivity) (by positivity)
  obtain ⟨tR, htR, hR⟩ := reset_radius_small (0.10 * delta) (1 / 2)
    (by norm_num [delta]) (by norm_num)
  refine ⟨min tT (min tB (min tS tR)), lt_min htT (lt_min htB (lt_min htS htR)), ?_⟩
  intro m k t b r I hIC hIc hIP hsmall
  have ht := I.positive.1
  have ht1 := I.positive.2.1
  have hsmallT : t < tT := hsmall.trans_le (min_le_left _ _)
  have hsmallB : t < tB := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallS : t < tS := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallR : t < tR := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let ε := t ^ (0.10 * delta)
  have hε0 : 0 ≤ ε := Real.rpow_nonneg ht.le _
  have hεhalf : ε ≤ 1 / 2 := hR t ht hsmallR
  have hε1 : ε < 1 := by linarith
  have hcoeff : K * t ^ (0.125 * delta - (d : ℝ) * nu d) +
      2 * t ^ (0.2 * delta) ≤ (c / 2) * ε := by
    have h := hS t ht hsmallS
    dsimp only [ε]
    nlinarith
  change ∀ a f, |assemblyError I a f| ≤ ε * endpointEnergy (I.state 0) r t f
  apply assembly_error_induction I ε hε0
  intro a ha hprev f
  let S : Finset (Fin k) := Finset.univ.filter fun q => q.val < a.val
  have hpre : ∀ q ∈ S, ∀ F : Torus d m → ℝ,
      endpointEnergy (I.state q.castSucc) r t F ≤
        (2 * C) * spatialEnergy (nnGraph d m) (I.state 0).active b F := by
    intro q hq F
    have hqval : q.val < a.val := (Finset.mem_filter.mp hq).2
    have herrors : ∀ q' : Fin (k + 1), q'.val ≤ a.val - 1 → ∀ F',
        |assemblyError I q' F'| ≤ ε * endpointEnergy (I.state 0) r t F' := by
      intro q' hq' F'
      exact hprev q' (by omega) F'
    have h := assembly_pre_comparison_upto I spatialFormInput_proof finiteFormInput_proof
      (assembly_graph_connected I) ε hε0 hε1 (a.val - 1) herrors
      q.castSucc (by simp only [Fin.val_castSucc]; omega) F
    rw [hIC] at h
    have hW : 0 ≤ spatialEnergy (nnGraph d m) (I.state 0).active b F :=
      spatial_energy_nonneg _ _ b I.positive.2.2.1 F
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1 + ε ≤ 2) hCp.le) hW)
  have hCommon : ∀ α v : Torus d m → ℝ,
      (∀ i ∈ (I.state 0).active, f i = α i + v i) →
      |assemblyError I a f| ≤
        (K * t ^ (0.125 * delta - (d : ℝ) * nu d) + 2 * t ^ (0.2 * delta)) *
          assemblyGlobalSplit I α v := by
    intro α v hsplit
    let L := ∑ q ∈ S, assemblyLocalSplit I q α v
    let W := assemblyGlobalSplit I α v
    have hL : 0 ≤ L := Finset.sum_nonneg fun q hq => assembly_local_split_nonneg I q α v
    have hW : 0 ≤ W := assembly_global_split_nonneg I α v
    have hNear : |∑ q ∈ S, assemblyNearChange I q f| ≤ Cnear * t ^ (0.125 * delta) * L := by
      calc
        _ ≤ ∑ q ∈ S, |assemblyNearChange I q f| := by
          simpa only [Real.norm_eq_abs] using norm_sum_le S (fun q => assemblyNearChange I q f)
        _ ≤ ∑ q ∈ S, Cnear * t ^ (0.125 * delta) * assemblyLocalSplit I q α v :=
          Finset.sum_le_sum fun q hq => hnear m k t b r I hIC q (hpre q hq) f α v hsplit
        _ = _ := (Finset.mul_sum ..).symm
    have hTail : |∑ q ∈ S, assemblySurvivorTail I q f| ≤ t ^ (0.2 * delta) * W :=
      hT m k t b r I hIC hIc hIP hsmallT S f α v hsplit
    have hBridge : (∑ q ∈ S, assemblyBridge I q f) ≤
        Cbridge * t ^ (0.27 * delta) * L + t ^ (0.2 * delta) * W :=
      hB m k t b r I hIC hIc hIP hsmallB S f α v hsplit
    have hBridge0 : 0 ≤ ∑ q ∈ S, assemblyBridge I q f :=
      Finset.sum_nonneg fun q hq => assembly_bridge_nonneg I q f
    have hp : t ^ (0.27 * delta) ≤ t ^ (0.125 * delta) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num [delta])
    have hBridge' : (∑ q ∈ S, assemblyBridge I q f) ≤
        Cbridge * t ^ (0.125 * delta) * L + t ^ (0.2 * delta) * W :=
      hBridge.trans (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCbridge.le) hL) le_rfl)
    have hSplit : assemblyError I a f = (∑ q ∈ S, assemblyNearChange I q f) +
        (∑ q ∈ S, assemblySurvivorTail I q f) - (∑ q ∈ S, assemblyBridge I q f) := by
      unfold assemblyError
      change (∑ q ∈ S, operationEnergyError I q f) = _
      simp_rw [operation_energy_split, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hAbs : |assemblyError I a f| ≤
        |∑ q ∈ S, assemblyNearChange I q f| +
        |∑ q ∈ S, assemblySurvivorTail I q f| + (∑ q ∈ S, assemblyBridge I q f) := by
      rw [hSplit]
      calc
        _ ≤ |(∑ q ∈ S, assemblyNearChange I q f) + (∑ q ∈ S, assemblySurvivorTail I q f)| +
            |∑ q ∈ S, assemblyBridge I q f| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le ((∑ q ∈ S, assemblyNearChange I q f) +
              (∑ q ∈ S, assemblySurvivorTail I q f)) 0 (∑ q ∈ S, assemblyBridge I q f))
        _ ≤ _ := add_le_add (abs_add_le _ _) (by rw [abs_of_nonneg hBridge0])
    have hLocal : |assemblyError I a f| ≤
        (Cnear + Cbridge) * t ^ (0.125 * delta) * L + 2 * t ^ (0.2 * delta) * W := by
      linarith [hAbs, hNear, hTail, hBridge']
    have hOverlap : L ≤ C * t ^ (-(d : ℝ) * nu d) * W := by
      simpa only [hIC] using assembly_prefix_split_overlap I S α v
    calc
      _ ≤ (Cnear + Cbridge) * t ^ (0.125 * delta) * L + 2 * t ^ (0.2 * delta) * W := hLocal
      _ ≤ (Cnear + Cbridge) * t ^ (0.125 * delta) *
          (C * t ^ (-(d : ℝ) * nu d) * W) + 2 * t ^ (0.2 * delta) * W := by
        exact add_le_add (mul_le_mul_of_nonneg_left hOverlap (by positivity)) le_rfl
      _ = _ := by
        dsimp [K]
        rw [show 0.125 * delta - (d : ℝ) * nu d =
          0.125 * delta + (-(d : ℝ) * nu d) by ring, Real.rpow_add ht]
        ring
  have hBound := assembly_error_of_common_split I a
    (K * t ^ (0.125 * delta - (d : ℝ) * nu d) + 2 * t ^ (0.2 * delta))
    (by positivity) f hCommon
  rw [hIc] at hBound
  have hDivide : (K * t ^ (0.125 * delta - (d : ℝ) * nu d) +
      2 * t ^ (0.2 * delta)) / c ≤ ε / 2 := by
    apply (div_le_iff₀ hc).2
    nlinarith [hcoeff]
  exact hBound.trans (mul_le_mul_of_nonneg_right hDivide (assembly_energy_nonneg I 0 f))

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assemblyEnergyBounds_of_local_inputs
