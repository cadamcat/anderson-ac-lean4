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

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- Graph distance on the torus is symmetric. -/
theorem physicalDistance_comm (d m : ℕ) (x y : Torus d m) :
    physicalDistance d m x y = physicalDistance d m y x := by
  unfold physicalDistance
  rw [SimpleGraph.dist_comm]

/-- Anchor sums are bounded by full torus sums via distinctness. -/
theorem sum_anchor_le {d m k : ℕ} (z : Fin k → Torus d m) (S : Finset (Fin k))
    (F : Torus d m → ℝ) (hF : ∀ y, 0 ≤ F y) (hinj : Function.Injective z) :
    ∑ a ∈ S, F (z a) ≤ ∑ y, F y := by
  classical
  have hmap : ∑ a ∈ S, F (z a) = ∑ y ∈ S.image z, F y := by
    symm
    apply Finset.sum_image
    intro a _ b _ hab
    exact hinj hab
  rw [hmap]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro y _ _
  exact hF y

/-- Pure-analysis exponential absorption. -/
theorem exp_absorb (d : ℕ) (Epoly Cpoly K : ℝ) (hK : 0 < K) (hCp : 0 < Cpoly) :
    ∃ t₀, 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      Cpoly * t ^ Epoly * Real.exp (-K * t ^ (-7 - nu d)) ≤ t ^ (0.2 * delta) := by
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have hA : 0 < 7 + nu d := by linarith
  have hAne : (7 : ℝ) + nu d ≠ 0 := ne_of_gt hA
  have hsA : (7 + nu d) * ((0.2 * delta - Epoly) / (7 + nu d)) =
      0.2 * delta - Epoly :=
    mul_div_cancel₀ _ hAne
  have hexp0 : (-7 - nu d) * ((0.2 * delta - Epoly) / (7 + nu d)) =
      Epoly - 0.2 * delta := by
    have h1 : (-7 - nu d) = -(7 + nu d) := by ring
    rw [h1, neg_mul, hsA]
    ring
  have hY : Filter.Tendsto (fun t : ℝ => t⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have hX : Filter.Tendsto (fun t : ℝ => (t⁻¹) ^ (7 + nu d))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
    (tendsto_rpow_atTop hA).comp hY
  have hG : Filter.Tendsto
      (fun X : ℝ => X ^ ((0.2 * delta - Epoly) / (7 + nu d)) * Real.exp (-K * X))
      Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ K hK
  have hH : Filter.Tendsto
      (fun t : ℝ => (((t⁻¹) ^ (7 + nu d)) ^ ((0.2 * delta - Epoly) / (7 + nu d))) *
        Real.exp (-K * ((t⁻¹) ^ (7 + nu d))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    hG.comp hX
  have eA : ∀ t : ℝ, 0 ≤ t → (t⁻¹) ^ (7 + nu d) = t ^ (-7 - nu d) := by
    intro t ht0
    have h1 : (-(7 + nu d)) = -7 - nu d := by ring
    rw [Real.inv_rpow ht0, ← Real.rpow_neg ht0, h1]
  have hF : Filter.Tendsto
      (fun t : ℝ => (t ^ (Epoly - 0.2 * delta)) *
        Real.exp (-K * t ^ (-7 - nu d)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    apply Filter.Tendsto.congr' _ hH
    rw [eventuallyEq_nhdsWithin_iff]
    apply Filter.Eventually.of_forall
    intro t ht
    have ht0le : 0 ≤ t := (Set.mem_Ioi.mp ht).le
    show (((t⁻¹) ^ (7 + nu d)) ^ ((0.2 * delta - Epoly) / (7 + nu d))) *
        Real.exp (-K * ((t⁻¹) ^ (7 + nu d))) =
      (t ^ (Epoly - 0.2 * delta)) * Real.exp (-K * t ^ (-7 - nu d))
    rw [eA t ht0le, ← Real.rpow_mul ht0le, hexp0]
  have hCinv : 0 < (1 : ℝ) / Cpoly := one_div_pos.mpr hCp
  have hev1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (t ^ (Epoly - 0.2 * delta)) * Real.exp (-K * t ^ (-7 - nu d)) < 1 / Cpoly :=
    hF.eventually (Iio_mem_nhds hCinv)
  rw [eventually_nhdsWithin_iff] at hev1
  rw [Metric.eventually_nhds_iff_ball] at hev1
  obtain ⟨ε, hε, hball⟩ := hev1
  refine ⟨ε, hε, fun t ht0 htt => ?_⟩
  have hmem : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact htt
  have h2 := hball t hmem (Set.mem_Ioi.mpr ht0)
  have hsplit : Epoly = (Epoly - 0.2 * delta) + 0.2 * delta := by ring
  have hfin : Cpoly * t ^ Epoly * Real.exp (-K * t ^ (-7 - nu d)) =
      ((t ^ (Epoly - 0.2 * delta)) * Real.exp (-K * t ^ (-7 - nu d))) *
        (Cpoly * t ^ (0.2 * delta)) := by
    rw [hsplit, Real.rpow_add ht0]
    ring
  rw [hfin]
  calc ((t ^ (Epoly - 0.2 * delta)) * Real.exp (-K * t ^ (-7 - nu d))) *
        (Cpoly * t ^ (0.2 * delta))
      ≤ ((1 / Cpoly)) * (Cpoly * t ^ (0.2 * delta)) :=
        mul_le_mul_of_nonneg_right (le_of_lt h2) (by positivity)
    _ = t ^ (0.2 * delta) := by
        rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hCp), one_mul]

/-- Far weights with the uniform `Ds` factor extracted. -/
theorem far_weight_split {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C c : ℝ) (hC : 1 ≤ C) (hc : 0 < c)
    (hIC : I.C = C) (hIc : I.c = c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C)
    (a : Fin k) (i : Torus d m)
    (hi : i ∉ cube d m (I.anchor a) (100 * I.Ds)) :
    ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 ≤
      ((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hKw : 0 ≤ C ^ 5 * t ^ (-2 - heatExponent) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)
  have h1 := far_weight_le I C c hC hc hIC hIc ht ht1 hdamp a i hi
  have hD : 100 * I.Ds ≤ physicalDistance d m i (I.anchor a) :=
    (outside_cube_lower i (I.anchor a) _ hi).le
  have hDsnn : 0 ≤ I.Ds := le_trans (Real.rpow_nonneg ht.le _) I.scaleRadius.1
  have h2 := exp_extract hc ht hD hDsnn
  calc ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2
      ≤ (C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * physicalDistance d m i (I.anchor a)) := h1
    _ ≤ (C ^ 5 * t ^ (-2 - heatExponent)) *
        (Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) :=
        mul_le_mul_of_nonneg_left h2 hKw
    _ = ((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by ring

/-- Far `α` energy via moments over distinct anchors. -/
theorem term_alpha_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C c Cmom0 : ℝ) (hC : 1 ≤ C) (hc : 0 < c) (hM0 : 0 ≤ Cmom0)
    (hIC : I.C = C) (hIc : I.c = c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C)
    (hmom0 : ∀ x : Torus d m,
      (∑ y, Real.exp (-(c / 16) * t * physicalDistance d m x y) *
        physicalDistance d m x y ^ (0 : ℕ)) ≤
        Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))
    (S : Finset (Fin k)) (α : Torus d m → ℝ) :
    ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2 ≤
      ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
        (∑ i ∈ (I.state 0).active, (α i) ^ 2) := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hKwE0nn : 0 ≤ (C ^ 5 * t ^ (-2 - heatExponent)) *
      Real.exp (-(c / 8) * t * (50 * I.Ds)) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)) (Real.exp_pos _).le
  have hterm : ∀ a ∈ S, ∀ i ∈ (I.state a.succ).active.filter
      (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
      (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2 ≤
        (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by
    intro a _ i hi
    have hiQ : i ∉ cube d m (I.anchor a) (100 * I.Ds) :=
      (Finset.mem_filter.mp hi).2
    have hw := far_weight_split I C c hC hc hIC hIc ht ht1 hdamp a i hiQ
    calc (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2
        ≤ (((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds))) *
            Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) * (α i) ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ = (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by
          ring
  have hnn : ∀ a ∈ S, ∀ i ∈ (I.state 0).active, 0 ≤
      (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
        Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by
    intro a _ i _
    apply mul_nonneg _ (Real.exp_pos _).le
    apply mul_nonneg _ (sq_nonneg _)
    exact hKwE0nn
  have hext : ∀ a ∈ S,
      (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) ≤
      ∑ i ∈ (I.state 0).active, (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
        Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)) := by
    intro a ha
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i hi _ => hnn a ha i hi)
    exact (Finset.filter_subset _ _).trans (assembly_active_subset_initial I a.succ)
  have hinner : ∀ i ∈ (I.state 0).active,
      (∑ a ∈ S, Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) ≤
        Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)) := by
    intro i _
    have himg : (∑ a ∈ S, Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) =
        ∑ y ∈ S.image (I.anchor), Real.exp (-(c / 16) * t * physicalDistance d m i y) := by
      symm
      apply Finset.sum_image
      intro a _ b _ hab
      exact I.distinct hab
    have hconv : (∑ y, Real.exp (-(c / 16) * t * physicalDistance d m i y)) =
        ∑ y, Real.exp (-(c / 16) * t * physicalDistance d m i y) *
          physicalDistance d m i y ^ (0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [pow_zero, mul_one]
    calc (∑ a ∈ S, Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)))
        = ∑ y ∈ S.image (I.anchor),
          Real.exp (-(c / 16) * t * physicalDistance d m i y) := himg
      _ ≤ ∑ y, Real.exp (-(c / 16) * t * physicalDistance d m i y) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun y _ _ => (Real.exp_pos _).le)
      _ = ∑ y, Real.exp (-(c / 16) * t * physicalDistance d m i y) *
          physicalDistance d m i y ^ (0 : ℕ) := hconv
      _ ≤ Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)) := hmom0 i
  calc ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2
      ≤ ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun i hi => hterm a ha i hi
    _ ≤ ∑ a ∈ S, ∑ i ∈ (I.state 0).active,
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) :=
        Finset.sum_le_sum fun a ha => hext a ha
    _ = ∑ i ∈ (I.state 0).active, ∑ a ∈ S,
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) :=
        Finset.sum_comm
    _ = ∑ i ∈ (I.state 0).active,
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          (∑ a ∈ S, Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a)))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ (I.state 0).active,
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) * (α i) ^ 2) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left (hinner i hi) _
        apply mul_nonneg _ (sq_nonneg _)
        exact hKwE0nn
    _ = ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
        (∑ i ∈ (I.state 0).active, (α i) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Far translation energy via reindexing, distinct anchors and cube moments. -/
theorem term_trans_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C c Cmom2 : ℝ) (hC : 1 ≤ C) (hc : 0 < c) (hM2 : 0 ≤ Cmom2)
    (hIC : I.C = C) (hIc : I.c = c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C)
    (hmom2 : ∀ x : Torus d m,
      (∑ y, Real.exp (-(c / 16) * t * physicalDistance d m x y) *
        physicalDistance d m x y ^ (2 : ℕ)) ≤
        Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))
    (S : Finset (Fin k)) (v : Torus d m → ℝ) :
    ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2 ≤
      ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ))))) *
        gradientEnergy (nnGraph d m) v := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hKwE0nn : 0 ≤ (C ^ 5 * t ^ (-2 - heatExponent)) *
      Real.exp (-(c / 8) * t * (50 * I.Ds)) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)) (Real.exp_pos _).le
  have hterm : ∀ a ∈ S, ∀ i ∈ (I.state a.succ).active.filter
      (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
      (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
        (v i - v (I.anchor a)) ^ 2 ≤
        (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) *
          (v i - v (I.anchor a)) ^ 2 := by
    intro a _ i hi
    have hiQ : i ∉ cube d m (I.anchor a) (100 * I.Ds) :=
      (Finset.mem_filter.mp hi).2
    have hw := far_weight_split I C c hC hc hIC hIc ht ht1 hdamp a i hiQ
    exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
  have hextend : ∀ a ∈ S,
      (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) *
          (v i - v (I.anchor a)) ^ 2) ≤
      ∑ i, (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) *
        (v i - v (I.anchor a)) ^ 2 := by
    intro a _
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    apply mul_nonneg _ (sq_nonneg _)
    apply mul_nonneg _ (Real.exp_pos _).le
    exact hKwE0nn
  have hreidx : ∀ a ∈ S,
      (∑ i, (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) *
        (v i - v (I.anchor a)) ^ 2) =
      ∑ j, (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
        (v (j + I.anchor a) - v (I.anchor a)) ^ 2 := by
    intro a _
    have h1 : (∑ i, (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) *
        (v i - v (I.anchor a)) ^ 2) =
        ∑ j, (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t *
            physicalDistance d m ((Equiv.addRight (I.anchor a)) j) (I.anchor a))) *
          (v (((Equiv.addRight (I.anchor a)) j)) - v (I.anchor a)) ^ 2 :=
      (Equiv.sum_comp (Equiv.addRight (I.anchor a)) _).symm
    rw [h1]
    apply Finset.sum_congr rfl
    intro j _
    have hdj : physicalDistance d m (j + I.anchor a) (I.anchor a) =
        physicalDistance d m 0 j := by
      have h := dist_shift d m (I.anchor a) j 0
      rw [zero_add] at h
      rw [physicalDistance_comm d m j 0] at h
      exact h
    have eadd : ((Equiv.addRight (I.anchor a)) j) = j + I.anchor a := rfl
    rw [eadd]
    rw [hdj]
  have hperj : ∀ j : Torus d m,
      (∑ a ∈ S, (v (j + I.anchor a) - v (I.anchor a)) ^ 2) ≤
        physicalDistance d m 0 j ^ (2 : ℕ) * gradientEnergy (nnGraph d m) v := by
    intro j
    have himg : (∑ a ∈ S, (v (j + I.anchor a) - v (I.anchor a)) ^ 2) =
        ∑ z ∈ S.image (fun a => (I.anchor a : Torus d m)),
          (v (j + z) - v z) ^ 2 := by
      symm
      apply Finset.sum_image
      intro a _ b _ hab
      simp only at hab
      exact I.distinct hab
    rw [himg]
    have hsub : (∑ z ∈ S.image (fun a => (I.anchor a : Torus d m)),
        (v (j + z) - v z) ^ 2) ≤
        ∑ z, (v (j + z) - v z) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ => sq_nonneg _)
    have hcomm2 : (∑ z, (v (j + z) - v z) ^ 2) =
        ∑ z, (v (z + j) - v z) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [add_comm j z]
    calc (∑ z ∈ S.image (fun a => (I.anchor a : Torus d m)), (v (j + z) - v z) ^ 2)
        ≤ ∑ z, (v (j + z) - v z) ^ 2 := hsub
      _ = ∑ z, (v (z + j) - v z) ^ 2 := hcomm2
      _ ≤ physicalDistance d m 0 j ^ (2 : ℕ) * gradientEnergy (nnGraph d m) v :=
          translation_energy_proof d m v j
  calc ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2
      ≤ ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) *
          (v i - v (I.anchor a)) ^ 2) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun i hi => hterm a ha i hi
    _ ≤ ∑ a ∈ S, ∑ i,
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m i (I.anchor a))) *
          (v i - v (I.anchor a)) ^ 2) :=
        Finset.sum_le_sum fun a ha => hextend a ha
    _ = ∑ a ∈ S, ∑ j,
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
          (v (j + I.anchor a) - v (I.anchor a)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hreidx a ha
    _ = ∑ j, ∑ a ∈ S,
        ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
          (v (j + I.anchor a) - v (I.anchor a)) ^ 2) :=
        Finset.sum_comm
    _ = ∑ j, ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
        (∑ a ∈ S, (v (j + I.anchor a) - v (I.anchor a)) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ ≤ ∑ j, ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
        (physicalDistance d m 0 j ^ (2 : ℕ) * gradientEnergy (nnGraph d m) v)) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left (hperj j) _
        apply mul_nonneg _ (Real.exp_pos _).le
        exact hKwE0nn
    _ = ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (∑ j, Real.exp (-(c / 16) * t * physicalDistance d m 0 j) *
          physicalDistance d m 0 j ^ (2 : ℕ)))) *
        gradientEnergy (nnGraph d m) v := by
        have e1 : ∀ j : Torus d m,
            ((((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
              (physicalDistance d m 0 j ^ (2 : ℕ) * gradientEnergy (nnGraph d m) v)) =
            (((((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
              physicalDistance d m 0 j ^ (2 : ℕ))) *
              gradientEnergy (nnGraph d m) v := fun j => by ring
        have hfacK : (∑ j, ((((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
              physicalDistance d m 0 j ^ (2 : ℕ))) =
            ((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              (∑ j, Real.exp (-(c / 16) * t * physicalDistance d m 0 j) *
                physicalDistance d m 0 j ^ (2 : ℕ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        calc ∑ j, ((((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
              (physicalDistance d m 0 j ^ (2 : ℕ) * gradientEnergy (nnGraph d m) v))
            = ∑ j, (((((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
              physicalDistance d m 0 j ^ (2 : ℕ))) *
              gradientEnergy (nnGraph d m) v :=
              Finset.sum_congr rfl (fun j _ => e1 j)
          _ = (∑ j, ((((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              Real.exp (-(c / 16) * t * physicalDistance d m 0 j)) *
              physicalDistance d m 0 j ^ (2 : ℕ))) *
              gradientEnergy (nnGraph d m) v := by
              rw [← Finset.sum_mul]
          _ = ((((C ^ 5 * t ^ (-2 - heatExponent)) *
              Real.exp (-(c / 8) * t * (50 * I.Ds))) *
              (∑ j, Real.exp (-(c / 16) * t * physicalDistance d m 0 j) *
                physicalDistance d m 0 j ^ (2 : ℕ)))) *
              gradientEnergy (nnGraph d m) v := by
              rw [hfacK]
    _ ≤ ((((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds))) *
        (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ))))) *
        gradientEnergy (nnGraph d m) v := by
        apply mul_le_mul_of_nonneg_right _ (gradient_energy_nonneg _ _)
        apply mul_le_mul_of_nonneg_left _ hKwE0nn
        exact hmom2 0


end AndersonAC.S78BridgeEnergy
