import AndersonAC.S78SurvivorTail.Sum
import AndersonAC.S78.ExponentialTail

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace AndersonAC.S78SurvivorTail
open AndersonAC.S78
open AndersonAC.SolS78

/-- Inverse square root as an rpow. -/
theorem div_sqrt_eq_rpow {t C : ℝ} (ht : 0 < t) :
    C / Real.sqrt t = C * t ^ (-(1 / 2 : ℝ)) := by
  have hsqrt : Real.sqrt t = t ^ ((1 / 2 : ℝ)) := Real.sqrt_eq_rpow t
  rw [hsqrt, div_eq_mul_inv, ← Real.rpow_neg ht.le]

/-- Halo radius is positive. -/
theorem Ds_pos {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (ht : 0 < t) :
    0 < I.Ds := by
  have hpow : (0 : ℝ) < t ^ (-8 - nu d) := Real.rpow_pos_of_pos ht _
  linarith [I.scaleRadius.1, hpow]

/-- Physical distance is nonnegative. -/
theorem dist_nonneg (d m : ℕ) (x y : Torus d m) :
    0 ≤ physicalDistance d m x y := by
  unfold physicalDistance
  exact_mod_cast Nat.zero_le ((nnGraph d m).dist x y)

/-- Far exponentials are at most one. -/
theorem exp_far_le_one {d m : ℕ} (c t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (x y : Torus d m) :
    Real.exp (-(c / 4) * t * (physicalDistance d m x y)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hnn : 0 ≤ physicalDistance d m x y := dist_nonneg _ _ _ _
  nlinarith [mul_nonneg (mul_nonneg hc.le ht.le) hnn]

/-- The survivor-tail contract: far survivor changes sum to t^(0.2 delta)
times the one global split. -/
theorem assemblySurvivorTailBounds_proof : AssemblySurvivorTailBounds := by
  classical
  intro hAnchor d hd C c P hC hc hP
  -- anchor envelope
  obtain ⟨P', tA, hP'nn, htApos, hAenv⟩ := hAnchor d hd C c P hC hc hP
  -- distinct-anchor sum
  obtain ⟨Canch, hCanchpos, hAnch0⟩ := anchored_exponential_sum d (c / 4) (by positivity)
  -- global split energy
  obtain ⟨Csplit, hCsplitpos, hSplit0⟩ := exponential_split_energy d (c / 8) (by positivity)
  -- absorption parameters
  have hnu_nn : 0 ≤ nu d := by unfold nu delta; positivity
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  -- polynomial exponents for the two terms
  set P1 : ℝ := P' + 1 / 2 + (d : ℝ) + ((d : ℝ) + 2) with hP1
  set P2 : ℝ := P' + P' + (d : ℝ) + ((d : ℝ) + 2) with hP2
  set Ptot : ℝ := P1 + P2 with hPtot
  set Q : ℝ := 0.2 * delta + 1 with hQ
  have hP1nn : 0 ≤ P1 := by positivity
  have hP2nn : 0 ≤ P2 := by positivity
  have hPtotnn : 0 ≤ Ptot := by positivity
  obtain ⟨ttail, httailpos, htail⟩ :=
    assembly_exponential_tail (c / 4) Ptot Q 7 (by positivity) (by norm_num)
  -- constants for the two terms
  set K1 : ℝ := C ^ 3 * Canch * Csplit with hK1
  set K2 : ℝ := (C ^ 2 / 2) * Canch * Csplit with hK2
  have hK1nn : 0 ≤ K1 := by positivity
  have hK2nn : 0 ≤ K2 := by positivity
  have hKnn : 0 ≤ K1 + K2 := add_nonneg hK1nn hK2nn
  -- small-time threshold absorbing constants and ensuring t ≤ 1
  set t0 : ℝ := min tA (min ttail (min 1 (1 / (K1 + K2 + 1)))) with ht0
  have ht0pos : 0 < t0 := by
    simp only [ht0]
    exact lt_min htApos (lt_min httailpos (lt_min one_pos
      (one_div_pos.mpr (by positivity))))
  refine ⟨t0, ht0pos, ?_⟩
  intro m k t b r I hIC hIc hIP hlt S f α v hsplit
  -- basic positivity from the assembly input
  have ht : 0 < t := I.positive.1
  have ht1 : t ≤ 1 := I.positive.2.1
  have hbpos : 0 < b := I.positive.2.2.1
  have hbt : b ≤ t := I.positive.2.2.2.1
  have hb1 : b ≤ 1 := le_trans hbt ht1
  have ht0lt : t < t0 := hlt
  have htA : t < tA := lt_of_lt_of_le ht0lt (min_le_left _ _)
  have httail : t < ttail := lt_of_lt_of_le ht0lt
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht1' : t < 1 := lt_of_lt_of_le ht0lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htK : t < 1 / (K1 + K2 + 1) := lt_of_lt_of_le ht0lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have htKle : t ≤ 1 / (K1 + K2 + 1) := htK.le
  -- replace I-fields by the frozen parameters
  have hICh : I.C = C := hIC
  have hIch : I.c = c := hIc
  -- zero extension of alpha
  set αt : Torus d m → ℝ := fun i => if i ∈ (I.state 0).active then α i else 0 with hαt
  have hmass : (∑ i, (αt i) ^ 2) = ∑ i ∈ (I.state 0).active, (α i) ^ 2 := by
    have h := zeroExtend_mass I α
    simpa [hαt] using h
  have hmassα : (∑ i, (αt i) ^ 2) = ∑ i ∈ (I.state 0).active, (αt i) ^ 2 := by
    -- αt agrees with itself on active; use mass comparison via global split later
    have h2 : (∑ i, (αt i) ^ 2) = ∑ i ∈ (I.state 0).active, (α i) ^ 2 := hmass
    have h3 : ∑ i ∈ (I.state 0).active, (αt i) ^ 2 = ∑ i ∈ (I.state 0).active, (α i) ^ 2 :=
      Finset.sum_congr rfl (fun i hi => by simp [hαt, hi])
    rw [h2, ← h3]
  -- f agrees with αt+v on retained sites
  have hfv : ∀ i ∈ (I.state 0).active, f i = αt i + v i := by
    intro i hi
    rw [hsplit i hi]
    have hαi : αt i = α i := by simp [hαt, hi]
    rw [hαi]
  -- retained actives lie in the initial active set
  have hsub0 : ∀ a : Fin k, (I.state a.succ).active ⊆ (I.state 0).active := fun a =>
    assembly_active_subset_initial I a.succ
  -- exponential factors
  set E0 : ℝ := Real.exp (-(c / 4) * t * I.Ds) with hE0
  set rP : ℝ := t ^ (-P') with hrP
  have hDspos : 0 < I.Ds := Ds_pos I ht
  have hE0nn : 0 ≤ E0 := (Real.exp_pos _).le
  have hE0le : E0 ≤ 1 := by
    simp only [hE0]
    apply Real.exp_le_one_iff.mpr
    have h1 : 0 ≤ (c / 4) * t * I.Ds :=
      mul_nonneg (mul_nonneg (by positivity) ht.le) hDspos.le
    linarith
  have hrPnn : 0 ≤ rP := Real.rpow_nonneg ht.le _
  -- old crude bound with frozen C
  have hOldC : ∀ (a : Fin k) (i j : Torus d m),
      ‖normalizedInverse (I.state a.castSucc) t i j‖ ≤ C / Real.sqrt t := by
    intro a i j
    have h := old_entry_le I a i j ht
    rwa [hICh] at h
  -- D bound from the anchor envelope on far pairs
  have hDfar : ∀ (a : Fin k) (q : Torus d m × Torus d m),
      q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)) →
      ‖survivorDifference (I.state a.castSucc) (I.state a.succ) t q.1 q.2‖ ≤
        rP * E0 * Real.exp (-(c / 4) * t *
          (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) := by
    intro a q hq
    have hfar := far_outside_cube I a q hq
    have hD := hAenv m k t b r I hIC hIc hIP htA a q.1 q.2 hfar
    simpa [hrP, hE0] using hD
  -- per-pair exponential kernel bound
  have hCsqrt_nn : (0 : ℝ) ≤ C / Real.sqrt t :=
    div_nonneg (by linarith [hC]) (Real.sqrt_nonneg _)
  have hKpair : ∀ (a : Fin k) (q : Torus d m × Torus d m),
      q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)) →
      |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| ≤
        (2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) := by
    intro a q hq
    have hmem := (Finset.mem_sdiff.mp hq).1
    have hm := Finset.mem_product.mp hmem
    have hOld := hOldC a q.1 q.2
    have hD := hDfar a q hq
    have hE : Real.exp (-(c / 4) * t *
        (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have h1 : 0 ≤ physicalDistance d m q.1 (I.anchor a) := dist_nonneg _ _ _ _
      have h2 : 0 ≤ physicalDistance d m q.2 (I.anchor a) := dist_nonneg _ _ _ _
      have hct : 0 ≤ (c / 4) * t := mul_nonneg (by positivity) ht.le
      nlinarith [mul_nonneg hct (add_nonneg h1 h2)]
    have hEnn : (0 : ℝ) ≤ Real.exp (-(c / 4) * t *
        (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) :=
      (Real.exp_pos _).le
    have hker := pair_kernel_exp_le
      (normalizedInverse (I.state a.castSucc) t q.1 q.2)
      (survivorDifference (I.state a.castSucc) (I.state a.succ) t q.1 q.2)
      (C / Real.sqrt t) rP E0
      (Real.exp (-(c / 4) * t *
        (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))))
      hOld hD hCsqrt_nn hrPnn hE0nn hE0le hEnn hE
    have heq := new_eq_old_add_diff I a q.1 q.2 hm.1 hm.2
    -- rewrite new as old+D to match hker
    have hrewrite : (‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) =
        (‖normalizedInverse (I.state a.castSucc) t q.1 q.2 +
          survivorDifference (I.state a.castSucc) (I.state a.succ) t q.1 q.2‖ ^ 2 -
        ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2) := by
      rw [← heq]
    rw [hrewrite]
    -- hker bounds |‖old+D‖^2-‖old‖^2| by (2*Csqrt*rP+rP*rP)*E0*E; rearrange
    calc |‖normalizedInverse (I.state a.castSucc) t q.1 q.2 +
          survivorDifference (I.state a.castSucc) (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2|
        ≤ (2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) :=
        hker
      _ = _ := by ring
  -- f differences agree with the zero-extended split on retained sites
  have hFdiff : ∀ (a : Fin k) (q : Torus d m × Torus d m),
      q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)) →
      (f q.1 - f q.2) ^ 2 =
        (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2) := by
    intro a q hq
    have hmem := (Finset.mem_sdiff.mp hq).1
    have hm := Finset.mem_product.mp hmem
    have h1 : f q.1 = αt q.1 + v q.1 := hfv q.1 (hsub0 a hm.1)
    have h2 : f q.2 = αt q.2 + v q.2 := hfv q.2 (hsub0 a hm.2)
    rw [h1, h2]
  -- per-operation absolute bound with the common E0 factored out
  have hTailA : ∀ a : Fin k,
      |assemblySurvivorTail I a f| ≤ (C ^ 2 / 2) *
        ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
            (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) := by
    intro a
    have hbase := tail_abs_le I a f
    have hC2nn : (0 : ℝ) ≤ C ^ 2 / 2 := by positivity
    -- bound each far summand by the exponential form
    have hterm : ∀ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
        (assemblyNearSites I a).product (assemblyNearSites I a)),
        |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
          (f q.1 - f q.2) ^ 2 ≤
        ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) := by
      intro q hq
      have hK := hKpair a q hq
      have hF := hFdiff a q hq
      have hsq : (0 : ℝ) ≤ (f q.1 - f q.2) ^ 2 := sq_nonneg _
      have hsq2 : (0 : ℝ) ≤ (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2) := sq_nonneg _
      have hKnn : 0 ≤ |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
          ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| := abs_nonneg _
      calc |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
            (f q.1 - f q.2) ^ 2
          = |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2) := by rw [hF]
        _ ≤ ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
            Real.exp (-(c / 4) * t *
              (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a)))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2) :=
          mul_le_mul_of_nonneg_right hK hsq2
        _ = _ := by ring
    calc |assemblySurvivorTail I a f|
        ≤ (I.C ^ 2 / 2) * ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
          (assemblyNearSites I a).product (assemblyNearSites I a)),
          |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
            (f q.1 - f q.2) ^ 2 := hbase
      _ ≤ (C ^ 2 / 2) * ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
          (assemblyNearSites I a).product (assemblyNearSites I a)),
          |‖normalizedInverse (I.state a.succ) t q.1 q.2‖ ^ 2 -
            ‖normalizedInverse (I.state a.castSucc) t q.1 q.2‖ ^ 2| *
            (f q.1 - f q.2) ^ 2 := by rw [hICh]
      _ ≤ (C ^ 2 / 2) * ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
          (assemblyNearSites I a).product (assemblyNearSites I a)),
          ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
            Real.exp (-(c / 4) * t *
              (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
              (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq => hterm q hq) hC2nn
      _ = (C ^ 2 / 2) *
        ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
            (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
  -- anchor and split bounds instantiated at our t
  have hAnchBd : ∀ i j : Torus d m,
      (∑ a : Fin k, Real.exp (-(c / 4) * t *
        (physicalDistance d m i (I.anchor a) + physicalDistance d m j (I.anchor a)))) ≤
      Canch * t ^ (-(d : ℝ)) * Real.exp (-(c / 8) * t * physicalDistance d m i j) := by
    intro i j
    have h := hAnch0 m t ht ht1 (Fin k) (I.anchor) I.distinct i j
    have heq : (c / 4 / 2 : ℝ) = c / 8 := by ring
    simpa [heq] using h
  have hSplitBd : (∑ i, ∑ j, Real.exp (-(c / 8) * t * physicalDistance d m i j) *
        (((αt i + v i) - (αt j + v j)) ^ 2)) ≤
      Csplit * t ^ (-(d : ℝ) - 2) * ((∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v) :=
    hSplit0 m t ht ht1 αt v
  -- sum the per-operation bounds over the arbitrary prefix S
  have hSumAbs : |∑ a ∈ S, assemblySurvivorTail I a f| ≤
      ∑ a ∈ S, |assemblySurvivorTail I a f| := by
    simpa [Real.norm_eq_abs] using norm_sum_le S (fun a => assemblySurvivorTail I a f)
  have hPerA_le : ∀ a ∈ S, |assemblySurvivorTail I a f| ≤ (C ^ 2 / 2) *
      ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
        ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
          (assemblyNearSites I a).product (assemblyNearSites I a)),
        Real.exp (-(c / 4) * t *
          (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
          (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) :=
    fun a _ => hTailA a
  have hSumPerA : ∑ a ∈ S, |assemblySurvivorTail I a f| ≤
      (C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
        ∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
          (assemblyNearSites I a).product (assemblyNearSites I a)),
        Real.exp (-(c / 4) * t *
          (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
          (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) := by
    have hle : ∑ a ∈ S, |assemblySurvivorTail I a f| ≤
        ∑ a ∈ S, ((C ^ 2 / 2) *
          ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
            ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
              (assemblyNearSites I a).product (assemblyNearSites I a)),
            Real.exp (-(c / 4) * t *
              (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
              (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2))) :=
      Finset.sum_le_sum fun a ha => hPerA_le a ha
    have heq1 : (∑ a ∈ S, ((C ^ 2 / 2) *
          ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
            ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
              (assemblyNearSites I a).product (assemblyNearSites I a)),
            Real.exp (-(c / 4) * t *
              (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
              (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)))) =
        ∑ a ∈ S, (((C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0)) *
          ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
            (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) :=
      Finset.sum_congr rfl (fun a _ => by ring)
    have heq2 : (∑ a ∈ S, (((C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0)) *
          ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
            (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2))) =
        ((C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0)) *
          ∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
            (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    have heq3 : (((C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0)) *
          ∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
            (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) =
        (C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          ∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
            (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) := by ring
    exact hle.trans (by rw [heq1, heq2, heq3])
  -- far double sum through anchors and split energy
  have hFarSum := sum_far_exp_le I S αt v c Canch Csplit hAnchBd hSplitBd
    hCanchpos.le hCsplitpos.le ht
  -- mass+gradient controlled by the global split (zero extension)
  have hGlob : (∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v ≤
      assemblyGlobalSplit I α v := by
    have hle := mass_grad_le_globalSplit I αt v hbpos hb1 hmassα
    have heq : assemblyGlobalSplit I αt v = assemblyGlobalSplit I α v := by
      unfold assemblyGlobalSplit
      have hsum : ∑ i ∈ (I.state 0).active, (αt i) ^ 2 =
          ∑ i ∈ (I.state 0).active, (α i) ^ 2 :=
        Finset.sum_congr rfl (fun i hi => by simp [hαt, hi])
      rw [hsum]
    rw [heq] at hle
    exact hle
  have hGnn : 0 ≤ assemblyGlobalSplit I α v :=
    globalSplit_nonneg I α v hbpos
  have hmassE_nn : 0 ≤ (∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v :=
    add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (gradient_energy_nonneg _ _)
  -- combine per-operation, far-sum and global bounds
  have hCombine : |∑ a ∈ S, assemblySurvivorTail I a f| ≤
      (C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
        (Canch * t ^ (-(d : ℝ)) * (Csplit * t ^ (-(d : ℝ) - 2) *
          assemblyGlobalSplit I α v))) := by
    have h1 := hSumAbs.trans hSumPerA
    have hC2nn : (0 : ℝ) ≤ C ^ 2 / 2 := by positivity
    have hKnn : (0 : ℝ) ≤ (2 * (C / Real.sqrt t) * rP + rP * rP) * E0 := by positivity
    have hinner_le : (∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
          (assemblyNearSites I a).product (assemblyNearSites I a)),
          Real.exp (-(c / 4) * t *
            (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
            (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) ≤
        Canch * t ^ (-(d : ℝ)) * (Csplit * t ^ (-(d : ℝ) - 2) *
          assemblyGlobalSplit I α v) := by
      have h := hFarSum.trans
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGlob (mul_nonneg hCsplitpos.le (Real.rpow_nonneg ht.le _)))
          (mul_nonneg hCanchpos.le (Real.rpow_nonneg ht.le _)))
      -- hFarSum gives ≤ Canch*...*(Csplit*...*(mass+E)), need mass+E ≤ global
      -- rewrite associativity to match
      calc (∑ a ∈ S, ∑ q ∈ _, _)
          ≤ Canch * t ^ (-(d : ℝ)) * (Csplit * t ^ (-(d : ℝ) - 2) *
            ((∑ i, (αt i) ^ 2) + gradientEnergy (nnGraph d m) v)) := hFarSum
        _ ≤ Canch * t ^ (-(d : ℝ)) * (Csplit * t ^ (-(d : ℝ) - 2) *
            assemblyGlobalSplit I α v) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCanchpos.le (Real.rpow_nonneg ht.le _))
          apply mul_le_mul_of_nonneg_left hGlob (mul_nonneg hCsplitpos.le (Real.rpow_nonneg ht.le _))
    calc |∑ a ∈ S, assemblySurvivorTail I a f|
        ≤ (C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          ∑ a ∈ S, ∑ q ∈ _, _) := hSumAbs.trans hSumPerA
      _ ≤ (C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
          (Canch * t ^ (-(d : ℝ)) * (Csplit * t ^ (-(d : ℝ) - 2) *
            assemblyGlobalSplit I α v))) := by
          have hKinner : ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
              ∑ a ∈ S, ∑ q ∈ ((I.state a.succ).active.product (I.state a.succ).active \
                (assemblyNearSites I a).product (assemblyNearSites I a)),
              Real.exp (-(c / 4) * t *
                (physicalDistance d m q.1 (I.anchor a) + physicalDistance d m q.2 (I.anchor a))) *
                (((αt q.1 + v q.1) - (αt q.2 + v q.2)) ^ 2)) ≤
              ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0) *
              (Canch * t ^ (-(d : ℝ)) * (Csplit * t ^ (-(d : ℝ) - 2) *
                assemblyGlobalSplit I α v)) :=
            mul_le_mul_of_nonneg_left hinner_le hKnn
          exact mul_le_mul_of_nonneg_left hKinner hC2nn
  -- convert 1/sqrt and products to single rpow exponents
  have hSqrt : C / Real.sqrt t = C * t ^ (-(1 / 2 : ℝ)) := div_sqrt_eq_rpow ht
  have hrPeq : rP = t ^ (-P') := rfl
  have hr1 : t ^ (-(1 / 2 : ℝ)) * (t ^ (-P') * (t ^ (-(d : ℝ)) * t ^ (-(d : ℝ) - 2))) =
      t ^ (-P1) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    rw [hP1]
    ring
  have hr2 : t ^ (-P') * (t ^ (-P') * (t ^ (-(d : ℝ)) * t ^ (-(d : ℝ) - 2))) =
      t ^ (-P2) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    rw [hP2]
    ring
  -- halo radius dominates t^{-8} for the exponential tail input
  have hScale : t ^ (-8 - nu d) ≤ I.Ds := I.scaleRadius.1
  have h8le : t ^ (-8 : ℝ) ≤ t ^ (-8 - nu d) := by
    apply Real.rpow_le_rpow_of_exponent_ge ht ht1
    linarith [hnu_nn]
  have hRle : t ^ (-1 - 7 : ℝ) ≤ I.Ds := by
    have heq : (-1 - 7 : ℝ) = -8 := by norm_num
    rw [heq]
    exact le_trans h8le hScale
  have hTailBd : t ^ (-Ptot) * E0 ≤ t ^ Q := by
    have h := htail t I.Ds ht httail hRle
    simpa [hE0, hPtot, hQ] using h
  -- dominate both polynomial exponents by the total
  have hP1le : P1 ≤ Ptot := by rw [hPtot]; linarith [hP2nn]
  have hP2le : P2 ≤ Ptot := by rw [hPtot]; linarith [hP1nn]
  have hrP1le : t ^ (-P1) ≤ t ^ (-Ptot) := by
    apply Real.rpow_le_rpow_of_exponent_ge ht ht1
    linarith [hP1le]
  have hrP2le : t ^ (-P2) ≤ t ^ (-Ptot) := by
    apply Real.rpow_le_rpow_of_exponent_ge ht ht1
    linarith [hP2le]
  -- expand the combined coefficient into the two polynomial terms
  have hCoeff : (C ^ 2 / 2) * ((2 * (C / Real.sqrt t) * rP + rP * rP) * E0 *
      (Canch * t ^ (-(d : ℝ)) * (Csplit * t ^ (-(d : ℝ) - 2) *
        assemblyGlobalSplit I α v))) =
      (K1 * (t ^ (-P1) * E0) + K2 * (t ^ (-P2) * E0)) *
        assemblyGlobalSplit I α v := by
    rw [hSqrt, hrPeq, hK1, hK2]
    linear_combination (K1 * E0 * assemblyGlobalSplit I α v) * hr1 +
      (K2 * E0 * assemblyGlobalSplit I α v) * hr2
  -- absorb each polynomial-exponential product
  have hAbs1 : K1 * (t ^ (-P1) * E0) ≤ K1 * t ^ Q := by
    apply mul_le_mul_of_nonneg_left _ hK1nn
    calc t ^ (-P1) * E0 ≤ t ^ (-Ptot) * E0 :=
          mul_le_mul_of_nonneg_right hrP1le hE0nn
      _ ≤ t ^ Q := hTailBd
  have hAbs2 : K2 * (t ^ (-P2) * E0) ≤ K2 * t ^ Q := by
    apply mul_le_mul_of_nonneg_left _ hK2nn
    calc t ^ (-P2) * E0 ≤ t ^ (-Ptot) * E0 :=
          mul_le_mul_of_nonneg_right hrP2le hE0nn
      _ ≤ t ^ Q := hTailBd
  have hCoeffLe : (K1 * (t ^ (-P1) * E0) + K2 * (t ^ (-P2) * E0)) ≤ t ^ (0.2 * delta) := by
    have hQeq : t ^ Q = t * t ^ (0.2 * delta) := by
      rw [hQ, show (0.2 * delta + 1 : ℝ) = 1 + 0.2 * delta by ring,
        Real.rpow_add ht, Real.rpow_one]
    have hKt : (K1 + K2) * t ≤ 1 := by
      have hDpos : (0 : ℝ) < K1 + K2 + 1 := by positivity
      have hlt : t * (K1 + K2 + 1) < 1 := by
        rw [lt_div_iff₀ hDpos] at htK
        linarith [htK]
      nlinarith [hKnn, ht.le, hlt]
    calc (K1 * (t ^ (-P1) * E0) + K2 * (t ^ (-P2) * E0))
        ≤ K1 * t ^ Q + K2 * t ^ Q := add_le_add hAbs1 hAbs2
      _ = (K1 + K2) * t ^ Q := by ring
      _ = (K1 + K2) * (t * t ^ (0.2 * delta)) := by rw [hQeq]
      _ = ((K1 + K2) * t) * t ^ (0.2 * delta) := by ring
      _ ≤ 1 * t ^ (0.2 * delta) :=
          mul_le_mul_of_nonneg_right hKt (Real.rpow_nonneg ht.le _)
      _ = t ^ (0.2 * delta) := one_mul _
  -- final bound with the global split
  calc |∑ a ∈ S, assemblySurvivorTail I a f|
      ≤ (K1 * (t ^ (-P1) * E0) + K2 * (t ^ (-P2) * E0)) *
        assemblyGlobalSplit I α v := by
        rw [← hCoeff]
        exact hCombine
    _ ≤ t ^ (0.2 * delta) * assemblyGlobalSplit I α v :=
        mul_le_mul_of_nonneg_right hCoeffLe hGnn

end AndersonAC.S78SurvivorTail

/-- Exact requested name for the lead integration. -/
theorem AndersonAC.SolS78.assemblySurvivorTailBounds_proof :
    AndersonAC.SolS78.AssemblySurvivorTailBounds :=
  AndersonAC.S78SurvivorTail.assemblySurvivorTailBounds_proof
