import AndersonAC.S78.Definitions
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.EnergyInputs
import AndersonAC.S78.AssemblyForms
import AndersonAC.S78.NearEnergy
import AndersonAC.S78BridgeEnergy.Basic
import AndersonAC.S78BridgeEnergy.Near
import AndersonAC.S78BridgeEnergy.Weights

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

/-- Cubes are monotone in the radius for nonnegative radii. -/
theorem cube_mono_le {d m : ℕ} (z : Torus d m) {R R' : ℝ}
    (hR : 0 ≤ R) (hle : R ≤ R') : cube d m z R ⊆ cube d m z R' := by
  intro i hi
  simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro j
  exact (hi j).trans hle

/-- Per-operation near part of the Schur trial, bounded by the local split.
The near index set is `B ∩ cube(100·Ds)`; the mean is the cube mean of `v`.
`hdevAll` is the `LocalDeviationInput` body at this `d` for `Cdev`. -/
theorem near_part_le {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r)
    (C c Cmat Cdev : ℝ) (hC : 1 ≤ C) (hc : 0 < c) (hCmat : 0 < Cmat)
    (hCdev : 0 ≤ Cdev)
    (hIC : I.C = C) (hIc : I.c = c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hbpos : 0 < b) (hbt : b ≤ t)
    (a : Fin k) (f α v : Torus d m → ℝ)
    (hf : ∀ i ∈ (I.state 0).active, f i = α i + v i)
    (hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C)
    (hR : 1 ≤ 100 * I.Ds)
    (hside : 4 * (100 * I.Ds) < (OAI.Anderson.sideLength m : ℝ))
    (hrow : ∀ i, rowFour (oldInv I a) i < 0.8 * t ^ (1 + delta))
    (hsymG : ∀ i j, (I.state a.castSucc).g i j = (I.state a.castSucc).g j i)
    (hsub : ∀ j : {x : Torus d m // x ∈ (I.state a.castSucc).active},
      rowTwo ((Real.sqrt t : ℂ) •
        (I.state a.castSucc).g.submatrix (fun i => (i.val : Torus d m))
          (fun i => (i.val : Torus d m))) j ≤ (C + Cmat) / c)
    (hdevAll : ∀ (m : ℕ) (z : Torus d m) (R Lmax Ltotal : ℝ) (l v : Torus d m → ℝ),
      1 ≤ R → 4 * R < (OAI.Anderson.sideLength m : ℝ) → 0 ≤ Lmax → 0 ≤ Ltotal →
      (∀ i, 0 ≤ l i ∧ l i ≤ Lmax) → (∀ i, i ∉ cube d m z R → l i = 0) →
      (∑ i, l i) ≤ Ltotal →
      (∑ i, l i * (v i - localCubeMean d m z R v) ^ 2 ≤
        Cdev * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
          cubeGradient d m (cube d m z (2 * R)) v ∧
        (v z - localCubeMean d m z R v) ^ 2 ≤
          Cdev * R ^ 2 * cubeGradient d m (cube d m z (2 * R)) v)) :
    (∑ i ∈ (I.state a.succ).active.filter (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
      ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
        (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) ≤
      (2 * max (C ^ 2 * Real.sqrt (0.8 * C))
        (Cdev * ((C ^ 2 * Real.sqrt (0.8 * C)) ^ (1 / 3 : ℝ) *
          (C ^ 2 * ((C + Cmat) / c) * C) ^ (2 / 3 : ℝ)))) *
        t ^ (0.27 * delta) * assemblyLocalSplit I a α v := by
  classical
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  -- Rate constants.
  set K1 : ℝ := C ^ 2 * Real.sqrt (0.8 * C) with hK1def
  set K2 : ℝ := C ^ 2 * ((C + Cmat) / c) * C with hK2def
  set K3 : ℝ := K1 ^ (1 / 3 : ℝ) * K2 ^ (2 / 3 : ℝ) with hK3def
  set Kmax : ℝ := max (C ^ 2 * Real.sqrt (0.8 * C)) (Cdev * K3) with hKmaxdef
  have hK1nn : 0 ≤ K1 := by positivity
  have hRwnn : 0 ≤ (C + Cmat) / c := by positivity
  have hK2nn : 0 ≤ K2 := by positivity
  have hK3nn : 0 ≤ K3 := by positivity
  have hKmaxnn : 0 ≤ Kmax := by
    rw [hKmaxdef]
    exact le_trans (by positivity) (le_max_left _ _)
  -- Near index set and weights.
  set T : Finset (Torus d m) :=
    (I.state a.succ).active.filter (· ∈ cube d m (I.anchor a) (100 * I.Ds)) with hTdef
  set l : Torus d m → ℝ := fun i =>
    if i ∈ T then ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2
    else 0 with hldef
  have hTsubB : T ⊆ (I.state a.succ).active := Finset.filter_subset _ _
  have hl_nonneg : ∀ i, 0 ≤ l i := by
    intro i
    simp only [hldef]
    split_ifs with hi
    · apply Finset.sum_nonneg
      intro x _
      exact mul_nonneg (mul_nonneg (hdamp i).1 (hdamp x).1) (sq_nonneg _)
    · exact le_rfl
  have hLmax : ∀ i, l i ≤ K1 * t ^ (0.27 * delta) := by
    intro i
    simp only [hldef]
    split_ifs with hi
    · have h := Lmax_le I C hC hIC ht ht1 a i (hrow i) hdamp
      rw [hK1def]
      exact h
    · exact mul_nonneg hK1nn (Real.rpow_nonneg ht.le _)
  have hLtotal : (∑ i, l i) ≤ K2 * t ^ (-1 - heatExponent) := by
    have h1 : ∀ i ∈ T, l i =
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 := by
      intro i hi
      simp only [hldef, if_pos hi]
    have hsupp : (∑ i, l i) =
        ∑ i ∈ T, ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 := by
      calc (∑ i, l i) = ∑ i ∈ T, l i :=
            (Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by
              simp only [hldef, if_neg hi])).symm
        _ = _ := Finset.sum_congr rfl (fun i hi => h1 i hi)
    rw [hsupp]
    have htot := Ltotal_le I C ((C + Cmat) / c) hC hRwnn hIC ht a T hTsubB
      hdamp hsymG hsub
    have heq : K2 * t ^ (-1 - heatExponent) =
        C ^ 2 * ((C + Cmat) / c) * (C * t ^ (-1 - heatExponent)) := by
      rw [hK2def]; ring
    rw [heq]
    exact htot
  have hLmax_nn : 0 ≤ K1 * t ^ (0.27 * delta) :=
    mul_nonneg hK1nn (Real.rpow_nonneg ht.le _)
  have hLtotal_nn : 0 ≤ K2 * t ^ (-1 - heatExponent) :=
    mul_nonneg hK2nn (Real.rpow_nonneg ht.le _)
  have hlsupp : ∀ i, i ∉ cube d m (I.anchor a) (100 * I.Ds) → l i = 0 := by
    intro i hi
    have hnT : i ∉ T := fun hT => hi ((Finset.mem_filter.mp hT).2)
    simp only [hldef, if_neg hnT]
  have hlmem : ∀ i, 0 ≤ l i ∧ l i ≤ K1 * t ^ (0.27 * delta) :=
    fun i => ⟨hl_nonneg i, hLmax i⟩
  obtain ⟨hweighted, _hpoint⟩ := hdevAll m (I.anchor a) (100 * I.Ds)
    (K1 * t ^ (0.27 * delta)) (K2 * t ^ (-1 - heatExponent)) l v
    hR hside hLmax_nn hLtotal_nn hlmem hlsupp hLtotal
  have hnear := near_weight_estimate (I.anchor a) (100 * I.Ds)
    (K1 * t ^ (0.27 * delta)) (K2 * t ^ (-1 - heatExponent)) Cdev l α v T
    hl_nonneg (fun i => hLmax i)
    (fun i hi => by simp only [hldef]; rw [if_neg hi]) hweighted
  -- Identify the near bridge sum with the weighted form.
  have hA0 : ∀ i ∈ T, i ∈ (I.state 0).active := by
    intro i hi
    exact assembly_active_subset_initial I a.succ (hTsubB hi)
  have heqfil : (∑ i ∈ T, ∑ x ∈ removedSet I a, (r i).im * (r x).im *
        ‖oldInv I a i x‖ ^ 2 * (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) =
      ∑ i, l i * ((α i + v i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
    have hsupp2 : (∑ i, l i * ((α i + v i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) =
        ∑ i ∈ T, l i * ((α i + v i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro i _ hi
      have hli : l i = 0 := by simp only [hldef]; rw [if_neg hi]
      simp [hli]
    rw [hsupp2]
    apply Finset.sum_congr rfl
    intro i hi
    have hli : l i = ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 := by
      simp only [hldef]; rw [if_pos hi]
    rw [hli, hf i (hA0 i hi), Finset.sum_mul]
  rw [heqfil]
  -- Restrict the `α` sum to the local split cube.
  have h100 : (0 : ℝ) ≤ 100 * I.Ds := by
    have hpos : 0 < I.Ds := by
      have hle : 0 < t ^ (-8 - nu d) := Real.rpow_pos_of_pos ht _
      exact hle.trans_le I.scaleRadius.1
    positivity
  have hTsub : T ⊆ cube d m (I.anchor a) (2 * (100 * I.Ds)) ∩ (I.state 0).active := by
    intro i hi
    have hiQ : i ∈ cube d m (I.anchor a) (100 * I.Ds) := (Finset.mem_filter.mp hi).2
    exact Finset.mem_inter.mpr
      ⟨cube_mono_le _ h100 (by linarith) hiQ, hA0 i hi⟩
  have halpha_sub : (∑ i ∈ T, (α i) ^ 2) ≤
      ∑ i ∈ cube d m (I.anchor a) (2 * (100 * I.Ds)) ∩ (I.state 0).active, (α i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hTsub
    intro i _ _
    exact sq_nonneg _
  have hTnn : 0 ≤ ∑ i ∈ T, (α i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- Exponent comparison for the `b`-weighted term.
  have ha_exp : (0.27 : ℝ) * delta ≤
      1 + (0.27 * delta) * (1 / 3 : ℝ) + (-1 - heatExponent) * (2 / 3 : ℝ) := by
    simp only [heatExponent]
    norm_num [delta]
  have hK3le : (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
      (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) ≤ K3 * t ^ (0.27 * delta - 1) := by
    have e1 : (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) =
        K1 ^ (1 / 3 : ℝ) * t ^ ((0.27 * delta) * (1 / 3 : ℝ)) := by
      rw [Real.mul_rpow hK1nn (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
    have e2 : (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) =
        K2 ^ (2 / 3 : ℝ) * t ^ ((-1 - heatExponent) * (2 / 3 : ℝ)) := by
      rw [Real.mul_rpow hK2nn (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
    have e3 : t ^ ((0.27 * delta) * (1 / 3 : ℝ)) * t ^ ((-1 - heatExponent) * (2 / 3 : ℝ)) =
        t ^ ((0.27 * delta) * (1 / 3 : ℝ) + (-1 - heatExponent) * (2 / 3 : ℝ)) :=
      (Real.rpow_add ht _ _).symm
    have e4 : t ^ ((0.27 * delta) * (1 / 3 : ℝ) + (-1 - heatExponent) * (2 / 3 : ℝ)) ≤
        t ^ (0.27 * delta - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith [ha_exp])
    have e34 : t ^ ((0.27 * delta) * (1 / 3 : ℝ)) * t ^ ((-1 - heatExponent) * (2 / 3 : ℝ)) ≤
        t ^ (0.27 * delta - 1) := by
      rw [e3]
      exact e4
    calc (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
          (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ)
        = (K1 ^ (1 / 3 : ℝ) * K2 ^ (2 / 3 : ℝ)) *
          (t ^ ((0.27 * delta) * (1 / 3 : ℝ)) * t ^ ((-1 - heatExponent) * (2 / 3 : ℝ))) := by
          rw [e1, e2]; ring
      _ ≤ (K1 ^ (1 / 3 : ℝ) * K2 ^ (2 / 3 : ℝ)) * t ^ (0.27 * delta - 1) :=
          mul_le_mul_of_nonneg_left e34 (by positivity)
      _ = K3 * t ^ (0.27 * delta - 1) := by rw [hK3def]
  have hbT : b * ((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
      (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ)) ≤ K3 * t ^ (0.27 * delta) := by
    have hMnn : 0 ≤ (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) := by positivity
    have h1 : b * (((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ))) ≤
        t * (((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_right hbt hMnn
    have h2 : t * (((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ))) ≤ K3 * t ^ (0.27 * delta) := by
      have hmul : t * (((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
          (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ))) =
          (((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
            (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ)) * t ^ (1 : ℝ)) := by
        rw [Real.rpow_one]; ring
      rw [hmul]
      have hle : ((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
          (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ)) * t ^ (1 : ℝ) ≤
          (K3 * t ^ (0.27 * delta - 1)) * t ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_right hK3le (Real.rpow_nonneg ht.le _)
      have heq2 : (K3 * t ^ (0.27 * delta - 1)) * t ^ (1 : ℝ) = K3 * t ^ (0.27 * delta) := by
        have hpow : t ^ (0.27 * delta - 1) * t ^ (1 : ℝ) = t ^ (0.27 * delta) := by
          have hexp : (0.27 * delta - 1) + (1 : ℝ) = 0.27 * delta := by ring
          rw [← Real.rpow_add ht, hexp]
        calc (K3 * t ^ (0.27 * delta - 1)) * t ^ (1 : ℝ)
            = K3 * (t ^ (0.27 * delta - 1) * t ^ (1 : ℝ)) := by ring
          _ = _ := by rw [hpow]
      rw [heq2] at hle
      exact hle
    exact h1.trans h2
  -- Move `b` across: `M * grad = (b * M) * (b⁻¹ * grad)`.
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hG : 0 ≤ cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v :=
    cubeGradient_nonneg _ _ _ _
  have hmid : Cdev * (b * ((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
      (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ))) ≤
      (Cdev * K3) * t ^ (0.27 * delta) := by
    have h := mul_le_mul_of_nonneg_left hbT hCdev
    calc Cdev * (b * _) ≤ Cdev * (K3 * t ^ (0.27 * delta)) := h
      _ = (Cdev * K3) * t ^ (0.27 * delta) := by ring
  have hmul2 : Cdev * (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
      (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) *
      cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v ≤
      (Cdev * K3) * t ^ (0.27 * delta) *
        (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v) := by
    have hbase : Cdev * (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) *
        cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v =
        Cdev * (b * ((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
          (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ))) *
          (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v) := by
      have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hbne
      calc Cdev * (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
            (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) *
            cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v
          = (Cdev * ((K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
              (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ)) *
              cubeGradient d m (cube d m (I.anchor a) (2 * (100 * I.Ds))) v) *
              (b * b⁻¹) := by rw [hbb, mul_one]; ring
        _ = _ := by ring
    rw [hbase]
    exact mul_le_mul_of_nonneg_right hmid (mul_nonneg (inv_nonneg.mpr hbpos.le) hG)
  -- Put everything over the `200·Ds` cube.
  have hQR : (2 : ℝ) * (100 * I.Ds) = 200 * I.Ds := by ring
  rw [hQR] at hweighted hnear hmul2 hG halpha_sub
  have hA : 0 ≤ ∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hBnn : 0 ≤ b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v :=
    mul_nonneg (inv_nonneg.mpr hbpos.le) (cubeGradient_nonneg _ _ _ _)
  have hTnn : 0 ≤ ∑ i ∈ T, (α i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htpow : 0 ≤ t ^ (0.27 * delta) := Real.rpow_nonneg ht.le _
  have hWsplit : assemblyLocalSplit I a α v =
      (∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) +
        b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v := rfl
  have hstep1 : 2 * (K1 * t ^ (0.27 * delta)) * (∑ i ∈ T, (α i) ^ 2) ≤
      2 * Kmax * t ^ (0.27 * delta) *
        (∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) := by
    have hkle : K1 * t ^ (0.27 * delta) ≤ Kmax * t ^ (0.27 * delta) :=
      mul_le_mul_of_nonneg_right (by rw [hKmaxdef, hK1def]; exact le_max_left _ _) htpow
    calc 2 * (K1 * t ^ (0.27 * delta)) * (∑ i ∈ T, (α i) ^ 2)
        ≤ 2 * (K1 * t ^ (0.27 * delta)) *
          (∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) :=
          mul_le_mul_of_nonneg_left halpha_sub (by positivity)
      _ ≤ 2 * Kmax * t ^ (0.27 * delta) *
          (∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) := by
          have h2 : 2 * (K1 * t ^ (0.27 * delta)) ≤ 2 * (Kmax * t ^ (0.27 * delta)) :=
            mul_le_mul_of_nonneg_left hkle (by norm_num)
          calc 2 * (K1 * t ^ (0.27 * delta)) * _ ≤ 2 * (Kmax * t ^ (0.27 * delta)) * _ :=
                mul_le_mul_of_nonneg_right h2 hA
            _ = _ := by ring
  have hstep2 : 2 * (Cdev * (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) *
        cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) ≤
      2 * Kmax * t ^ (0.27 * delta) *
        (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) := by
    have hkle : (Cdev * K3) * t ^ (0.27 * delta) ≤ Kmax * t ^ (0.27 * delta) :=
      mul_le_mul_of_nonneg_right (by rw [hKmaxdef]; exact le_max_right _ _) htpow
    have h2 : Cdev * (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) *
        cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v ≤
        ((Cdev * K3) * t ^ (0.27 * delta)) *
          (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) :=
      hmul2
    have s1 : 2 * (Cdev * (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
        (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) *
        cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) ≤
        2 * (((Cdev * K3) * t ^ (0.27 * delta)) *
          (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v)) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have s2 : 2 * (((Cdev * K3) * t ^ (0.27 * delta)) *
        (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v)) ≤
        2 * Kmax * t ^ (0.27 * delta) *
          (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) := by
      have e : ((Cdev * K3) * t ^ (0.27 * delta)) *
          (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) ≤
          (Kmax * t ^ (0.27 * delta)) *
            (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) :=
        mul_le_mul_of_nonneg_right hkle hBnn
      calc 2 * _ ≤ 2 * _ := mul_le_mul_of_nonneg_left e (by norm_num)
        _ = _ := by ring
    exact s1.trans s2
  calc ∑ i, l i * ((α i + v i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)
      ≤ 2 * (K1 * t ^ (0.27 * delta)) * (∑ i ∈ T, (α i) ^ 2) +
        2 * (Cdev * (K1 * t ^ (0.27 * delta)) ^ (1 / 3 : ℝ) *
          (K2 * t ^ (-1 - heatExponent)) ^ (2 / 3 : ℝ) *
          cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) :=
        hnear
    _ ≤ 2 * Kmax * t ^ (0.27 * delta) *
          (∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) +
        2 * Kmax * t ^ (0.27 * delta) *
          (b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v) :=
        add_le_add hstep1 hstep2
    _ = (2 * Kmax) * t ^ (0.27 * delta) * assemblyLocalSplit I a α v := by
        rw [hWsplit]; ring

end AndersonAC.S78BridgeEnergy
