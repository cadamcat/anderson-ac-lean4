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
import AndersonAC.S78BridgeEnergy.MainHelper

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.S78BridgeEnergy

open AndersonAC.S78 AndersonAC.SolS78

theorem assemblyBridgeBounds_proof : AssemblyBridgeBounds := by
  classical
  intro hM hD d hd C c P hC hc hP
  obtain ⟨Cmat, tmat, hCmat_pos, htmat_pos, hMbody⟩ := hM d hd C c P hC hc hP
  obtain ⟨Cdev, hCdev_pos, hDbody⟩ := hD d hd
  have hCdev_nn : 0 ≤ Cdev := hCdev_pos.le
  obtain ⟨Cmom0, hCmom0_pos, hmom0_all⟩ :=
    lattice_exponential_moments_proof d 0 (c / 16) (by positivity)
  obtain ⟨Cmom2, hCmom2_pos, hmom2_all⟩ :=
    lattice_exponential_moments_proof d 2 (c / 16) (by positivity)
  have hM0_nn : 0 ≤ Cmom0 := hCmom0_pos.le
  have hM2_nn : 0 ≤ Cmom2 := hCmom2_pos.le
  -- Near constant.
  set K1 : ℝ := C ^ 2 * Real.sqrt (0.8 * C) with hK1def
  set K2 : ℝ := C ^ 2 * ((C + Cmat) / c) * C with hK2def
  set K3 : ℝ := K1 ^ (1 / 3 : ℝ) * K2 ^ (2 / 3 : ℝ) with hK3def
  set Kmax : ℝ := max (C ^ 2 * Real.sqrt (0.8 * C)) (Cdev * K3) with hKmaxdef
  set C' : ℝ := 2 * Kmax with hC'def
  have hK1nn : 0 ≤ K1 := by positivity
  have hKmax_pos : 0 < Kmax := by
    rw [hKmaxdef]
    have h1 : 0 < C ^ 2 * Real.sqrt (0.8 * C) := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  have hC'_pos : 0 < C' := by rw [hC'def]; positivity
  -- Far absorption constants.
  have hKexp_pos : 0 < (c / 8) * 50 := by positivity
  set Ealpha : ℝ := -2 - heatExponent - (d : ℝ) with hEalpha
  set Etrans : ℝ := -2 - heatExponent - (d : ℝ) - 2 with hEtrans
  set Epoint : ℝ := -2 - heatExponent - (d : ℝ) + (-16 - 2 * nu d) + (-(d : ℝ) * nu d) with hEpoint
  have hCpolyA_pos : 0 < 9 * (C ^ 5 * Cmom0) := by positivity
  have hCpolyT_pos : 0 < 9 * (C ^ 5 * Cmom2) := by positivity
  have hCpolyP_pos : 0 < 9 * (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C)) := by positivity
  obtain ⟨tabsA, htabsA_pos, htabsA⟩ :=
    exp_absorb d Ealpha (9 * (C ^ 5 * Cmom0)) ((c / 8) * 50) hKexp_pos hCpolyA_pos
  obtain ⟨tabsT, htabsT_pos, htabsT⟩ :=
    exp_absorb d Etrans (9 * (C ^ 5 * Cmom2)) ((c / 8) * 50) hKexp_pos hCpolyT_pos
  obtain ⟨tabsP, htabsP_pos, htabsP⟩ :=
    exp_absorb d Epoint (9 * (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C)))
      ((c / 8) * 50) hKexp_pos hCpolyP_pos
  -- Overall radius.
  set t₀ : ℝ := min tmat (min tabsA (min tabsT (min tabsP 1))) with ht₀def
  have ht₀_pos : 0 < t₀ := by
    rw [ht₀def]
    exact lt_min htmat_pos (lt_min htabsA_pos (lt_min htabsT_pos (lt_min htabsP_pos (by norm_num))))
  refine ⟨C', t₀, hC'_pos, ht₀_pos, ?_⟩
  intro m k t b r I hIC hIc hIP hsmall S f α v hsplit
  have ht : 0 < t := I.positive.1
  have ht1 : t ≤ 1 := I.positive.2.1
  have hbpos : 0 < b := I.positive.2.2.1
  have hbt : b ≤ t := I.positive.2.2.2.1
  have hb1 : b ≤ 1 := hbt.trans ht1
  have hsmall_mat : t < tmat := hsmall.trans_le (min_le_left _ _)
  have hsmall_A : t < tabsA :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall_T : t < tabsT :=
    hsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall_P : t < tabsP :=
    hsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hMholds := hMbody m k t b r I hIC hIc hIP hsmall_mat
  -- Damping.
  have hdamp : ∀ j, 0 ≤ (r j).im ∧ (r j).im ≤ C := by
    intro j
    have h1 : I.c ≤ (r j).im := (I.damping j).1
    have h2 : (r j).im ≤ I.C := (I.damping j).2.1
    rw [hIc] at h1
    rw [hIC] at h2
    exact ⟨hc.le.trans h1, h2⟩
  have hlow : ∀ k2, c ≤ (r k2).im := fun k2 => hIc ▸ (I.damping k2).1
  -- Radii.
  have hR : 1 ≤ 100 * I.Ds := Ds_R_ge_one I ht ht1
  have hside : 4 * (100 * I.Ds) < (OAI.Anderson.sideLength m : ℝ) := by
    have h := I.embedded
    linarith
  -- Row-four from matrix bounds.
  have hrow : ∀ (a : Fin k) (i : Torus d m),
      rowFour (oldInv I a) i < 0.8 * t ^ (1 + delta) := by
    intro a i
    have h : rowFour (normalizedInverse (I.state a.castSucc) t) i <
        0.8 * t ^ (1 + delta) := ((hMholds a.castSucc).2.2 i).2
    simpa [oldInv] using h
  -- Symmetry.
  have hsymG : ∀ (a : Fin k) (i j : Torus d m),
      (I.state a.castSucc).g i j = (I.state a.castSucc).g j i := by
    intro a i j
    exact damped_endpoint_symmetric _ _ _ (I.physical _) i j
  -- Ward rows via lag.
  have hexp_nn : 0 ≤ 0.42 * delta - (d : ℝ) * nu d := lag_exp_nonneg hd
  have hCmat_nn : 0 ≤ Cmat := hCmat_pos.le
  have hlag_le : ∀ (a : Fin k) (i : Torus d m), i ∈ (I.state a.castSucc).active →
      ‖(I.state a.castSucc).g i i - r i‖ ≤ Cmat := by
    intro a i hi
    have h : ‖(I.state a.castSucc).g i i - r i‖ ≤
        Cmat * t ^ (0.42 * delta - (d : ℝ) * nu d) :=
      (hMholds a.castSucc).2.1 i hi
    have hpow_le : t ^ (0.42 * delta - (d : ℝ) * nu d) ≤ 1 :=
      Real.rpow_le_one ht.le ht1 hexp_nn
    calc ‖(I.state a.castSucc).g i i - r i‖ ≤ Cmat * t ^ (0.42 * delta - (d : ℝ) * nu d) := h
      _ ≤ Cmat * 1 := mul_le_mul_of_nonneg_left hpow_le hCmat_nn
      _ = Cmat := by ring
  have hsub_all : ∀ (a : Fin k) (j : {x : Torus d m // x ∈ (I.state a.castSucc).active}),
      rowTwo ((Real.sqrt t : ℂ) •
        (I.state a.castSucc).g.submatrix (fun i => (i.val : Torus d m))
          (fun i => (i.val : Torus d m))) j ≤ (C + Cmat) / c := by
    intro a j
    have hIm : ∀ i : {x : Torus d m // x ∈ (I.state a.castSucc).active},
        (((I.state a.castSucc).g.submatrix (fun i : {x // x ∈ (I.state a.castSucc).active} => (i.val : Torus d m))
          (fun i : {x // x ∈ (I.state a.castSucc).active} => (i.val : Torus d m))) i i).im ≤ C + Cmat := by
      intro i
      have hiA : (i.val : Torus d m) ∈ (I.state a.castSucc).active := i.property
      have hlag := hlag_le a i.val hiA
      have hri : (r i.val).im ≤ C := (hdamp _).2
      have h := lag_Im_le ((I.state a.castSucc).g i.val i.val) (r i.val) C Cmat
        (Cmat * t ^ (0.42 * delta - (d : ℝ) * nu d)) hri
        (by
          have h0 : ‖(I.state a.castSucc).g i.val i.val - r i.val‖ ≤
              Cmat * t ^ (0.42 * delta - (d : ℝ) * nu d) :=
            (hMholds a.castSucc).2.1 i.val hiA
          exact h0)
        (by
          have hpow_le : t ^ (0.42 * delta - (d : ℝ) * nu d) ≤ 1 :=
            Real.rpow_le_one ht.le ht1 hexp_nn
          calc Cmat * t ^ (0.42 * delta - (d : ℝ) * nu d) ≤ Cmat * 1 :=
                mul_le_mul_of_nonneg_left hpow_le hCmat_nn
            _ = Cmat := by ring)
      -- h : Im ≤ C + Cmat, but need submatrix diag form (definitionally equal)
      simpa using h
    exact subtype_rowTwo_bound (I.state a.castSucc) r t c (C + Cmat) ht hc hlow
      (I.physical _) hIm j
  -- Deviation input as expected by near/far.
  have hdevAll : ∀ (m' : ℕ) (z : Torus d m') (R Lmax Ltotal : ℝ) (l v' : Torus d m' → ℝ),
      1 ≤ R → 4 * R < (OAI.Anderson.sideLength m' : ℝ) → 0 ≤ Lmax → 0 ≤ Ltotal →
      (∀ i, 0 ≤ l i ∧ l i ≤ Lmax) → (∀ i, i ∉ cube d m' z R → l i = 0) →
      (∑ i, l i) ≤ Ltotal →
      (∑ i, l i * (v' i - localCubeMean d m' z R v') ^ 2 ≤
        Cdev * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
          cubeGradient d m' (cube d m' z (2 * R)) v' ∧
        (v' z - localCubeMean d m' z R v') ^ 2 ≤
          Cdev * R ^ 2 * cubeGradient d m' (cube d m' z (2 * R)) v') := by
    intro m' z R Lmax Ltotal l v' h1R hside' hLmax hLtotal hl hsupp hsum
    exact hDbody m' z R Lmax Ltotal l v' h1R hside' hLmax hLtotal hl hsupp hsum
  -- Moments at this m, t.
  have hmom0 : ∀ x : Torus d m,
      (∑ y, Real.exp (-(c / 16) * t * physicalDistance d m x y) *
        physicalDistance d m x y ^ (0 : ℕ)) ≤
        Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)) := by
    intro x
    exact hmom0_all m t ht ht1 x
  have hmom2 : ∀ x : Torus d m,
      (∑ y, Real.exp (-(c / 16) * t * physicalDistance d m x y) *
        physicalDistance d m x y ^ (2 : ℕ)) ≤
        Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)) := by
    intro x
    exact hmom2_all m t ht ht1 x
  have hmov : ∀ x, ((overlap (fun a => cube d m (I.anchor a) (200 * I.Ds)) x : ℕ) : ℝ) ≤
      C * t ^ (-(d : ℝ) * nu d) := by
    intro x
    have h := I.haloOverlap x
    rw [hIC] at h
    exact h
  -- Active succ subset initial for f split.
  have hf0 : ∀ (a : Fin k) (i : Torus d m), i ∈ (I.state a.succ).active →
      f i = α i + v i := by
    intro a i hi
    exact hsplit i (assembly_active_subset_initial I a.succ hi)
  have hfS : ∀ a ∈ S, ∀ i ∈ (I.state a.succ).active, f i = α i + v i := by
    intro a _ i hi
    exact hf0 a i hi
  -- Near sums.
  have hnear_sum : ∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) ≤
      C' * t ^ (0.27 * delta) * (∑ a ∈ S, assemblyLocalSplit I a α v) := by
    have hper : ∀ a ∈ S,
        (∑ i ∈ (I.state a.succ).active.filter
          (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
          ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
            (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) ≤
        C' * t ^ (0.27 * delta) * assemblyLocalSplit I a α v := by
      intro a ha
      have h := near_part_le I C c Cmat Cdev hC hc hCmat_pos hCdev_nn hIC hIc ht ht1
        hbpos hbt a f α v hsplit hdamp hR hside (hrow a) (hsymG a) (hsub_all a) hDbody
      -- h has constant (2 * max...) * t^... * local; need C' defeq
      simpa [hC'def, hK1def, hK2def, hK3def, hKmaxdef] using h
    calc ∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
          (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
          ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
            (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)
        ≤ ∑ a ∈ S, C' * t ^ (0.27 * delta) * assemblyLocalSplit I a α v :=
          Finset.sum_le_sum fun a ha => hper a ha
      _ = C' * t ^ (0.27 * delta) * (∑ a ∈ S, assemblyLocalSplit I a α v) := by
          rw [Finset.mul_sum]
  -- Far three sums via moments/translation/point.
  have hAlpha : ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2 ≤
      ((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))) *
        (∑ i ∈ (I.state 0).active, (α i) ^ 2) := by
    have h := term_alpha_le I C c Cmom0 hC hc hM0_nn hIC hIc ht ht1 hdamp hmom0 S α
    -- rearrange assoc to match
    calc ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2
        ≤ ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
          (∑ i ∈ (I.state 0).active, (α i) ^ 2) := h
      _ = _ := by ring
  have hTrans : ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2 ≤
      ((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))) *
        gradientEnergy (nnGraph d m) v := by
    have h := term_trans_le I C c Cmom2 hC hc hM2_nn hIC hIc ht ht1 hdamp hmom2 S v
    calc ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
            (v i - v (I.anchor a)) ^ 2
        ≤ ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds))) *
          (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ))))) *
          gradientEnergy (nnGraph d m) v := h
      _ = _ := by ring
  have hPoint : ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 ≤
      (C ^ 5 * t ^ (-2 - heatExponent) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
        (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))) *
        gradientEnergy (nnGraph d m) v := by
    exact term_point_le I C c Cdev Cmom0 hC hc hCdev_nn hM0_nn hIC hIc ht ht1 hdamp
      hmom0 hDbody hmov hR hside S v
  -- Bridge split into near + far per operation.
  have hbridge_each : ∀ a ∈ S, assemblyBridge I a f ≤
      (∑ i ∈ (I.state a.succ).active.filter
        (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) +
      (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
    intro a _
    have hle := bridge_trial_bound I a f (localCubeMean d m (I.anchor a) (100 * I.Ds) v)
    have hsplit_eq : (∑ i ∈ (I.state a.succ).active,
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) =
        (∑ i ∈ (I.state a.succ).active.filter
          (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
          ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
            (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) +
        (∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
            (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) := by
      have h := Finset.sum_filter_add_sum_filter_not
        (s := (I.state a.succ).active)
        (p := (· ∈ cube d m (I.anchor a) (100 * I.Ds)))
        (f := fun i => ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)
      simpa using h.symm
    rw [hsplit_eq] at hle
    exact hle
  have hsum_bridge : (∑ a ∈ S, assemblyBridge I a f) ≤
      (∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) +
      (∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) := by
    calc ∑ a ∈ S, assemblyBridge I a f
        ≤ ∑ a ∈ S, ((∑ i ∈ (I.state a.succ).active.filter
          (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
          ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
            (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) +
        (∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
            (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) :=
          Finset.sum_le_sum fun a ha => hbridge_each a ha
      _ = _ := by rw [Finset.sum_add_distrib]
  -- Far factored sums for three-term comparison.
  have hfar_factored : (∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) =
      ∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  -- Absorption to t^(0.2δ).
  have hexp_mono : Real.exp (-(c / 8) * t * (50 * I.Ds)) ≤
      Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) :=
    far_exp_le I c hc ht
  have hrpow_nn : ∀ e : ℝ, 0 ≤ t ^ e := fun e => Real.rpow_nonneg ht.le _
  have hglobal_nn : 0 ≤ assemblyGlobalSplit I α v :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (inv_nonneg.mpr hbpos.le) (gradient_energy_nonneg _ _))
  have halpha_glob : ∑ i ∈ (I.state 0).active, (α i) ^ 2 ≤ assemblyGlobalSplit I α v :=
    alpha_le_global I α v
  have hgrad_glob : gradientEnergy (nnGraph d m) v ≤ assemblyGlobalSplit I α v :=
    grad_le_global I hb1 α v
  -- Absorption to t^(0.2δ).
  have hexp_mono : Real.exp (-(c / 8) * t * (50 * I.Ds)) ≤
      Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) :=
    far_exp_le I c hc ht
  have hrpow_nn : ∀ e : ℝ, 0 ≤ t ^ e := fun e => Real.rpow_nonneg ht.le _
  have hglobal_nn : 0 ≤ assemblyGlobalSplit I α v :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (inv_nonneg.mpr hbpos.le) (gradient_energy_nonneg _ _))
  have halpha_glob : ∑ i ∈ (I.state 0).active, (α i) ^ 2 ≤ assemblyGlobalSplit I α v :=
    alpha_le_global I α v
  have hgrad_glob : gradientEnergy (nnGraph d m) v ≤ assemblyGlobalSplit I α v :=
    grad_le_global I hb1 α v
  -- Exponent identifications.
  have hEalpha_eq : t ^ (-2 - heatExponent) * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)) =
      t ^ Ealpha := by
    rw [hEalpha]
    have h0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
    rw [h0]
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hEtrans_eq : t ^ (-2 - heatExponent) * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)) =
      t ^ Etrans := by
    rw [hEtrans]
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hEpoint_eq : (t ^ (-2 - heatExponent) * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
      (t ^ (-16 - 2 * nu d) * t ^ (-(d : ℝ) * nu d)) = t ^ Epoint := by
    rw [hEpoint]
    have h0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
    rw [h0]
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  have hexp_nn : 0 ≤ Real.exp (-(c / 8) * t * (50 * I.Ds)) := (Real.exp_pos _).le
  have hexp2_nn : 0 ≤ Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) :=
    (Real.exp_pos _).le
  -- Nine-fold absorption for each far piece.
  have hAbsA : 9 * ((C ^ 5 * t ^ (-2 - heatExponent)) *
      Real.exp (-(c / 8) * t * (50 * I.Ds)) *
      (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))) ≤ t ^ (0.2 * delta) := by
    have h1 : 9 * ((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))) =
        (9 * (C ^ 5 * Cmom0)) * t ^ Ealpha *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) := by
      have he := hEalpha_eq
      calc 9 * ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))) =
          (9 * (C ^ 5 * Cmom0)) * (t ^ (-2 - heatExponent) * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) := by ring
        _ = _ := by rw [he]
    have h2 : (9 * (C ^ 5 * Cmom0)) * t ^ Ealpha *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) ≤
        (9 * (C ^ 5 * Cmom0)) * t ^ Ealpha *
          Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) :=
      mul_le_mul_of_nonneg_left hexp_mono (by positivity)
    have h3 := htabsA t ht hsmall_A
    -- htabsA : Cpoly * t^Ealpha * exp2 ≤ t^0.2δ, need assoc match
    have h3' : (9 * (C ^ 5 * Cmom0)) * t ^ Ealpha *
        Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) ≤ t ^ (0.2 * delta) := by
      have e : (9 * (C ^ 5 * Cmom0)) * t ^ Ealpha *
          Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) =
          9 * (C ^ 5 * Cmom0) * t ^ Ealpha *
            Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) := by ring
      rw [e] at h3 ⊢
      -- htabsA statement is Cpoly * t^E * exp ≤ ..., with Cpoly * t^E * exp parsed left-assoc?
      -- Convert via ring_nf if needed; here defeq by ring.
      have h3r : 9 * (C ^ 5 * Cmom0) * t ^ Ealpha *
          Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) ≤ t ^ (0.2 * delta) := by
        simpa only [mul_assoc] using h3
      exact h3r
    rw [h1]
    exact h2.trans h3'
  have hAbsT : 9 * ((C ^ 5 * t ^ (-2 - heatExponent)) *
      Real.exp (-(c / 8) * t * (50 * I.Ds)) *
      (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))) ≤ t ^ (0.2 * delta) := by
    have h1 : 9 * ((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))) =
        (9 * (C ^ 5 * Cmom2)) * t ^ Etrans *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) := by
      have he := hEtrans_eq
      calc 9 * ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))) =
          (9 * (C ^ 5 * Cmom2)) * (t ^ (-2 - heatExponent) * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ))) *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) := by ring
        _ = _ := by rw [he]
    -- Use same exp monotonicity and tabsT.
    have h2 : (9 * (C ^ 5 * Cmom2)) * t ^ Etrans *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) ≤
        (9 * (C ^ 5 * Cmom2)) * t ^ Etrans *
          Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) :=
      mul_le_mul_of_nonneg_left hexp_mono (by positivity)
    have h3 := htabsT t ht hsmall_T
    have h3' : (9 * (C ^ 5 * Cmom2)) * t ^ Etrans *
        Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) ≤ t ^ (0.2 * delta) := by
      simpa only [mul_assoc] using h3
    rw [h1]
    exact h2.trans h3'
  -- Point absorption (with extra polynomial factors).
  have hAbsP : 9 * ((C ^ 5 * t ^ (-2 - heatExponent)) *
      Real.exp (-(c / 8) * t * (50 * I.Ds)) *
      (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
      (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))) ≤
      t ^ (0.2 * delta) := by
    have hpoly_eq : (C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
        (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d))) =
        (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C)) * t ^ Epoint *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) := by
      have he := hEpoint_eq
      -- rewrite t powers via he, rest by ring with rpow atoms
      calc (C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
          (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))
          = (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C)) *
            ((t ^ (-2 - heatExponent) * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
              (t ^ (-16 - 2 * nu d) * t ^ (-(d : ℝ) * nu d))) *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) := by ring
        _ = (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C)) * t ^ Epoint *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) := by rw [he]
    have h1 : 9 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
        (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d))))) =
        (9 * (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C))) * t ^ Epoint *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) := by
      rw [hpoly_eq]
      ring
    have h2 : (9 * (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C))) * t ^ Epoint *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) ≤
        (9 * (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C))) * t ^ Epoint *
          Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) :=
      mul_le_mul_of_nonneg_left hexp_mono (by positivity)
    have h3 := htabsP t ht hsmall_P
    have h3' : (9 * (C ^ 5 * Cmom0 * (Cdev * ((100 * C) ^ 2) * C))) * t ^ Epoint *
        Real.exp (-((c / 8) * 50) * t ^ (-7 - nu d)) ≤ t ^ (0.2 * delta) := by
      simpa only [mul_assoc] using h3
    rw [h1]
    exact h2.trans h3'
  -- Far sums to global via 1/3 splits.
  have hfar_three := far_total_three I C hdamp S f α v hfS
  -- hfar_three : factored ≤ 3*Alpha + 3*Trans + 3*Point; keep factored form for now.
  -- hfar_three : far_factored ≤ 3*Alpha + 3*Trans + 3*Point
  -- Bound each of the three by (1/3) t^0.2δ * global.
  have hA_third : 3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) ≤
      (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
    have hle : (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) ≤
        ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))) *
          (∑ i ∈ (I.state 0).active, (α i) ^ 2) := by
      calc (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
            (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
            (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2)
          ≤ ((((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds))) *
            (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
            (∑ i ∈ (I.state 0).active, (α i) ^ 2) := by
            have h := hAlpha
            -- hAlpha has extra assoc; convert
            simpa only [mul_assoc] using h
        _ = _ := by ring
    have hKw_nn : 0 ≤ (C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) := by positivity
    have h3Kw : 3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) ≤ (1 / 3) * t ^ (0.2 * delta) := by
      have h9 := hAbsA
      -- hAbsA : 9*(Kw) ≤ t^..., so 3*Kw = (1/3)*(9*Kw) ≤ (1/3)*t^...
      have heq : 3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) =
          (1 / 3) * (9 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) *
            (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))))) := by ring
      rw [heq]
      have hle9 : 9 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) ≤ t ^ (0.2 * delta) := hAbsA
      calc (1 / 3) * (9 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) *
            (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))))
          ≤ (1 / 3) * t ^ (0.2 * delta) :=
            mul_le_mul_of_nonneg_left hle9 (by norm_num)
        _ = (1 / 3) * t ^ (0.2 * delta) := rfl
    calc 3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2)
        ≤ 3 * ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))))) *
          (∑ i ∈ (I.state 0).active, (α i) ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = (3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ)))))) *
          (∑ i ∈ (I.state 0).active, (α i) ^ 2) := by ring
      _ ≤ ((1 / 3) * t ^ (0.2 * delta)) *
          (∑ i ∈ (I.state 0).active, (α i) ^ 2) :=
          mul_le_mul_of_nonneg_right h3Kw (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ ≤ (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
          have h := mul_le_mul_of_nonneg_left halpha_glob (by positivity : (0:ℝ) ≤ (1/3) * t ^ (0.2*delta))
          calc ((1 / 3) * t ^ (0.2 * delta)) * (∑ i ∈ (I.state 0).active, (α i) ^ 2)
              ≤ (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := h
            _ = (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := rfl
  have hT_third : 3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v i - v (I.anchor a)) ^ 2) ≤
      (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
    have hle : (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
            (v i - v (I.anchor a)) ^ 2) ≤
        ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))) *
          gradientEnergy (nnGraph d m) v := by
      have h := hTrans
      simpa only [mul_assoc] using h
    have h3Kw : 3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ))))) ≤ (1 / 3) * t ^ (0.2 * delta) := by
      have h9 := hAbsT
      have heq : 3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ))))) =
          (1 / 3) * (9 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) *
            (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))))) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left h9 (by norm_num)
    calc 3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
            (v i - v (I.anchor a)) ^ 2)
        ≤ 3 * ((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ))))) *
          gradientEnergy (nnGraph d m) v) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = (3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom2 * t ^ (-(d : ℝ) - ((2 : ℕ) : ℝ)))))) *
          gradientEnergy (nnGraph d m) v := by ring
      _ ≤ ((1 / 3) * t ^ (0.2 * delta)) * gradientEnergy (nnGraph d m) v :=
          mul_le_mul_of_nonneg_right h3Kw (gradient_energy_nonneg _ _)
      _ ≤ (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
          have h := mul_le_mul_of_nonneg_left hgrad_glob (by positivity : (0:ℝ) ≤ (1/3) * t ^ (0.2*delta))
          simpa only [mul_assoc] using h
  have hP_third : 3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
          (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) ≤
      (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
    have hle : (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
            (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) ≤
        ((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
          (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))) *
          gradientEnergy (nnGraph d m) v := by
      have h := hPoint
      simpa only [mul_assoc] using h
    have h3Kw : 3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
        Real.exp (-(c / 8) * t * (50 * I.Ds)) *
        (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
        (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d))))) ≤
        (1 / 3) * t ^ (0.2 * delta) := by
      have h9 := hAbsP
      have heq : 3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
          (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d))))) =
          (1 / 3) * (9 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
            Real.exp (-(c / 8) * t * (50 * I.Ds)) *
            (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
            (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))))) := by
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left h9 (by norm_num)
    calc 3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
          (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
          (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
            (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)
        ≤ 3 * (((((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
          (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d))))) *
          gradientEnergy (nnGraph d m) v)) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = (3 * (((C ^ 5 * t ^ (-2 - heatExponent)) *
          Real.exp (-(c / 8) * t * (50 * I.Ds)) *
          (Cmom0 * t ^ (-(d : ℝ) - ((0 : ℕ) : ℝ))) *
          (Cdev * ((100 * C) ^ 2 * t ^ (-16 - 2 * nu d)) * (C * t ^ (-(d : ℝ) * nu d)))))) *
          gradientEnergy (nnGraph d m) v := by ring
      _ ≤ ((1 / 3) * t ^ (0.2 * delta)) * gradientEnergy (nnGraph d m) v :=
          mul_le_mul_of_nonneg_right h3Kw (gradient_energy_nonneg _ _)
      _ ≤ (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
          have h := mul_le_mul_of_nonneg_left hgrad_glob (by positivity : (0:ℝ) ≤ (1/3) * t ^ (0.2*delta))
          simpa only [mul_assoc] using h
  -- Combine far.
  have hfar_le : (∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) ≤
      t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
    rw [hfar_factored]
    calc (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
            (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
            (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
              (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)
        ≤ 3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
            (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
            (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) * (α i) ^ 2) +
          3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
            (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
            (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
              (v i - v (I.anchor a)) ^ 2) +
          3 * (∑ a ∈ S, ∑ i ∈ (I.state a.succ).active.filter
            (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
            (∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2) *
              (v (I.anchor a) - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2) :=
        hfar_three
      _ ≤ (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v +
          (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v +
          (1 / 3) * t ^ (0.2 * delta) * assemblyGlobalSplit I α v :=
          add_le_add (add_le_add hA_third hT_third) hP_third
      _ = t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by ring
  -- Final join.
  calc (∑ a ∈ S, assemblyBridge I a f)
      ≤ (∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∈ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) +
        (∑ a ∈ S, (∑ i ∈ (I.state a.succ).active.filter
        (· ∉ cube d m (I.anchor a) (100 * I.Ds)),
        ∑ x ∈ removedSet I a, (r i).im * (r x).im * ‖oldInv I a i x‖ ^ 2 *
          (f i - localCubeMean d m (I.anchor a) (100 * I.Ds) v) ^ 2)) := hsum_bridge
    _ ≤ C' * t ^ (0.27 * delta) * (∑ a ∈ S, assemblyLocalSplit I a α v) +
        t ^ (0.2 * delta) * assemblyGlobalSplit I α v := by
        exact add_le_add hnear_sum hfar_le

end AndersonAC.S78BridgeEnergy

namespace AndersonAC.SolS78

theorem assemblyBridgeBounds_proof : AssemblyBridgeBounds :=
  AndersonAC.S78BridgeEnergy.assemblyBridgeBounds_proof

end AndersonAC.SolS78
