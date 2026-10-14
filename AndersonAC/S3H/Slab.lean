import AndersonAC.S3.HelperStatements
import Mathlib

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace AndersonAC.S3

theorem slabSlice_proof : SlabSliceStatement := by
  unfold SlabSliceStatement
  intro n b j₀ S c w M hb hS hw hM hSlice
  have habs_pos : (0 : ℝ) < abs (b j₀) := abs_pos.mpr hb
  have habs_ne : abs (b j₀) ≠ 0 := ne_of_gt habs_pos
  have hbinv_nonneg : (0 : ℝ) ≤ (abs (b j₀))⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  have hbinv_eq : abs ((b j₀)⁻¹) = (abs (b j₀))⁻¹ := abs_inv (b j₀)
  -- linear forms
  let Lfun : (Fin n → ℝ) → ℝ := fun x' => ∑ i, b (j₀.succAbove i) * x' i
  have hLmeas : Measurable Lfun := by fun_prop
  let linfun : (Fin (n + 1) → ℝ) → ℝ := fun x => ∑ j, b j * x j
  have hlinmeas : Measurable linfun := by fun_prop
  have sum_insert (t : ℝ) (x' : Fin n → ℝ) :
      linfun (Fin.insertNth (α := fun _ => ℝ) j₀ t x')
        = b j₀ * t + Lfun x' := by
    show ∑ j, b j * (Fin.insertNth (α := fun _ => ℝ) j₀ t x' j)
      = b j₀ * t + ∑ i, b (j₀.succAbove i) * x' i
    have h := Fin.sum_univ_succAbove
      (fun j => b j * (Fin.insertNth (α := fun _ => ℝ) j₀ t x' j)) j₀
    rw [h]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  -- the slab set
  let Tset : Set (Fin (n + 1) → ℝ) :=
    {x | x ∈ S ∧ |linfun x - c| ≤ w}
  have hTdef : Tset = {x : Fin (n + 1) → ℝ | x ∈ S ∧ |∑ j, b j * x j - c| ≤ w} := rfl
  have hT : MeasurableSet Tset := by
    have hset : {x : Fin (n + 1) → ℝ | |linfun x - c| ≤ w}
        = linfun ⁻¹' (Set.Icc (c - w) (c + w)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
      rw [abs_le]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    have hTeq : Tset = S ∩ {x : Fin (n + 1) → ℝ | |linfun x - c| ≤ w} := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Tset]
    rw [hTeq, hset]
    exact hS.inter (measurableSet_Icc.preimage hlinmeas)
  -- goal in terms of Tset (linfun unfolds to the sum)
  have hgoal : volume {x : Fin (n + 1) → ℝ | x ∈ S ∧ |∑ j, b j * x j - c| ≤ w}
      = volume Tset := rfl
  rw [hgoal]
  -- the coordinate equiv
  let e : ((Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) j₀
  have hPres : MeasurePreserving (e : (Fin (n + 1) → ℝ) → ℝ × (Fin n → ℝ))
      volume volume :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) j₀
  have hPresSymm :
      MeasurePreserving (e.symm : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ))
        volume volume :=
    hPres.symm _
  have hInd : Measurable
      (Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)) :=
    Measurable.indicator measurable_const hT
  have hSInd : Measurable
      (S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)) :=
    Measurable.indicator measurable_const hS
  have hIccMeas : MeasurableSet (Set.Icc (c - w) (c + w) : Set ℝ) :=
    measurableSet_Icc
  have hIccInd : Measurable
      ((Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞)) :=
    Measurable.indicator measurable_const hIccMeas
  -- indicator of Tset splits as product
  have hind_eq (y : Fin (n + 1) → ℝ) :
      Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) y
        = S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) y
          * (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (linfun y) := by
    have hmem : (y ∈ Tset) ↔ (y ∈ S ∧ linfun y ∈ Set.Icc (c - w) (c + w)) := by
      constructor
      · rintro ⟨hyS, hyw⟩
        refine ⟨hyS, ?_⟩
        simp only [Set.mem_Icc]
        have hle := abs_le.mp hyw
        constructor <;> linarith
      · rintro ⟨hyS, hyI⟩
        simp only [Set.mem_Icc] at hyI
        refine ⟨hyS, ?_⟩
        rw [abs_le]
        constructor <;> linarith
    by_cases hyS : y ∈ S <;> by_cases hyI : linfun y ∈ Set.Icc (c - w) (c + w)
    · have hyT : y ∈ Tset := hmem.mpr ⟨hyS, hyI⟩
      simp only [Set.indicator_of_mem hyT, Set.indicator_of_mem hyS,
        Set.indicator_of_mem hyI, Pi.one_apply, one_mul]
    · have hyT : y ∉ Tset := fun h => hyI (hmem.mp h).2
      simp only [Set.indicator_of_notMem hyT, Set.indicator_of_notMem hyI,
        mul_zero]
    · have hyT : y ∉ Tset := fun h => hyS (hmem.mp h).1
      simp only [Set.indicator_of_notMem hyT, Set.indicator_of_notMem hyS,
        Set.indicator_of_mem hyI, Pi.one_apply, zero_mul]
    · have hyT : y ∉ Tset := fun h => hyS (hmem.mp h).1
      simp only [Set.indicator_of_notMem hyT, Set.indicator_of_notMem hyI,
        mul_zero]
  -- affine map and its lintegral
  have hmap (L : ℝ) : Measure.map (fun t : ℝ => b j₀ * t + L) volume
      = ENNReal.ofReal (abs ((b j₀)⁻¹)) • volume := by
    have h1 : (fun t : ℝ => b j₀ * t + L) = (· + L) ∘ (b j₀ * ·) := rfl
    rw [h1, ← Measure.map_map (measurable_add_const L) (measurable_const_mul (b j₀))]
    rw [Real.map_volume_mul_left hb]
    rw [Measure.map_smul _ (measurable_add_const L).aemeasurable]
    rw [MeasureTheory.map_add_right_eq_self volume L]
  have hlin_affine (x' : Fin n → ℝ) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
      ∫⁻ t, G (b j₀ * t + Lfun x') ∂volume
        = ENNReal.ofReal (abs ((b j₀)⁻¹)) * ∫⁻ τ, G τ ∂volume := by
    have hmeas : Measurable (fun t : ℝ => b j₀ * t + Lfun x') :=
      (measurable_const_mul (b j₀)).add_const (Lfun x')
    calc ∫⁻ t, G (b j₀ * t + Lfun x') ∂volume
        = ∫⁻ τ, G τ ∂Measure.map (fun t : ℝ => b j₀ * t + Lfun x') volume := by
          rw [lintegral_map hG hmeas]
      _ = ∫⁻ τ, G τ ∂(ENNReal.ofReal (abs ((b j₀)⁻¹)) • volume) := by rw [hmap]
      _ = ENNReal.ofReal (abs ((b j₀)⁻¹)) * ∫⁻ τ, G τ ∂volume := by
          rw [lintegral_smul_measure, smul_eq_mul]
  -- for fixed x', the slice-insert function in τ
  have hInsTau (x' : Fin n → ℝ) :
      Measurable (fun τ : ℝ =>
        Fin.insertNth (α := fun _ => ℝ) j₀ ((τ - Lfun x') / b j₀) x') := by
    have heq : (fun τ : ℝ =>
        Fin.insertNth (α := fun _ => ℝ) j₀ ((τ - Lfun x') / b j₀) x')
        = (fun τ : ℝ => e.symm (((τ - Lfun x') / b j₀), x')) := by
      funext τ; rfl
    rw [heq]
    exact e.symm.measurable.comp
      (((measurable_id.sub_const (Lfun x')).div_const (b j₀)).prodMk measurable_const)
  have hInsX (tau : ℝ) :
      Measurable (fun x' : Fin n → ℝ =>
        Fin.insertNth (α := fun _ => ℝ) j₀ ((tau - Lfun x') / b j₀) x') := by
    have heq : (fun x' : Fin n → ℝ =>
        Fin.insertNth (α := fun _ => ℝ) j₀ ((tau - Lfun x') / b j₀) x')
        = (fun x' : Fin n → ℝ => e.symm (((tau - Lfun x') / b j₀), x')) := by
      funext x'; rfl
    rw [heq]
    apply e.symm.measurable.comp
    apply Measurable.prodMk
    · apply Measurable.div_const
      apply Measurable.sub measurable_const
      exact hLmeas
    · exact measurable_id
  have hInsJoint :
      Measurable (fun p : (Fin n → ℝ) × ℝ =>
        Fin.insertNth (α := fun _ => ℝ) j₀ ((p.2 - Lfun p.1) / b j₀) p.1) := by
    have heq : (fun p : (Fin n → ℝ) × ℝ =>
        Fin.insertNth (α := fun _ => ℝ) j₀ ((p.2 - Lfun p.1) / b j₀) p.1)
        = (fun p : (Fin n → ℝ) × ℝ => e.symm (((p.2 - Lfun p.1) / b j₀), p.1)) := by
      funext p; rfl
    rw [heq]
    apply e.symm.measurable.comp
    apply Measurable.prodMk
    · apply Measurable.div_const
      apply Measurable.sub measurable_snd
      exact hLmeas.comp measurable_fst
    · exact measurable_fst
  -- G for fixed x'
  let Gfun : (Fin n → ℝ) → ℝ → ℝ≥0∞ := fun x' tau =>
    S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
        (Fin.insertNth (α := fun _ => ℝ) j₀ ((tau - Lfun x') / b j₀) x')
      * (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) tau
  have hGmeas (x' : Fin n → ℝ) : Measurable (Gfun x') := by
    apply Measurable.mul
    · exact hSInd.comp (hInsTau x')
    · exact hIccInd
  have hGjoint : Measurable (Function.uncurry Gfun) := by
    have heq : Function.uncurry Gfun
        = (fun p : (Fin n → ℝ) × ℝ =>
          S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
            (Fin.insertNth (α := fun _ => ℝ) j₀ ((p.2 - Lfun p.1) / b j₀) p.1)
          * (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) p.2) := by
      funext p
      obtain ⟨x', tau⟩ := p
      rfl
    rw [heq]
    apply Measurable.mul
    · exact hSInd.comp hInsJoint
    · exact hIccInd.comp measurable_snd
  -- pointwise identity: T-indicator at (t,x') equals Gfun x' at φ(t)
  have hpoint (x' : Fin n → ℝ) (t : ℝ) :
      Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀ t x')
        = Gfun x' (b j₀ * t + Lfun x') := by
    have hdiv : ((b j₀ * t + Lfun x' - Lfun x') / b j₀) = t := by
      field_simp
      ring
    show Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
        (Fin.insertNth (α := fun _ => ℝ) j₀ t x')
      = S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀
            ((b j₀ * t + Lfun x' - Lfun x') / b j₀) x')
        * (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞)
          (b j₀ * t + Lfun x')
    rw [hdiv]
    rw [hind_eq]
    rw [sum_insert]
  -- transport to double integral
  have hvol : volume Tset
      = ∫⁻ x' : (Fin n → ℝ), ∫⁻ t : ℝ,
        Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀ t x') ∂volume ∂volume := by
    have hvol0 : volume Tset
        = ∫⁻ y : ℝ × (Fin n → ℝ),
          Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) (e.symm y) ∂volume := by
      rw [hPresSymm.lintegral_comp hInd]
      rw [lintegral_indicator_one hT]
    rw [hvol0]
    have hmeas2 : AEMeasurable
        (fun y : ℝ × (Fin n → ℝ) =>
          Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) (e.symm y))
        (volume.prod volume) := by
      have hpr : (volume : Measure (ℝ × (Fin n → ℝ))) = volume.prod volume := rfl
      rw [hpr] at *
      exact (hInd.comp e.symm.measurable).aemeasurable
    have hprod : (volume : Measure (ℝ × (Fin n → ℝ))) = volume.prod volume := rfl
    rw [hprod, lintegral_prod_symm _ hmeas2]
    apply lintegral_congr_ae
    filter_upwards with x'
    apply lintegral_congr_ae
    filter_upwards with t
    have hrr : e.symm (t, x')
        = Fin.insertNth (α := fun _ => ℝ) j₀ t x' := rfl
    rw [hrr]
  -- inner affine substitution per x'
  have hinner (x' : Fin n → ℝ) :
      (∫⁻ t : ℝ, Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀ t x') ∂volume)
        = ENNReal.ofReal (abs ((b j₀)⁻¹)) * ∫⁻ tau : ℝ, Gfun x' tau ∂volume := by
    have heq : (fun t : ℝ => Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀ t x'))
        = (fun t : ℝ => Gfun x' (b j₀ * t + Lfun x')) := by
      funext t
      exact hpoint x' t
    rw [heq]
    exact hlin_affine x' (Gfun x') (hGmeas x')
  -- pull constant out of outer integral
  have hHmeas : Measurable (fun x' : Fin n → ℝ => ∫⁻ tau : ℝ, Gfun x' tau ∂volume) :=
    Measurable.lintegral_prod_right hGjoint
  have hvol2 : volume Tset
      = ENNReal.ofReal (abs ((b j₀)⁻¹))
        * (∫⁻ x' : (Fin n → ℝ), ∫⁻ tau : ℝ, Gfun x' tau ∂volume ∂volume) := by
    rw [hvol]
    have heqfun : (fun x' : Fin n → ℝ => ∫⁻ t : ℝ,
        Tset.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀ t x') ∂volume)
        = (fun x' : Fin n → ℝ => ENNReal.ofReal (abs ((b j₀)⁻¹))
          * ∫⁻ tau : ℝ, Gfun x' tau ∂volume) := by
      funext x'
      exact hinner x'
    rw [heqfun]
    rw [lintegral_const_mul _ hHmeas]
  -- swap integrals
  have hswap : (∫⁻ x' : (Fin n → ℝ), ∫⁻ tau : ℝ, Gfun x' tau ∂volume ∂volume)
      = ∫⁻ tau : ℝ, ∫⁻ x' : (Fin n → ℝ), Gfun x' tau ∂volume ∂volume := by
    exact lintegral_lintegral_swap hGjoint.aemeasurable
  -- bound inner x'-integral for fixed tau
  have hslice_vol (tau : ℝ) :
      (∫⁻ x' : (Fin n → ℝ),
        S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀ ((tau - Lfun x') / b j₀) x')
        ∂volume)
        ≤ ENNReal.ofReal M := by
    calc (∫⁻ x' : (Fin n → ℝ),
          S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
            (Fin.insertNth (α := fun _ => ℝ) j₀ ((tau - Lfun x') / b j₀) x')
          ∂volume)
        ≤ volume {x' : Fin n → ℝ |
          Fin.insertNth (α := fun _ => ℝ) j₀
            ((tau - ∑ i, b (j₀.succAbove i) * x' i) / b j₀) x' ∈ S} :=
          lintegral_indicator_one_le _
      _ ≤ ENNReal.ofReal M := hSlice tau
  have hbound_tau (tau : ℝ) :
      (∫⁻ x' : (Fin n → ℝ), Gfun x' tau ∂volume)
        ≤ (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) tau
          * ENNReal.ofReal M := by
    have hSmeas_tau : AEMeasurable
        (fun x' : Fin n → ℝ => S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
          (Fin.insertNth (α := fun _ => ℝ) j₀ ((tau - Lfun x') / b j₀) x'))
        volume :=
      (hSInd.comp (hInsX tau)).aemeasurable
    have heq : (fun x' : Fin n → ℝ => Gfun x' tau)
        = (fun x' : Fin n → ℝ =>
          (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) tau
          * S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞)
            (Fin.insertNth (α := fun _ => ℝ) j₀ ((tau - Lfun x') / b j₀) x')) := by
      funext x'
      show S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) _
          * (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) tau
        = (Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) tau
          * S.indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) _
      rw [mul_comm]
    rw [heq, lintegral_const_mul'' _ hSmeas_tau]
    exact mul_le_mul_right (hslice_vol tau) _
  -- integrate the tau bound over the interval
  have hIcc_vol : volume (Set.Icc (c - w) (c + w) : Set ℝ) = ENNReal.ofReal (2 * w) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hInt_bound :
      (∫⁻ tau : ℝ, ∫⁻ x' : (Fin n → ℝ), Gfun x' tau ∂volume ∂volume)
        ≤ ENNReal.ofReal M * ENNReal.ofReal (2 * w) := by
    calc (∫⁻ tau : ℝ, ∫⁻ x' : (Fin n → ℝ), Gfun x' tau ∂volume ∂volume)
        ≤ ∫⁻ tau : ℝ,
          ((Set.Icc (c - w) (c + w) : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) tau
            * ENNReal.ofReal M) ∂volume :=
          lintegral_mono (fun tau => hbound_tau tau)
      _ = ∫⁻ tau : ℝ,
          (Set.Icc (c - w) (c + w) : Set ℝ).indicator
            (fun _ => ENNReal.ofReal M) tau ∂volume := by
          apply lintegral_congr_ae
          filter_upwards with tau
          by_cases htau : tau ∈ Set.Icc (c - w) (c + w)
          · simp only [Set.indicator_of_mem htau, Pi.one_apply, one_mul]
          · simp only [Set.indicator_of_notMem htau, zero_mul]
      _ = ∫⁻ _ in Set.Icc (c - w) (c + w), ENNReal.ofReal M ∂volume :=
          lintegral_indicator hIccMeas _
      _ = ENNReal.ofReal M * volume (Set.Icc (c - w) (c + w)) :=
          setLIntegral_const _ _
      _ = ENNReal.ofReal M * ENNReal.ofReal (2 * w) := by rw [hIcc_vol]
  -- assemble
  have hvol_bound : volume Tset
      ≤ ENNReal.ofReal (abs ((b j₀)⁻¹)) * (ENNReal.ofReal M * ENNReal.ofReal (2 * w)) := by
    rw [hvol2, hswap]
    exact mul_le_mul_right hInt_bound _
  -- convert RHS to ofReal (2 * w * M / |b j₀|)
  have hRHS : ENNReal.ofReal (abs ((b j₀)⁻¹)) * (ENNReal.ofReal M * ENNReal.ofReal (2 * w))
      = ENNReal.ofReal (2 * w * M / abs (b j₀)) := by
    rw [hbinv_eq]
    have h1 : (0 : ℝ) ≤ (abs (b j₀))⁻¹ := hbinv_nonneg
    have h2 : ENNReal.ofReal ((abs (b j₀))⁻¹ * (M * (2 * w)))
        = ENNReal.ofReal ((abs (b j₀))⁻¹) * ENNReal.ofReal (M * (2 * w)) :=
      ENNReal.ofReal_mul h1
    have h3 : ENNReal.ofReal (M * (2 * w))
        = ENNReal.ofReal M * ENNReal.ofReal (2 * w) :=
      ENNReal.ofReal_mul hM
    have h4 : (abs (b j₀))⁻¹ * (M * (2 * w)) = 2 * w * M / abs (b j₀) := by
      rw [div_eq_mul_inv]
      ring
    rw [← h3, ← h2, h4]
  rw [hRHS] at hvol_bound
  exact hvol_bound

end AndersonAC.S3
