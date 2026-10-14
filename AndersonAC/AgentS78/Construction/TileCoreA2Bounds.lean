import AndersonAC.AgentS78.Construction.TileCoreA2Transfer

/-!
# WP10 C4a: A2 monitor bounds (`TileMonitorBoundsStatement2`)

At a running slot the included prefix `q` is valid; `prestate_and_forms_of_slotSeq` gives the
S45 prestate and the local-pullback comparisons of the current live state, so Proposition 4.8
(`AgentS45.ordinary_increment_estimates_proof`) gives the increment table. The monitored
increments of `tileEval` are fixed real-linear images (padding, dilation, compression,
pull-back) of the table's increments (`TileCoreA2Transfer`), which transfers mean, square and
jump bounds (05-local-sweeps.tex:795–842).
-/

open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw signValue binarySuffix)
open Matrix

/-! ## Product measures and a two-point law -/

section Analysis

theorem integral_pi_eval_a2 {L E : Type*} [Fintype L] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : L → Measure ℝ) [∀ v, IsProbabilityMeasure (ρ v)] (v : L) {f : ℝ → E}
    (hf : AEStronglyMeasurable f (ρ v)) :
    ∫ ω, f (ω v) ∂(Measure.pi ρ) = ∫ z, f z ∂(ρ v) := by
  have hmp := MeasureTheory.measurePreserving_eval (μ := ρ) v
  rw [← hmp.map_eq] at hf
  rw [← hmp.map_eq]
  exact (integral_map (measurable_pi_apply v).aemeasurable hf).symm

theorem momentLaw_pi_a2 {L : Type*} [Fintype L] (ρ : L → Measure ℝ)
    [∀ v, IsProbabilityMeasure (ρ v)] (v : L) {t c C : ℝ} (h : S45.MomentLaw (ρ v) t c id)
    (hcC : c ≤ C) : S45.MomentLaw (Measure.pi ρ) t C (fun ω => ω v) where
  measurable := measurable_pi_apply v
  mean := by
    rw [integral_pi_eval_a2 ρ v (f := fun z => z) measurable_id.aestronglyMeasurable]
    exact h.mean
  variance := by
    rw [integral_pi_eval_a2 ρ v (f := fun z => z ^ 2)
      (measurable_id.pow_const 2).aestronglyMeasurable]
    exact h.variance
  bounded := by
    have hmp := MeasureTheory.measurePreserving_eval (μ := ρ) v
    have hb : ∀ᵐ z ∂(Measure.map (Function.eval v) (Measure.pi ρ)), |z| ≤ C * Real.sqrt t := by
      rw [hmp.map_eq]
      filter_upwards [h.bounded] with z hz
      exact hz.trans (mul_le_mul_of_nonneg_right hcC (Real.sqrt_nonneg t))
    exact ae_of_ae_map (measurable_pi_apply v).aemeasurable hb

/-- The two-point law `±√t` with equal weights. -/
def twoPoint (t : ℝ) : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac (Real.sqrt t) + Measure.dirac (-Real.sqrt t))

instance twoPoint_isProb (t : ℝ) : IsProbabilityMeasure (twoPoint t) := by
  constructor
  rw [twoPoint, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero (by norm_num)

theorem integral_twoPoint (t : ℝ) (f : ℝ → ℝ) :
    ∫ z, f z ∂(twoPoint t) = 2⁻¹ * (f (Real.sqrt t) + f (-Real.sqrt t)) := by
  rw [twoPoint, integral_smul_measure,
    integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]

theorem momentLaw_twoPoint {t C : ℝ} (ht : 0 ≤ t) (hC : 1 ≤ C) :
    S45.MomentLaw (twoPoint t) t C id where
  measurable := measurable_id
  mean := by
    rw [integral_twoPoint]
    simp
  variance := by
    rw [integral_twoPoint]
    simp only [id, neg_sq, Real.sq_sqrt ht]
    ring
  bounded := by
    have hb : |Real.sqrt t| ≤ C * Real.sqrt t := by
      rw [abs_of_nonneg (Real.sqrt_nonneg t)]
      exact le_mul_of_one_le_left (Real.sqrt_nonneg t) hC
    have hb' : |-Real.sqrt t| ≤ C * Real.sqrt t := by rw [abs_neg]; exact hb
    refine Measure.ae_smul_measure ?_ _
    rw [ae_add_measure_iff]
    refine ⟨?_, ?_⟩
    · rw [ae_dirac_eq]; exact Filter.eventually_pure.mpr hb
    · rw [ae_dirac_eq]; exact Filter.eventually_pure.mpr hb'

/-- Means of fixed real-linear images of increments under a product law. -/
theorem mean_transfer_a2 {L E G : Type*} [Fintype L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (ρ : L → Measure ℝ) [∀ v, IsProbabilityMeasure (ρ v)] (S : Finset L)
    (F : L → ℝ → E) (hFm : ∀ v, AEStronglyMeasurable (F v) (ρ v))
    (Bd : ℝ) (hFb : ∀ v ∈ S, ∀ᵐ z ∂(ρ v), ‖F v z‖ ≤ Bd) (Φ : E →L[ℝ] G) :
    ∑ v ∈ S, ∫ z, Φ (F v z) ∂(ρ v) = Φ (∑ v ∈ S, ∫ ω, F v (ω v) ∂(Measure.pi ρ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [integral_pi_eval_a2 ρ v (hFm v)]
  exact ContinuousLinearMap.integral_comp_comm Φ (Integrable.of_bound (hFm v) Bd (hFb v hv))

/-- A real-linear map on a finite-dimensional space as a continuous linear map. -/
def clmOf_a2 {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : ℝ) a, f (c • a) = c • f a) :
    E →L[ℝ] G :=
  LinearMap.toContinuousLinearMap { toFun := f, map_add' := hadd, map_smul' := hsmul }

theorem clmOf_a2_apply {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : ℝ) a, f (c • a) = c • f a) (e : E) :
    clmOf_a2 f hadd hsmul e = f e := rfl

end Analysis

/-! ## Measurability of the single-deletion increments in the scalar -/

section IncMeas

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem constStateMeas_a2 (s : S45.State ι) : StateMeas (fun _ : ℝ => s) :=
  ⟨measurable_const, measurable_const⟩

theorem measurable_Jinc_a2 (t : ℝ) (s : S45.State ι) (x : ι) :
    Measurable fun z : ℝ => S45.Jinc t s x z :=
  (constStateMeas_a2 s).Jinc t x measurable_id

theorem measurable_Linc_a2 (t : ℝ) (s : S45.State ι) (x : ι) :
    Measurable fun z : ℝ => S45.Linc t s x z :=
  (constStateMeas_a2 s).Linc t x measurable_id

theorem measurable_pullback_Linc_a2 {H : Type*} [Fintype H] (t : ℝ) (s : S45.State ι) (x : ι)
    (B : Matrix ι H ℝ) : Measurable fun z : ℝ => S45.pullback B (S45.Linc t s x z) := by
  have hL := measurable_Linc_a2 t s x
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [S45.pullback, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun l _ => Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul hL.eval_matrix

theorem measurable_lagInc_a2 (t : ℝ) (s : S45.State ι) (x w : ι) :
    Measurable fun z : ℝ => S45.lagInc t s x z w := by
  unfold S45.lagInc
  by_cases hw : w ∈ S45.survivors x
  · simp only [dif_pos hw]
    have hc : Measurable fun z : ℝ => ((z : ℂ) + t * s.r x) :=
      (Complex.measurable_ofReal.comp measurable_id).add measurable_const
    have hs : StateMeas (fun z : ℝ => S45.deleteState t s x z) := by
      refine ⟨Measurable.of_eval_matrix _ fun i j => ?_, measurable_const⟩
      simp only [S45.deleteState]
      exact measurable_const.sub (((hc.mul measurable_const).mul measurable_const).div
        (measurable_const.add (hc.mul measurable_const)))
    exact (hs.lag_entry t ⟨w, hw⟩).sub measurable_const
  · simp only [dif_neg hw]
    exact measurable_const

theorem measurable_fourthProxy_a2 (t : ℝ) (s : S45.State ι) (cols : Finset ι) (w x : ι) :
    Measurable fun z : ℝ => S45.fourthProxy t s cols w x z := by
  unfold S45.fourthProxy
  by_cases h : w = x
  · simp only [if_pos h]
    exact measurable_const
  · simp only [if_neg h]
    have hg : Measurable fun z : ℝ => S45.gamma t s x z :=
      (constStateMeas_a2 s).gamma t x measurable_id
    refine Finset.measurable_sum _ fun j _ => Measurable.sub ?_ measurable_const
    exact (continuous_norm.measurable.comp
      (measurable_const.sub ((hg.mul measurable_const).mul measurable_const))).pow_const 4

end IncMeas

/-! ## The fixed real-linear monitor maps -/

section Maps

theorem padInto_smul_a2 {α : Type} [Fintype α] [DecidableEq α] (D : ℕ) (e : α → Fin D)
    (c : ℝ) (A : S45.CMat α) : padInto D e (c • A) = c • padInto D e A := by
  ext a b
  simp only [padInto, Matrix.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem scalarDilation_add_a2 (u w : ℂ) :
    scalarDilation (u + w) = scalarDilation u + scalarDilation w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarDilation]

theorem scalarDilation_smul_a2 (c : ℝ) (u : ℂ) :
    scalarDilation (c • u) = c • scalarDilation u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarDilation, Complex.real_smul]

theorem scalarBlock_add_a2 (a b : ℝ) : scalarBlock (a + b) = scalarBlock a + scalarBlock b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarBlock]

theorem scalarBlock_smul_a2 (c a : ℝ) : scalarBlock (c • a) = c • scalarBlock a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarBlock, Complex.real_smul]

theorem dilation_smul_a2 {P H : Type*} (c : ℝ) (B : Matrix P H ℂ) :
    S45.dilation (c • B) = c • S45.dilation B := by
  simp [S45.dilation, Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

theorem compressJ_smul_a2 {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (L : Finset (Port d m)) (c : ℝ) (A : S45.CMat L) :
    compressJ P j T L (c • A) = c • compressJ P j T L A := by
  ext a b
  simp only [compressJ, S45.restrict, Matrix.submatrix_apply, S45.pad, Matrix.smul_apply]
  split_ifs <;> simp

theorem map_ofReal_add_a2 {H : Type*} (X Y : S45.RMat H) :
    (X + Y).map (fun a : ℝ => (a : ℂ)) =
      X.map (fun a : ℝ => (a : ℂ)) + Y.map (fun a : ℝ => (a : ℂ)) := by
  ext a b
  simp

theorem map_ofReal_smul_a2 {H : Type*} (c : ℝ) (X : S45.RMat H) :
    (c • X).map (fun a : ℝ => (a : ℂ)) = c • X.map (fun a : ℝ => (a : ℂ)) := by
  ext a b
  simp [Complex.real_smul]

/-- Lag monitor map `c ↦ pad(scalarDilation c)`. -/
def ΦS_a2 (D : ℕ) (e : Fin 2 → Fin D) : ℂ →L[ℝ] S45.CMat (Fin D) :=
  clmOf_a2 (fun c => padInto D e (scalarDilation c))
    (fun a b => by rw [scalarDilation_add_a2, padInto_add])
    (fun c a => by rw [scalarDilation_smul_a2, padInto_smul_a2])

/-- Row monitor map `a ↦ pad(scalarBlock a)`. -/
def ΦR_a2 (D : ℕ) (e : Fin 2 → Fin D) : ℝ →L[ℝ] S45.CMat (Fin D) :=
  clmOf_a2 (fun a => padInto D e (scalarBlock a))
    (fun a b => by rw [scalarBlock_add_a2, padInto_add])
    (fun c a => by rw [scalarBlock_smul_a2, padInto_smul_a2])

/-- `J` monitor map `A ↦ pad(dilation(compress A))`. -/
def ΦJ_a2 {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (L : Finset (Port d m)) : S45.CMat L →L[ℝ] S45.CMat (Fin (monitorDim P j T)) :=
  clmOf_a2 (fun A => padInto _ (embJ P j T) (S45.dilation (compressJ P j T L A)))
    (fun a b => by rw [compressJ_add, dilation_add, padInto_add])
    (fun c a => by rw [compressJ_smul_a2, dilation_smul_a2, padInto_smul_a2])

/-- `L` monitor map `X ↦ pad(dilation(X))` on the real local coordinates. -/
def ΦL_a2 {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) :
    S45.RMat (Fin (localDim P j T)) →L[ℝ] S45.CMat (Fin (monitorDim P j T)) :=
  clmOf_a2 (fun X => padInto _ (embL P j T) (S45.dilation (X.map (fun a : ℝ => (a : ℂ)))))
    (fun a b => by rw [map_ofReal_add_a2, dilation_add, padInto_add])
    (fun c a => by rw [map_ofReal_smul_a2, dilation_smul_a2, padInto_smul_a2])

theorem ΦS_norm_le (D : ℕ) (e : Fin 2 → Fin D) (he : Function.Injective e) (c : ℂ) :
    ‖ΦS_a2 D e c‖ ≤ ‖c‖ := by
  change ‖padInto D e (scalarDilation c)‖ ≤ ‖c‖
  rw [padInto_norm D e he]
  exact scalarDilation_norm_le c

theorem ΦR_norm_le (D : ℕ) (e : Fin 2 → Fin D) (he : Function.Injective e) (a : ℝ) :
    ‖ΦR_a2 D e a‖ ≤ ‖a‖ := by
  change ‖padInto D e (scalarBlock a)‖ ≤ ‖a‖
  rw [padInto_norm D e he, Real.norm_eq_abs]
  exact scalarBlock_norm_le a

theorem ΦJ_norm_le {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (L : Finset (Port d m)) (A : S45.CMat L) : ‖ΦJ_a2 P j T L A‖ ≤ ‖A‖ := by
  change ‖padInto _ (embJ P j T) (S45.dilation (compressJ P j T L A))‖ ≤ ‖A‖
  rw [padInto_norm _ _ (embJ_injective P j T), dilation_norm]
  exact compressJ_norm_le P j T L A

theorem ΦL_norm_le {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (X : S45.RMat (Fin (localDim P j T))) : ‖ΦL_a2 P j T X‖ ≤ ‖X‖ := by
  change ‖padInto _ (embL P j T) (S45.dilation (X.map (fun a : ℝ => (a : ℂ))))‖ ≤ ‖X‖
  rw [padInto_norm _ _ (embL_injective P j T), dilation_norm]
  exact real_map_complex_norm_le X

theorem zero_le_one_cmat_a2 {ι : Type*} [Fintype ι] [DecidableEq ι] : (0 : S45.CMat ι) ≤ 1 := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact Matrix.PosSemidef.one

theorem sum_fromBlocks_a2 {ι P H : Type*} [Fintype P] [Fintype H] (S : Finset ι)
    (a : ι → S45.CMat P) (b : ι → S45.CMat H) :
    ∑ v ∈ S, Matrix.fromBlocks (a v) 0 0 (b v) =
      Matrix.fromBlocks (∑ v ∈ S, a v) 0 0 (∑ v ∈ S, b v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Matrix.fromBlocks_zero]
  | insert v S hv ih =>
    rw [Finset.sum_insert hv, Finset.sum_insert hv, Finset.sum_insert hv, ih,
      Matrix.fromBlocks_add]
    simp

/-- Stack bound for scalar monitors. -/
theorem stack_scalar_a2 {ι : Type} (S : Finset ι) (D : ℕ) (e : Fin 2 → Fin D)
    (he : Function.Injective e) (Mv : ι → S45.CMat (Fin 2)) (a : ι → ℝ)
    (hM : ∀ v ∈ S, (Mv v) ^ 2 ≤ a v • (1 : S45.CMat (Fin 2))) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∑ v ∈ S, a v ≤ R) :
    ∑ v ∈ S, (padInto D e (Mv v)) ^ 2 ≤ R • (1 : S45.CMat (Fin D)) := by
  have hsq : ∑ v ∈ S, (padInto D e (Mv v)) ^ 2 = padInto D e (∑ v ∈ S, (Mv v) ^ 2) := by
    rw [padInto_sum]
    exact Finset.sum_congr rfl fun v _ => padInto_sq D e he (Mv v)
  rw [hsq]
  refine padInto_le_smul_one D e he hR0 ?_
  refine (Finset.sum_le_sum hM).trans ?_
  rw [← Finset.sum_smul]
  exact smul_le_smul_of_nonneg_right hR zero_le_one_cmat_a2

/-- Stack bound for dilation monitors. -/
theorem stack_dil_a2 {ι P H : Type} [Fintype P] [DecidableEq P] [Fintype H] [DecidableEq H]
    (S : Finset ι) (D : ℕ) (e : P ⊕ H → Fin D) (he : Function.Injective e)
    (B : ι → Matrix P H ℂ) (R : ℝ) (hR0 : 0 ≤ R)
    (h1 : ∑ v ∈ S, B v * (B v)ᴴ ≤ R • (1 : S45.CMat P))
    (h2 : ∑ v ∈ S, (B v)ᴴ * B v ≤ R • (1 : S45.CMat H)) :
    ∑ v ∈ S, (padInto D e (S45.dilation (B v))) ^ 2 ≤ R • (1 : S45.CMat (Fin D)) := by
  have hsq : ∑ v ∈ S, (padInto D e (S45.dilation (B v))) ^ 2 =
      padInto D e (Matrix.fromBlocks (∑ v ∈ S, B v * (B v)ᴴ) 0 0 (∑ v ∈ S, (B v)ᴴ * B v)) := by
    rw [← sum_fromBlocks_a2, padInto_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [padInto_sq D e he, (AgentS45.dilation_square_proof (B v)).2.1]
  rw [hsq]
  exact padInto_le_smul_one D e he hR0 (fromBlocks_le_smul_one h1 h2)

end Maps

/-! ## Running slots: reindexing the unexposed sites by live bit ports -/

section Slot

variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
  (x : RunRecord d m)

open Classical in
/-- The live bit ports of the unexposed active sites. -/
def slotPorts_a2 (L : Finset (Port d m)) (rem : Finset (Fin (siteCount d m))) : Finset L :=
  Finset.univ.filter fun v : L => v.1.2 = false ∧ siteRank d m v.1.1 ∈ rem ∧ activeIn P j T x v.1.1

open Classical in
theorem mem_slotPorts_a2 (L : Finset (Port d m)) (rem : Finset (Fin (siteCount d m))) (v : L) :
    v ∈ slotPorts_a2 P j T x L rem ↔
      v.1.2 = false ∧ siteRank d m v.1.1 ∈ rem ∧ activeIn P j T x v.1.1 := by
  simp [slotPorts_a2]

open Classical in
theorem sum_slotPorts_a2 {β : Type*} [AddCommMonoid β] (L : Finset (Port d m))
    (rem : Finset (Fin (siteCount d m))) (f : Fin (siteCount d m) → β)
    (hf : ∀ y ∈ rem, ¬ (activeIn P j T x ((siteRank d m).symm y) ∧
      (((siteRank d m).symm y, false) : Port d m) ∈ L) → f y = 0) :
    ∑ y ∈ rem, f y = ∑ v ∈ slotPorts_a2 P j T x L rem, f (siteRank d m v.1.1) := by
  have hinj : Set.InjOn (fun v : L => siteRank d m v.1.1)
      (slotPorts_a2 P j T x L rem : Set L) := by
    intro v hv w hw hvw
    have hv' := (mem_slotPorts_a2 P j T x L rem v).mp hv
    have hw' := (mem_slotPorts_a2 P j T x L rem w).mp hw
    have h1 : v.1.1 = w.1.1 := (siteRank d m).injective hvw
    exact Subtype.ext (Prod.ext h1 (hv'.1.trans hw'.1.symm))
  have himg := Finset.sum_image (f := f) (s := slotPorts_a2 P j T x L rem)
    (g := fun v : L => siteRank d m v.1.1) hinj
  rw [← himg]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact ((mem_slotPorts_a2 P j T x L rem v).mp hv).2.1
  · intro y hy hny
    apply hf y hy
    rintro ⟨hact, hlive⟩
    apply hny
    refine Finset.mem_image.mpr ⟨⟨((siteRank d m).symm y, false), hlive⟩, ?_, ?_⟩
    · rw [mem_slotPorts_a2]
      exact ⟨rfl, by simpa using hy, hact⟩
    · simp

open Classical in
/-- Transfer of slot-port bounds to the unexposed sites. -/
theorem rem_transfer_a2 {D : ℕ} (L : Finset (Port d m)) (rem : Finset (Fin (siteCount d m)))
    (t Bm Bs Bj : ℝ) (hBs : 0 ≤ Bs) (hBj : 0 ≤ Bj)
    (ev : Fin (siteCount d m) → ℝ → S45.CMat (Fin D)) (G : L → ℝ → S45.CMat (Fin D))
    (hbad : ∀ y ∈ rem, ¬ (activeIn P j T x ((siteRank d m).symm y) ∧
      (((siteRank d m).symm y, false) : Port d m) ∈ L) → ∀ z, ev y z = 0)
    (hgood : ∀ v ∈ slotPorts_a2 P j T x L rem, ∀ z, ev (siteRank d m v.1.1) z = G v z)
    (hmeanS : ∀ ρ' : L → Measure ℝ, (∀ v, IsProbabilityMeasure (ρ' v)) →
      (∀ v ∈ slotPorts_a2 P j T x L rem, S45.MomentLaw (ρ' v) t 2 id) →
      ‖∑ v ∈ slotPorts_a2 P j T x L rem, ∫ z, G v z ∂(ρ' v)‖ ≤ Bm)
    (hstackS : ∀ z : L → ℝ, (∀ v ∈ slotPorts_a2 P j T x L rem, |z v| ≤ 2 * Real.sqrt t) →
      ∑ v ∈ slotPorts_a2 P j T x L rem, (G v (z v)) ^ 2 ≤ Bs • (1 : S45.CMat (Fin D)))
    (hjumpS : ∀ v ∈ slotPorts_a2 P j T x L rem, ∀ z, |z| ≤ 2 * Real.sqrt t → ‖G v z‖ ≤ Bj) :
    (∀ (ρ : Fin (siteCount d m) → Measure ℝ), (∀ y, IsProbabilityMeasure (ρ y)) →
      (∀ y ∈ rem, S45.MomentLaw (ρ y) t 2 id) →
      ‖∑ y ∈ rem, ∫ z, ev y z ∂(ρ y)‖ ≤ Bm) ∧
    (∀ z : Fin (siteCount d m) → ℝ, (∀ y ∈ rem, |z y| ≤ 2 * Real.sqrt t) →
      (∑ y ∈ rem, (ev y (z y)) ^ 2) ≤ Bs • (1 : S45.CMat (Fin D))) ∧
    (∀ y ∈ rem, ∀ z, |z| ≤ 2 * Real.sqrt t → ‖ev y z‖ ≤ Bj) := by
  refine ⟨fun ρ hρ hmom => ?_, fun z hz => ?_, fun y hy z hz => ?_⟩
  · rw [sum_slotPorts_a2 P j T x L rem (fun y => ∫ z, ev y z ∂(ρ y)) (fun y hy hn => by
      have h0 : (fun z => ev y z) = fun _ => 0 := funext (hbad y hy hn)
      simp only [h0, integral_zero])]
    have hS : ∑ v ∈ slotPorts_a2 P j T x L rem, ∫ z, ev (siteRank d m v.1.1) z ∂(ρ (siteRank d m v.1.1)) =
        ∑ v ∈ slotPorts_a2 P j T x L rem, ∫ z, G v z ∂(ρ (siteRank d m v.1.1)) :=
      Finset.sum_congr rfl fun v hv => integral_congr_ae (ae_of_all _ fun z => hgood v hv z)
    rw [hS]
    exact hmeanS (fun v => ρ (siteRank d m v.1.1)) (fun v => hρ _) (fun v hv =>
      hmom _ ((mem_slotPorts_a2 P j T x L rem v).mp hv).2.1)
  · rw [sum_slotPorts_a2 P j T x L rem (fun y => (ev y (z y)) ^ 2) (fun y hy hn => by
      simp only [hbad y hy hn, sq, mul_zero])]
    have hS : ∑ v ∈ slotPorts_a2 P j T x L rem, (ev (siteRank d m v.1.1) (z (siteRank d m v.1.1))) ^ 2 =
        ∑ v ∈ slotPorts_a2 P j T x L rem, (G v (z (siteRank d m v.1.1))) ^ 2 :=
      Finset.sum_congr rfl fun v hv => by rw [hgood v hv]
    rw [hS]
    exact hstackS (fun v => z (siteRank d m v.1.1)) (fun v hv =>
      hz _ ((mem_slotPorts_a2 P j T x L rem v).mp hv).2.1)
  · by_cases hg : activeIn P j T x ((siteRank d m).symm y) ∧
        (((siteRank d m).symm y, false) : Port d m) ∈ L
    · set v : L := ⟨((siteRank d m).symm y, false), hg.2⟩
      have hv : v ∈ slotPorts_a2 P j T x L rem := by
        rw [mem_slotPorts_a2]
        exact ⟨rfl, by simpa [v] using hy, hg.1⟩
      have hyv : siteRank d m v.1.1 = y := by simp [v]
      rw [← hyv, hgood v hv z]
      exact hjumpS v hv z hz
    · rw [hbad y hy hg z, norm_zero]
      exact hBj

open Classical in
theorem tileEval_slot_a2 (i : Fin (monitorCount P j T)) (k : ℕ)
    (ω : RandomSources (Torus d m) M) (q : S45.Sequence (Port d m))
    (hq : slotSeq P j T M x k ω = some q) (y : Fin (siteCount d m)) (z : ℝ) :
    tileEval P j T M x i k ω y z =
      if activeIn P j T x ((siteRank d m).symm y) ∧
          (((siteRank d m).symm y, false) : Port d m) ∈ (q.state q.length).live then
        stepMon P j T i x (candidate P j x q ((siteRank d m).symm y) z) q.length
      else 0 := by
  have h := tileEval_eq P j T M x i k ω ((siteRank d m).symm y) z
  rw [Equiv.apply_symm_apply, hq] at h
  simpa only [Option.getD_some] using h

theorem stepMon_form_a2 (i : Fin (monitorCount P j T)) (q : S45.Sequence (Port d m))
    (site : Torus d m) (z : ℝ) (hal2 : ((site, false) : Port d m) ∈ (q.state q.length).live)
    (htpos : 0 < sweepScale P.u m j) :
    stepMon P j T i x (candidate P j x q site z) q.length =
      monitorOf P j T i
        (fun u => if hu : u ∈ (q.state q.length).live then
          S45.lagInc (sweepScale P.u m j)
            ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
            ⟨(site, false), hal2⟩ z ⟨u, hu⟩ else 0)
        (fun u => if hu : u ∈ (q.state q.length).live then
          S45.fourthProxy (sweepScale P.u m j)
            ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
            (Finset.univ.filter (fun v : (q.state q.length).live =>
              v.1 ∈ (Finset.univ : Finset (Port d m))))
            ⟨u, hu⟩ ⟨(site, false), hal2⟩ z / S45.rowCap (sweepScale P.u m j) else 0)
        (fun u => if hu : u ∈ (q.state q.length).live then
          S45.fourthProxy (sweepScale P.u m j)
            ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
            (Finset.univ.filter (fun v : (q.state q.length).live =>
              v.1 ∈ (S45.reserves : Finset (Port d m))))
            ⟨u, hu⟩ ⟨(site, false), hal2⟩ z / S45.rowCap (sweepScale P.u m j) else 0)
        (S45.pad (q.state q.length).live (S45.Jinc (sweepScale P.u m j)
          ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) ⟨(site, false), hal2⟩ z))
        (S45.pad (q.state q.length).live (S45.Linc (sweepScale P.u m j)
          ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) ⟨(site, false), hal2⟩ z)) := by
  unfold stepMon
  congr 1
  · funext u
    exact candidate_stepLag_eq P j x q site z hal2 u
  · funext u
    exact candidate_stepRow_eq P j x q site z htpos hal2 _ u
  · funext u
    exact candidate_stepRow_eq P j x q site z htpos hal2 _ u
  · exact candidate_stepJ_eq P j x q site z hal2
  · exact candidate_stepL_eq P j x q site z hal2

end Slot

/-! ## Per-kind bounds on the live slot ports -/

section Kinds

variable {L : Type} [Fintype L] [DecidableEq L] {H : Type} [Fintype H] [DecidableEq H]

/-- The increment table, available for every probability law of the scalars. -/
def FTHyp_a2 (t C4 Cfam : ℝ) (sk : S45.State L) (S cols : Finset L) (B : Matrix L H ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : L → Ω → ℝ),
    (∀ v ∈ S, S45.MomentLaw μ t C4 (ξ v)) → S45.FamilyTable μ t C4 Cfam sk S cols B ξ

theorem FTHyp_two_a2 {t C4 Cfam : ℝ} {sk : S45.State L} {S cols : Finset L} {B : Matrix L H ℝ}
    (hFT : FTHyp_a2 t C4 Cfam sk S cols B) (ht : 0 < t) (hC4 : 2 ≤ C4) :
    S45.FamilyTable (Measure.pi fun _ : L => twoPoint t) t C4 Cfam sk S cols B
      (fun v ω => ω v) :=
  hFT (L → ℝ) _ _ fun v _ =>
    momentLaw_pi_a2 (fun _ : L => twoPoint t) v (momentLaw_twoPoint ht.le (by linarith)) le_rfl

theorem FTHyp_pi_a2 {t C4 Cfam : ℝ} {sk : S45.State L} {S cols : Finset L} {B : Matrix L H ℝ}
    (hFT : FTHyp_a2 t C4 Cfam sk S cols B) (hC4 : 2 ≤ C4) (ρ' : L → Measure ℝ)
    [∀ v, IsProbabilityMeasure (ρ' v)] (hmom : ∀ v ∈ S, S45.MomentLaw (ρ' v) t 2 id) :
    S45.FamilyTable (Measure.pi ρ') t C4 Cfam sk S cols B (fun v ω => ω v) :=
  hFT (L → ℝ) _ _ fun v hv => momentLaw_pi_a2 ρ' v (hmom v hv) hC4

theorem two_sqrt_le_a2 {t C4 : ℝ} (hC4 : 2 ≤ C4) : 2 * Real.sqrt t ≤ C4 * Real.sqrt t :=
  mul_le_mul_of_nonneg_right hC4 (Real.sqrt_nonneg t)

/-- Lag monitors at a live inner port `w`. -/
theorem lag_kind_a2 {t C4 Cfam : ℝ} {sk : S45.State L} {S cols : Finset L} {B : Matrix L H ℝ}
    (hFT : FTHyp_a2 t C4 Cfam sk S cols B) (ht : 0 < t) (ht1 : t ≤ 1) (hC4 : 2 ≤ C4)
    (hCfam : 0 < Cfam) (D : ℕ) (e : Fin 2 → Fin D) (he : Function.Injective e) (w : L) :
    (∀ ρ' : L → Measure ℝ, (∀ v, IsProbabilityMeasure (ρ' v)) →
      (∀ v ∈ S, S45.MomentLaw (ρ' v) t 2 id) →
      ‖∑ v ∈ S, ∫ z, ΦS_a2 D e (S45.lagInc t sk v z w) ∂(ρ' v)‖ ≤
        Cfam * (S45.logFactor t * (S45.power t (2 * S45.beta) + Real.sqrt t) +
          S45.logFactor t ^ 2 * S45.power t (S45.delta / 2))) ∧
    (∀ z : L → ℝ, (∀ v ∈ S, |z v| ≤ 2 * Real.sqrt t) →
      ∑ v ∈ S, (ΦS_a2 D e (S45.lagInc t sk v (z v) w)) ^ 2 ≤
        (Cfam * S45.logFactor t ^ 2 * S45.power t S45.delta) • (1 : S45.CMat (Fin D))) ∧
    (∀ v ∈ S, ∀ z, |z| ≤ 2 * Real.sqrt t →
      ‖ΦS_a2 D e (S45.lagInc t sk v z w)‖ ≤
        Cfam * S45.logFactor t * S45.power t (S45.delta / 2)) := by
  have hL := AgentS45.logFactor_pos ht ht1
  have hp : ∀ e, 0 < S45.power t e := fun e => Real.rpow_pos_of_pos ht e
  have h2 := two_sqrt_le_a2 (t := t) hC4
  refine ⟨fun ρ' hρ hmom => ?_, fun z hz => ?_, fun v hv z hz => ?_⟩
  · haveI : ∀ v, IsProbabilityMeasure (ρ' v) := hρ
    have FT := FTHyp_pi_a2 hFT hC4 ρ' hmom
    rw [mean_transfer_a2 ρ' S (fun v z => S45.lagInc t sk v z w)
      (fun v => (measurable_lagInc_a2 t sk v w).aestronglyMeasurable)
      (Cfam * S45.logFactor t * S45.power t (S45.delta / 2))
      (fun v hv => by
        filter_upwards [(hmom v hv).bounded] with z hz
        exact FT.lag_jump v hv z (hz.trans h2) w) (ΦS_a2 D e)]
    exact (ΦS_norm_le D e he _).trans (FT.lag_mean w)
  · have FT := FTHyp_two_a2 hFT ht hC4
    have hsq := FT.lag_square z (fun v hv => (hz v hv).trans h2) w
    change ∑ v ∈ S, (padInto D e (scalarDilation (S45.lagInc t sk v (z v) w))) ^ 2 ≤ _
    exact stack_scalar_a2 S D e he (fun v => scalarDilation (S45.lagInc t sk v (z v) w))
      (fun v => ‖S45.lagInc t sk v (z v) w‖ ^ 2) (fun v _ => le_of_eq (scalarDilation_sq _)) _
      (by have := hp S45.delta; positivity) hsq
  · have FT := FTHyp_two_a2 hFT ht hC4
    exact (ΦS_norm_le D e he _).trans (FT.lag_jump v hv z (hz.trans h2) w)

/-- Row monitors at a live inner port `w` with column set `cols`. -/
theorem row_kind_a2 {t C4 Cfam : ℝ} {sk : S45.State L} {S cols : Finset L} {B : Matrix L H ℝ}
    (hFT : FTHyp_a2 t C4 Cfam sk S cols B) (ht : 0 < t) (hC4 : 2 ≤ C4)
    (hCfam : 0 < Cfam) (D : ℕ) (e : Fin 2 → Fin D) (he : Function.Injective e) (w : L) :
    (∀ ρ' : L → Measure ℝ, (∀ v, IsProbabilityMeasure (ρ' v)) →
      (∀ v ∈ S, S45.MomentLaw (ρ' v) t 2 id) →
      ‖∑ v ∈ S, ∫ z, ΦR_a2 D e (S45.fourthProxy t sk cols w v z / S45.rowCap t) ∂(ρ' v)‖ ≤
        Cfam * S45.power t S45.kappa) ∧
    (∀ z : L → ℝ, (∀ v ∈ S, |z v| ≤ 2 * Real.sqrt t) →
      ∑ v ∈ S, (ΦR_a2 D e (S45.fourthProxy t sk cols w v (z v) / S45.rowCap t)) ^ 2 ≤
        (Cfam * S45.power t S45.kappa) • (1 : S45.CMat (Fin D))) ∧
    (∀ v ∈ S, ∀ z, |z| ≤ 2 * Real.sqrt t →
      ‖ΦR_a2 D e (S45.fourthProxy t sk cols w v z / S45.rowCap t)‖ ≤
        Cfam * S45.power t (S45.kappa / 2)) := by
  have hp : ∀ e, 0 < S45.power t e := fun e => Real.rpow_pos_of_pos ht e
  have h2 := two_sqrt_le_a2 (t := t) hC4
  refine ⟨fun ρ' hρ hmom => ?_, fun z hz => ?_, fun v hv z hz => ?_⟩
  · haveI : ∀ v, IsProbabilityMeasure (ρ' v) := hρ
    have FT := FTHyp_pi_a2 hFT hC4 ρ' hmom
    rw [mean_transfer_a2 ρ' S (fun v z => S45.fourthProxy t sk cols w v z / S45.rowCap t)
      (fun v => ((measurable_fourthProxy_a2 t sk cols w v).div_const _).aestronglyMeasurable)
      (Cfam * S45.power t (S45.kappa / 2))
      (fun v hv => by
        filter_upwards [(hmom v hv).bounded] with z hz
        rw [Real.norm_eq_abs]
        exact FT.row_jump v hv z (hz.trans h2) w) (ΦR_a2 D e)]
    refine (ΦR_norm_le D e he _).trans ?_
    rw [Real.norm_eq_abs]
    exact FT.row_mean w
  · have FT := FTHyp_two_a2 hFT ht hC4
    have hsq := FT.row_square z (fun v hv => (hz v hv).trans h2) w
    change ∑ v ∈ S, (padInto D e (scalarBlock
      (S45.fourthProxy t sk cols w v (z v) / S45.rowCap t))) ^ 2 ≤ _
    exact stack_scalar_a2 S D e he
      (fun v => scalarBlock (S45.fourthProxy t sk cols w v (z v) / S45.rowCap t))
      (fun v => |S45.fourthProxy t sk cols w v (z v) / S45.rowCap t| ^ 2)
      (fun v _ => scalarBlock_sq_le _) _ (by have := hp S45.kappa; positivity) hsq
  · have FT := FTHyp_two_a2 hFT ht hC4
    refine (ΦR_norm_le D e he _).trans ?_
    rw [Real.norm_eq_abs]
    exact FT.row_jump v hv z (hz.trans h2) w

end Kinds

/-! ## Matrix monitors -/

section MatrixKinds

variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

/-- The `J` monitor. -/
theorem J_kind_a2 (L' : Finset (Port d m)) {t C4 Cfam : ℝ} {sk : S45.State L'}
    {S cols : Finset L'} {B : Matrix L' (Fin (localDim P j T)) ℝ}
    (hFT : FTHyp_a2 t C4 Cfam sk S cols B) (ht : 0 < t) (hC4 : 2 ≤ C4) (hCfam : 0 < Cfam) :
    (∀ ρ' : L' → Measure ℝ, (∀ v, IsProbabilityMeasure (ρ' v)) →
      (∀ v ∈ S, S45.MomentLaw (ρ' v) t 2 id) →
      ‖∑ v ∈ S, ∫ z, ΦJ_a2 P j T L' (S45.Jinc t sk v z) ∂(ρ' v)‖ ≤
        Cfam * S45.power t S45.beta) ∧
    (∀ z : L' → ℝ, (∀ v ∈ S, |z v| ≤ 2 * Real.sqrt t) →
      ∑ v ∈ S, (ΦJ_a2 P j T L' (S45.Jinc t sk v (z v))) ^ 2 ≤
        (Cfam * S45.power t (S45.delta / 2)) • (1 : S45.CMat (Fin (monitorDim P j T)))) ∧
    (∀ v ∈ S, ∀ z, |z| ≤ 2 * Real.sqrt t →
      ‖ΦJ_a2 P j T L' (S45.Jinc t sk v z)‖ ≤ Cfam * S45.power t (S45.delta / 4)) := by
  have hp : ∀ e, 0 < S45.power t e := fun e => Real.rpow_pos_of_pos ht e
  have h2 := two_sqrt_le_a2 (t := t) hC4
  refine ⟨fun ρ' hρ hmom => ?_, fun z hz => ?_, fun v hv z hz => ?_⟩
  · haveI : ∀ v, IsProbabilityMeasure (ρ' v) := hρ
    have FT := FTHyp_pi_a2 hFT hC4 ρ' hmom
    rw [mean_transfer_a2 ρ' S (fun v z => S45.Jinc t sk v z)
      (fun v => (measurable_Jinc_a2 t sk v).aestronglyMeasurable)
      (Cfam * S45.power t (S45.delta / 4))
      (fun v hv => by
        filter_upwards [(hmom v hv).bounded] with z hz
        exact FT.J_jump v hv z (hz.trans h2)) (ΦJ_a2 P j T L')]
    exact (ΦJ_norm_le P j T L' _).trans FT.J_mean
  · have FT := FTHyp_two_a2 hFT ht hC4
    have hsq := FT.J_squares z (fun v hv => (hz v hv).trans h2)
    have hR0 : 0 ≤ Cfam * S45.power t (S45.delta / 2) := by
      have := hp (S45.delta / 2); positivity
    change ∑ v ∈ S, (padInto _ (embJ P j T)
      (S45.dilation (compressJ P j T L' (S45.Jinc t sk v (z v))))) ^ 2 ≤ _
    refine stack_dil_a2 S _ (embJ P j T) (embJ_injective P j T)
      (fun v => compressJ P j T L' (S45.Jinc t sk v (z v))) _ hR0 ?_ ?_
    · refine (Finset.sum_le_sum fun v _ => compressJ_mul_conjTranspose_le P j T L' _).trans ?_
      rw [← compressJ_sum]
      exact compressJ_le_smul_one P j T L' hR0 hsq.1
    · refine (Finset.sum_le_sum fun v _ => compressJ_conjTranspose_mul_le P j T L' _).trans ?_
      rw [← compressJ_sum]
      exact compressJ_le_smul_one P j T L' hR0 hsq.2
  · have FT := FTHyp_two_a2 hFT ht hC4
    exact (ΦJ_norm_le P j T L' _).trans (FT.J_jump v hv z (hz.trans h2))

theorem pullback_isSymm_a2 {ι H : Type*} (B : Matrix ι H ℝ) {X : S45.RMat ι} (hX : X.IsSymm)
    [Fintype ι] [Fintype H] : (S45.pullback B X).IsSymm := by
  unfold S45.pullback
  rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hX.eq, Matrix.mul_assoc]

theorem map_ofReal_conjTranspose_a2 {H : Type*} {X : S45.RMat H} (hX : X.IsSymm) :
    (X.map (fun a : ℝ => (a : ℂ)))ᴴ = X.map (fun a : ℝ => (a : ℂ)) := by
  ext a b
  simp [Matrix.conjTranspose_apply, hX.apply a b]

/-- The `L` monitor. -/
theorem L_kind_a2 (L' : Finset (Port d m)) {t C4 Cfam : ℝ} {sk : S45.State L'}
    {S cols : Finset L'} {B : Matrix L' (Fin (localDim P j T)) ℝ}
    (hFT : FTHyp_a2 t C4 Cfam sk S cols B) (ht : 0 < t) (hC4 : 2 ≤ C4) (hCfam : 0 < Cfam)
    (hsym : sk.g.IsSymm) :
    (∀ ρ' : L' → Measure ℝ, (∀ v, IsProbabilityMeasure (ρ' v)) →
      (∀ v ∈ S, S45.MomentLaw (ρ' v) t 2 id) →
      ‖∑ v ∈ S, ∫ z, ΦL_a2 P j T (S45.pullback B (S45.Linc t sk v z)) ∂(ρ' v)‖ ≤
        Cfam * S45.power t S45.beta) ∧
    (∀ z : L' → ℝ, (∀ v ∈ S, |z v| ≤ 2 * Real.sqrt t) →
      ∑ v ∈ S, (ΦL_a2 P j T (S45.pullback B (S45.Linc t sk v (z v)))) ^ 2 ≤
        (Cfam * S45.power t (S45.delta / 2)) • (1 : S45.CMat (Fin (monitorDim P j T)))) ∧
    (∀ v ∈ S, ∀ z, |z| ≤ 2 * Real.sqrt t →
      ‖ΦL_a2 P j T (S45.pullback B (S45.Linc t sk v z))‖ ≤ Cfam * S45.power t (S45.delta / 4)) := by
  have hp : ∀ e, 0 < S45.power t e := fun e => Real.rpow_pos_of_pos ht e
  have h2 := two_sqrt_le_a2 (t := t) hC4
  refine ⟨fun ρ' hρ hmom => ?_, fun z hz => ?_, fun v hv z hz => ?_⟩
  · haveI : ∀ v, IsProbabilityMeasure (ρ' v) := hρ
    have FT := FTHyp_pi_a2 hFT hC4 ρ' hmom
    rw [mean_transfer_a2 ρ' S (fun v z => S45.pullback B (S45.Linc t sk v z))
      (fun v => (measurable_pullback_Linc_a2 t sk v B).aestronglyMeasurable)
      (Cfam * S45.power t (S45.delta / 4))
      (fun v hv => by
        filter_upwards [(hmom v hv).bounded] with z hz
        exact FT.L_jump v hv z (hz.trans h2)) (ΦL_a2 P j T)]
    exact (ΦL_norm_le P j T _).trans FT.L_mean
  · have FT := FTHyp_two_a2 hFT ht hC4
    have hsq := FT.L_square z (fun v hv => (hz v hv).trans h2)
    have hR0 : 0 ≤ Cfam * S45.power t (S45.delta / 2) := by
      have := hp (S45.delta / 2); positivity
    have hsymX : ∀ v, (S45.pullback B (S45.Linc t sk v (z v))).IsSymm := fun v =>
      pullback_isSymm_a2 B (AgentS45.Linc_symmetric t sk v (z v) hsym)
    have hC := real_sq_sum_le_complex S (fun v => S45.pullback B (S45.Linc t sk v (z v))) _ hsq
    change ∑ v ∈ S, (padInto _ (embL P j T)
      (S45.dilation ((S45.pullback B (S45.Linc t sk v (z v))).map (fun a : ℝ => (a : ℂ))))) ^ 2 ≤ _
    refine stack_dil_a2 S _ (embL P j T) (embL_injective P j T)
      (fun v => (S45.pullback B (S45.Linc t sk v (z v))).map (fun a : ℝ => (a : ℂ))) _ hR0 ?_ ?_
    · refine le_of_eq_of_le ?_ hC
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_ofReal_conjTranspose_a2 (hsymX v), sq]
    · refine le_of_eq_of_le ?_ hC
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_ofReal_conjTranspose_a2 (hsymX v), sq]
  · have FT := FTHyp_two_a2 hFT ht hC4
    exact (ΦL_norm_le P j T _).trans (FT.L_jump v hv z (hz.trans h2))

end MatrixKinds

/-! ## Assembly at a running slot -/

section Assembly

theorem budget_a2 {Lf X Cf C' : ℝ} (hL : 0 < Lf) (hX : 0 ≤ X) (hc : Cf ≤ C') :
    Cf * X ≤ C' * (Lf * X) / Lf := by
  rw [mul_div_assoc, mul_div_cancel_left₀ X hL.ne']
  exact mul_le_mul_of_nonneg_right hc hX

theorem zero_kind_a2 {L : Type} {D : ℕ} (S : Finset L) (t : ℝ) :
    (∀ ρ' : L → Measure ℝ, (∀ v, IsProbabilityMeasure (ρ' v)) →
      (∀ v ∈ S, S45.MomentLaw (ρ' v) t 2 id) →
      ‖∑ v ∈ S, ∫ z, (fun (_ : L) (_ : ℝ) => (0 : S45.CMat (Fin D))) v z ∂(ρ' v)‖ ≤ 0) ∧
    (∀ z : L → ℝ, (∀ v ∈ S, |z v| ≤ 2 * Real.sqrt t) →
      ∑ v ∈ S, ((fun (_ : L) (_ : ℝ) => (0 : S45.CMat (Fin D))) v (z v)) ^ 2 ≤
        (0 : ℝ) • (1 : S45.CMat (Fin D))) ∧
    (∀ v ∈ S, ∀ z, |z| ≤ 2 * Real.sqrt t →
      ‖(fun (_ : L) (_ : ℝ) => (0 : S45.CMat (Fin D))) v z‖ ≤ 0) := by
  refine ⟨fun _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ _ => by simp⟩

variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
  (x : RunRecord d m)

open Classical in
theorem rem_transfer'_a2 {D : ℕ} (L : Finset (Port d m)) (rem : Finset (Fin (siteCount d m)))
    (t Bm Bs Bj Bm' Bs' Bj' : ℝ) (hBs : 0 ≤ Bs) (hBj : 0 ≤ Bj)
    (hm : Bm' ≤ Bm) (hs : Bs' ≤ Bs) (hj : Bj' ≤ Bj)
    (ev : Fin (siteCount d m) → ℝ → S45.CMat (Fin D)) (G : L → ℝ → S45.CMat (Fin D))
    (hbad : ∀ y ∈ rem, ¬ (activeIn P j T x ((siteRank d m).symm y) ∧
      (((siteRank d m).symm y, false) : Port d m) ∈ L) → ∀ z, ev y z = 0)
    (hgood : ∀ v ∈ slotPorts_a2 P j T x L rem, ∀ z, ev (siteRank d m v.1.1) z = G v z)
    (hkind : (∀ ρ' : L → Measure ℝ, (∀ v, IsProbabilityMeasure (ρ' v)) →
      (∀ v ∈ slotPorts_a2 P j T x L rem, S45.MomentLaw (ρ' v) t 2 id) →
      ‖∑ v ∈ slotPorts_a2 P j T x L rem, ∫ z, G v z ∂(ρ' v)‖ ≤ Bm') ∧
    (∀ z : L → ℝ, (∀ v ∈ slotPorts_a2 P j T x L rem, |z v| ≤ 2 * Real.sqrt t) →
      ∑ v ∈ slotPorts_a2 P j T x L rem, (G v (z v)) ^ 2 ≤ Bs' • (1 : S45.CMat (Fin D))) ∧
    (∀ v ∈ slotPorts_a2 P j T x L rem, ∀ z, |z| ≤ 2 * Real.sqrt t → ‖G v z‖ ≤ Bj')) :
    (∀ (ρ : Fin (siteCount d m) → Measure ℝ), (∀ y, IsProbabilityMeasure (ρ y)) →
      (∀ y ∈ rem, S45.MomentLaw (ρ y) t 2 id) →
      ‖∑ y ∈ rem, ∫ z, ev y z ∂(ρ y)‖ ≤ Bm) ∧
    (∀ z : Fin (siteCount d m) → ℝ, (∀ y ∈ rem, |z y| ≤ 2 * Real.sqrt t) →
      (∑ y ∈ rem, (ev y (z y)) ^ 2) ≤ Bs • (1 : S45.CMat (Fin D))) ∧
    (∀ y ∈ rem, ∀ z, |z| ≤ 2 * Real.sqrt t → ‖ev y z‖ ≤ Bj) :=
  rem_transfer_a2 P j T x L rem t Bm Bs Bj hBs hBj ev G hbad hgood
    (fun ρ' hρ hmom => (hkind.1 ρ' hρ hmom).trans hm)
    (fun z hz => (hkind.2.1 z hz).trans (smul_le_smul_of_nonneg_right hs zero_le_one_cmat_a2))
    (fun v hv z hz => (hkind.2.2 v hv z hz).trans hj)

theorem scalarDilation_zero_a2 : scalarDilation 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [scalarDilation]

theorem scalarBlock_zero_a2 : scalarBlock 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [scalarBlock]

open Classical in
/-- **All monitor bounds at a running slot.** -/
theorem slot_bounds_a2 (C4 Cfam C' : ℝ) (hC4 : 2 ≤ C4) (hCfam : 0 < Cfam) (hC' : Cfam ≤ C')
    (htpos : 0 < sweepScale P.u m j) (ht1 : sweepScale P.u m j ≤ 1)
    (k : ℕ) (ω : RandomSources (Torus d m) M) (q : S45.Sequence (Port d m))
    (hq : slotSeq P j T M x k ω = some q)
    (hFT : (q.state q.length).live.Nonempty →
      ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)).g.IsSymm ∧
      ∀ cols, FTHyp_a2 (sweepScale P.u m j) C4 Cfam
        ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
        (slotPorts_a2 P j T x (q.state q.length).live (tileRemaining P j T M k ω)) cols
        (fun a j_col => ((P.cover j).cover.coords T).B a.1 j_col))
    (i : Fin (monitorCount P j T)) :
    (∀ (ρ : Fin (siteCount d m) → Measure ℝ), (∀ y, IsProbabilityMeasure (ρ y)) →
      (∀ y ∈ tileRemaining P j T M k ω, S45.MomentLaw (ρ y) (sweepScale P.u m j) 2 id) →
      ‖∑ y ∈ tileRemaining P j T M k ω, ∫ z, tileEval P j T M x i k ω y z ∂(ρ y)‖ ≤
        C' * S45.monitorBias (sweepScale P.u m j) (monitorKind P j T i) /
          S45.logFactor (sweepScale P.u m j)) ∧
    (∀ z : Fin (siteCount d m) → ℝ,
      (∀ y ∈ tileRemaining P j T M k ω, |z y| ≤ 2 * Real.sqrt (sweepScale P.u m j)) →
      (∑ y ∈ tileRemaining P j T M k ω, (tileEval P j T M x i k ω y (z y)) ^ 2) ≤
        (C' * S45.monitorVariance (sweepScale P.u m j) (monitorKind P j T i) /
          S45.logFactor (sweepScale P.u m j)) • (1 : S45.CMat (Fin (monitorDim P j T)))) ∧
    (∀ y ∈ tileRemaining P j T M k ω, ∀ z, |z| ≤ 2 * Real.sqrt (sweepScale P.u m j) →
      ‖tileEval P j T M x i k ω y z‖ ≤
        C' * S45.monitorJump (sweepScale P.u m j) (monitorKind P j T i)) := by
  have hL := AgentS45.logFactor_pos htpos ht1
  have hp : ∀ e, 0 < S45.power (sweepScale P.u m j) e := fun e => Real.rpow_pos_of_pos htpos e
  have hC'0 : 0 < C' := hCfam.trans_le hC'
  obtain ⟨hJ0, hV0, hB0⟩ := AgentS45.monitor_nonneg htpos ht1 (monitorKind P j T i)
  have hBm : 0 ≤ C' * S45.monitorBias (sweepScale P.u m j) (monitorKind P j T i) /
      S45.logFactor (sweepScale P.u m j) := div_nonneg (mul_nonneg hC'0.le hB0) hL.le
  have hBs : 0 ≤ C' * S45.monitorVariance (sweepScale P.u m j) (monitorKind P j T i) /
      S45.logFactor (sweepScale P.u m j) := div_nonneg (mul_nonneg hC'0.le hV0) hL.le
  have hBj : 0 ≤ C' * S45.monitorJump (sweepScale P.u m j) (monitorKind P j T i) :=
    mul_nonneg hC'0.le hJ0
  have hbad : ∀ y ∈ tileRemaining P j T M k ω,
      ¬ (activeIn P j T x ((siteRank d m).symm y) ∧
        (((siteRank d m).symm y, false) : Port d m) ∈ (q.state q.length).live) →
      ∀ z, tileEval P j T M x i k ω y z = 0 := fun y _ hn z => by
    rw [tileEval_slot_a2 P j T M x i k ω q hq, if_neg hn]
  by_cases hne : (q.state q.length).live.Nonempty
  swap
  · refine rem_transfer'_a2 P j T x _ _ _ _ _ _ 0 0 0 hBs hBj hBm hBs hBj _
      (fun _ _ => (0 : S45.CMat (Fin (monitorDim P j T)))) hbad ?_ (zero_kind_a2 _ _)
    intro v _ z
    exact absurd ⟨v.1, v.2⟩ hne
  obtain ⟨hsym, hFTc⟩ := hFT hne
  have hev : ∀ v ∈ slotPorts_a2 P j T x (q.state q.length).live (tileRemaining P j T M k ω),
      ∀ z, tileEval P j T M x i k ω (siteRank d m v.1.1) z =
        monitorOf P j T i
          (fun u => if hu : u ∈ (q.state q.length).live then
            S45.lagInc (sweepScale P.u m j)
              ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) v z ⟨u, hu⟩ else 0)
          (fun u => if hu : u ∈ (q.state q.length).live then
            S45.fourthProxy (sweepScale P.u m j)
              ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
              (Finset.univ.filter (fun v : (q.state q.length).live =>
                v.1 ∈ (Finset.univ : Finset (Port d m))))
              ⟨u, hu⟩ v z / S45.rowCap (sweepScale P.u m j) else 0)
          (fun u => if hu : u ∈ (q.state q.length).live then
            S45.fourthProxy (sweepScale P.u m j)
              ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
              (Finset.univ.filter (fun v : (q.state q.length).live =>
                v.1 ∈ (S45.reserves : Finset (Port d m))))
              ⟨u, hu⟩ v z / S45.rowCap (sweepScale P.u m j) else 0)
          (S45.pad (q.state q.length).live (S45.Jinc (sweepScale P.u m j)
            ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) v z))
          (S45.pad (q.state q.length).live (S45.Linc (sweepScale P.u m j)
            ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) v z)) := by
    intro v hv z
    have hv' := (mem_slotPorts_a2 P j T x _ _ v).mp hv
    have hvq : v.1 = (v.1.1, false) := Prod.ext rfl hv'.1
    have hal2 : ((v.1.1, false) : Port d m) ∈ (q.state q.length).live := hvq ▸ v.2
    have hpv : (⟨(v.1.1, false), hal2⟩ : (q.state q.length).live) = v := Subtype.ext hvq.symm
    rw [tileEval_slot_a2 P j T M x i k ω q hq]
    simp only [Equiv.symm_apply_apply]
    rw [if_pos ⟨hv'.2.2, hal2⟩, stepMon_form_a2 P j T x i q v.1.1 z hal2 htpos, hpv]
  have hn3 : i.val ≤ 3 * (innerPorts P j T).card + 1 := by
    have := i.isLt; unfold monitorCount at this; omega
  by_cases h1 : i.val < (innerPorts P j T).card
  · -- lag monitors
    have hk : monitorKind P j T i = .lag := by unfold monitorKind; rw [if_pos h1]
    obtain ⟨u, hu_def⟩ : ∃ u : Port d m,
        u = ↑((innerPorts P j T).equivFin.symm ⟨i.val, h1⟩) := ⟨_, rfl⟩
    have hmo : ∀ a b c J Lm, monitorOf P j T i a b c J Lm =
        padInto _ (embS P j T) (scalarDilation (a u)) := by
      intro a b c J Lm; unfold monitorOf; rw [dif_pos h1, ← hu_def]
    rw [hk]
    rw [hk] at hBm hBs hBj
    by_cases hu : u ∈ (q.state q.length).live
    · refine rem_transfer'_a2 P j T x _ _ _ _ _ _ _ _ _ hBs hBj ?_ ?_ ?_ _
        (fun v z => ΦS_a2 _ (embS P j T) (S45.lagInc (sweepScale P.u m j)
          ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) v z ⟨u, hu⟩))
        hbad ?_ (lag_kind_a2 (hFTc Finset.univ) htpos ht1 hC4 hCfam _ (embS P j T)
          (embS_injective P j T) ⟨u, hu⟩)
      · have hX : 0 ≤ S45.logFactor (sweepScale P.u m j) *
            (S45.power (sweepScale P.u m j) (2 * S45.beta) + Real.sqrt (sweepScale P.u m j)) +
            S45.logFactor (sweepScale P.u m j) ^ 2 * S45.power (sweepScale P.u m j) (S45.delta / 2) :=
          add_nonneg (mul_nonneg hL.le (add_nonneg (hp _).le (Real.sqrt_nonneg _)))
            (mul_nonneg (pow_nonneg hL.le 2) (hp _).le)
        have he : S45.monitorBias (sweepScale P.u m j) .lag = S45.logFactor (sweepScale P.u m j) *
            (S45.logFactor (sweepScale P.u m j) *
              (S45.power (sweepScale P.u m j) (2 * S45.beta) + Real.sqrt (sweepScale P.u m j)) +
            S45.logFactor (sweepScale P.u m j) ^ 2 *
              S45.power (sweepScale P.u m j) (S45.delta / 2)) := by
          simp only [S45.monitorBias]; ring
        rw [he]
        exact budget_a2 hL hX hC'
      · have he : S45.monitorVariance (sweepScale P.u m j) .lag =
            S45.logFactor (sweepScale P.u m j) * (S45.logFactor (sweepScale P.u m j) ^ 2 *
              S45.power (sweepScale P.u m j) S45.delta) := by
          simp only [S45.monitorVariance]; ring
        rw [he, mul_assoc Cfam]
        exact budget_a2 hL (mul_nonneg (pow_nonneg hL.le 2) (hp _).le) hC'
      · simp only [S45.monitorJump]
        rw [mul_assoc Cfam]
        exact mul_le_mul_of_nonneg_right hC' (mul_nonneg hL.le (hp _).le)
      · intro v hv z
        rw [hev v hv z, hmo]
        simp only [dif_pos hu]
        rfl
    · refine rem_transfer'_a2 P j T x _ _ _ _ _ _ 0 0 0 hBs hBj hBm hBs hBj _
        (fun _ _ => (0 : S45.CMat (Fin (monitorDim P j T)))) hbad ?_ (zero_kind_a2 _ _)
      intro v hv z
      rw [hev v hv z, hmo]
      simp only [dif_neg hu, scalarDilation_zero_a2, padInto_zero]
  by_cases h3 : i.val < 3 * (innerPorts P j T).card
  · -- row monitors
    have hk : monitorKind P j T i = .row := by
      unfold monitorKind; rw [if_neg h1, if_pos h3]
    rw [hk]
    rw [hk] at hBm hBs hBj
    have hbm : Cfam * S45.power (sweepScale P.u m j) S45.kappa ≤
        C' * S45.monitorBias (sweepScale P.u m j) .row / S45.logFactor (sweepScale P.u m j) := by
      simp only [S45.monitorBias]
      exact budget_a2 hL (hp _).le hC'
    have hbs : Cfam * S45.power (sweepScale P.u m j) S45.kappa ≤
        C' * S45.monitorVariance (sweepScale P.u m j) .row /
          S45.logFactor (sweepScale P.u m j) := by
      simp only [S45.monitorVariance]
      exact budget_a2 hL (hp _).le hC'
    have hbj : Cfam * S45.power (sweepScale P.u m j) (S45.kappa / 2) ≤
        C' * S45.monitorJump (sweepScale P.u m j) .row := by
      simp only [S45.monitorJump]
      exact mul_le_mul_of_nonneg_right hC' (hp _).le
    by_cases h2 : i.val < 2 * (innerPorts P j T).card
    · obtain ⟨u, hu_def⟩ : ∃ u : Port d m,
          u = ↑((innerPorts P j T).equivFin.symm ⟨i.val - (innerPorts P j T).card, by omega⟩) := ⟨_, rfl⟩
      have hmo : ∀ a b c J Lm, monitorOf P j T i a b c J Lm =
          padInto _ (embS P j T) (scalarBlock (b u)) := by
        intro a b c J Lm; unfold monitorOf; rw [dif_neg h1, dif_pos h2, ← hu_def]
      by_cases hu : u ∈ (q.state q.length).live
      · refine rem_transfer'_a2 P j T x _ _ _ _ _ _ _ _ _ hBs hBj hbm hbs hbj _
          (fun v z => ΦR_a2 _ (embS P j T) (S45.fourthProxy (sweepScale P.u m j)
            ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
            (Finset.univ.filter (fun v : (q.state q.length).live =>
              v.1 ∈ (Finset.univ : Finset (Port d m)))) ⟨u, hu⟩ v z / S45.rowCap (sweepScale P.u m j)))
          hbad ?_ (row_kind_a2 (hFTc _) htpos hC4 hCfam _ (embS P j T) (embS_injective P j T)
            ⟨u, hu⟩)
        intro v hv z
        rw [hev v hv z, hmo]
        simp only [dif_pos hu]
        rfl
      · refine rem_transfer'_a2 P j T x _ _ _ _ _ _ 0 0 0 hBs hBj hBm hBs hBj _
          (fun _ _ => (0 : S45.CMat (Fin (monitorDim P j T)))) hbad ?_ (zero_kind_a2 _ _)
        intro v hv z
        rw [hev v hv z, hmo]
        simp only [dif_neg hu, scalarBlock_zero_a2, padInto_zero]
    · obtain ⟨u, hu_def⟩ : ∃ u : Port d m,
          u = ↑((innerPorts P j T).equivFin.symm ⟨i.val - 2 * (innerPorts P j T).card, by omega⟩) := ⟨_, rfl⟩
      have hmo : ∀ a b c J Lm, monitorOf P j T i a b c J Lm =
          padInto _ (embS P j T) (scalarBlock (c u)) := by
        intro a b c J Lm; unfold monitorOf; rw [dif_neg h1, dif_neg h2, dif_pos h3, ← hu_def]
      by_cases hu : u ∈ (q.state q.length).live
      · refine rem_transfer'_a2 P j T x _ _ _ _ _ _ _ _ _ hBs hBj hbm hbs hbj _
          (fun v z => ΦR_a2 _ (embS P j T) (S45.fourthProxy (sweepScale P.u m j)
            ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
            (Finset.univ.filter (fun v : (q.state q.length).live =>
              v.1 ∈ (S45.reserves : Finset (Port d m)))) ⟨u, hu⟩ v z / S45.rowCap (sweepScale P.u m j)))
          hbad ?_ (row_kind_a2 (hFTc _) htpos hC4 hCfam _ (embS P j T) (embS_injective P j T)
            ⟨u, hu⟩)
        intro v hv z
        rw [hev v hv z, hmo]
        simp only [dif_pos hu]
        rfl
      · refine rem_transfer'_a2 P j T x _ _ _ _ _ _ 0 0 0 hBs hBj hBm hBs hBj _
          (fun _ _ => (0 : S45.CMat (Fin (monitorDim P j T)))) hbad ?_ (zero_kind_a2 _ _)
        intro v hv z
        rw [hev v hv z, hmo]
        simp only [dif_neg hu, scalarBlock_zero_a2, padInto_zero]
  have h2 : ¬ i.val < 2 * (innerPorts P j T).card := by omega
  have hk : monitorKind P j T i = .matrix := by
    unfold monitorKind; rw [if_neg h1, if_neg h3]
  rw [hk]
  rw [hk] at hBm hBs hBj
  have hbm : Cfam * S45.power (sweepScale P.u m j) S45.beta ≤
      C' * S45.monitorBias (sweepScale P.u m j) .matrix / S45.logFactor (sweepScale P.u m j) := by
    simp only [S45.monitorBias]
    exact budget_a2 hL (hp _).le hC'
  have hbs : Cfam * S45.power (sweepScale P.u m j) (S45.delta / 2) ≤
      C' * S45.monitorVariance (sweepScale P.u m j) .matrix /
        S45.logFactor (sweepScale P.u m j) := by
    simp only [S45.monitorVariance]
    exact budget_a2 hL (hp _).le hC'
  have hbj : Cfam * S45.power (sweepScale P.u m j) (S45.delta / 4) ≤
      C' * S45.monitorJump (sweepScale P.u m j) .matrix := by
    simp only [S45.monitorJump]
    exact mul_le_mul_of_nonneg_right hC' (hp _).le
  by_cases h4 : i.val = 3 * (innerPorts P j T).card
  · have hmo : ∀ a b c J Lm, monitorOf P j T i a b c J Lm =
        padInto _ (embJ P j T) (S45.dilation (S45.restrict J (innerPorts P j T))) := by
      intro a b c J Lm; unfold monitorOf; rw [dif_neg h1, dif_neg h2, dif_neg h3, if_pos h4]
    refine rem_transfer'_a2 P j T x _ _ _ _ _ _ _ _ _ hBs hBj hbm hbs hbj _
      (fun v z => ΦJ_a2 P j T (q.state q.length).live (S45.Jinc (sweepScale P.u m j)
        ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) v z))
      hbad ?_ (J_kind_a2 P j T (q.state q.length).live (hFTc Finset.univ) htpos hC4 hCfam)
    intro v hv z
    rw [hev v hv z, hmo]
    rfl
  · have hmo : ∀ a b c J Lm, monitorOf P j T i a b c J Lm =
        padInto _ (embL P j T) (S45.dilation ((S45.pullback ((P.cover j).cover.coords T).B
          Lm).map (fun a => (a : ℂ)))) := by
      intro a b c J Lm; unfold monitorOf; rw [dif_neg h1, dif_neg h2, dif_neg h3, if_neg h4]
    refine rem_transfer'_a2 P j T x _ _ _ _ _ _ _ _ _ hBs hBj hbm hbs hbj _
      (fun v z => ΦL_a2 P j T (S45.pullback
        (fun (a : (q.state q.length).live) (j_col : Fin (localDim P j T)) =>
          ((P.cover j).cover.coords T).B a.1 j_col)
        (S45.Linc (sweepScale P.u m j)
          ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)) v z)))
      hbad ?_ (L_kind_a2 P j T (q.state q.length).live (hFTc Finset.univ) htpos hC4 hCfam hsym)
    intro v hv z
    rw [hev v hv z, hmo, pullback_pad]
    rfl

end Assembly

/-! ## The A2 theorem -/

section Main

theorem power_nonneg_a2 {a : ℝ} (ha : 0 ≤ a) (e : ℝ) : 0 ≤ S45.power a e := Real.rpow_nonneg ha e

theorem l1_nonneg_a2 {ι : Type*} [Fintype ι] (y : ι → ℝ) : 0 ≤ S45.l1 y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem l2sq_nonneg_a2 {ι : Type*} [Fintype ι] (y : ι → ℝ) : 0 ≤ S45.l2sq y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A prestate stays a prestate for a larger constant (with the Fourier form cut at `0`). -/
theorem prestate_mono_a2 {P : Type*} [Fintype P] [DecidableEq P] {t C C' : ℝ}
    {Λ Wstar : S45.Form P} {s : S45.State P} (h : S45.Prestate t C Λ Wstar s) (hC : 0 < C)
    (hCC : C ≤ C') : S45.Prestate t C' (fun y => max (Λ y) 0) Wstar s where
  scale := h.scale
  broad := fun i => by
    obtain ⟨h1, h2, h3⟩ := h.broad i
    exact ⟨h1.trans hCC, le_trans (one_div_le_one_div_of_le hC hCC) h2, h3.trans hCC⟩
  symmetric := h.symmetric
  ward := h.ward
  K_cap := h.K_cap
  invertible := h.invertible
  kernel := h.kernel
  row_cap := h.row_cap
  lag_cap := h.lag_cap
  sharp := fun y hy => by
    have h1 := h.sharp y hy
    have ht : 0 ≤ t := h.scale.1.le
    have hκ : 0 ≤ S45.power t S45.kappa := power_nonneg_a2 ht _
    have hsum : 0 ≤ ∑ i, y i ^ 2 / s.p i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    have hΛ : Λ y ≤ max (Λ y) 0 := le_max_left _ _
    have hΛ0 : 0 ≤ max (Λ y) 0 := le_max_right _ _
    have e1 : C * t * Λ y ≤ C' * t * max (Λ y) 0 := by
      have a1 := mul_le_mul_of_nonneg_left hΛ (mul_nonneg hC.le ht)
      have a2 := mul_le_mul_of_nonneg_right hCC (mul_nonneg ht hΛ0)
      nlinarith
    have e2 : (1 + C * S45.power t S45.kappa) * (∑ i, y i ^ 2 / s.p i ^ 2) ≤
        (1 + C' * S45.power t S45.kappa) * (∑ i, y i ^ 2 / s.p i ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hsum
    linarith
  fourier := fun y hy => by
    have hp1 := power_nonneg_a2 (l1_nonneg_a2 y) (4 / 3)
    have hp2 := power_nonneg_a2 (l2sq_nonneg_a2 y) (1 / 3)
    refine max_le ((h.fourier y hy).trans ?_) ?_
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hp1) hp2
    · exact mul_nonneg (mul_nonneg (hC.le.trans hCC) hp1) hp2
  dual_fourier := fun y hy => by
    have hp1 := power_nonneg_a2 (l1_nonneg_a2 y) (4 / 3)
    have hp2 := power_nonneg_a2 (l2sq_nonneg_a2 y) (1 / 3)
    have ht : 0 ≤ t := h.scale.1.le
    have e : C * t * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) ≤
        C' * t * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC ht) hp1) hp2
    linarith [h.dual_fourier y hy]
  volume := h.volume.trans (mul_le_mul_of_nonneg_right hCC (power_nonneg_a2 h.scale.1.le _))

/-- **A2 (monitored increment bounds), approved input-constant-`2` form.** -/
theorem tileMonitorBounds2_proof : ∀ d (C : ℝ), 1 ≤ C → TileMonitorBoundsStatement2 d C := by
  intro d C hC
  obtain ⟨C_row, hC_row, t0_pre, ht0_pre, ht0_pre_le, hPF⟩ :=
    prestate_and_forms_of_slotSeq d C hC
  have hCpos : 0 < C := by linarith
  have hA : 0 ≤ 2 * C ^ 2 := by positivity
  have hB : 0 ≤ 2 * C ^ 4 * (1 + 4 * C) := by positivity
  obtain ⟨C4, hC4def⟩ : ∃ C4 : ℝ, C4 = 4 * C + C_row + 2 * C ^ 2 + 2 * C ^ 4 * (1 + 4 * C) + 2 :=
    ⟨_, rfl⟩
  have hC4_2 : 2 ≤ C4 := by rw [hC4def]; linarith
  have hC4_1 : 1 ≤ C4 := by linarith
  have hC4_pre : 4 * C ≤ C4 := by rw [hC4def]; linarith
  have hC4_row : C_row ≤ C4 := by rw [hC4def]; linarith
  have hC4_q : 2 * C ^ 2 ≤ C4 := by rw [hC4def]; linarith
  have hC4_d : 2 * C ^ 4 * (1 + 4 * C) ≤ C4 := by rw [hC4def]; linarith
  obtain ⟨Cfam, hCfam, tfam, htfam, hfam⟩ :=
    AgentS45.ordinary_increment_estimates_proof C4 hC4_1
  refine ⟨max Cfam 2, le_max_right _ _, min t0_pre tfam, lt_min ht0_pre htfam, ?_⟩
  intro m P j T M x hu hj hjm hM hab hx htsmall
  have htpre : sweepScale P.u m j < t0_pre := lt_of_lt_of_le htsmall (min_le_left _ _)
  have htf : sweepScale P.u m j < tfam := lt_of_lt_of_le htsmall (min_le_right _ _)
  have htpos : 0 < sweepScale P.u m j := sweepScale_pos_a2 (lt_trans (by norm_num) hu.1) m j
  have ht1 : sweepScale P.u m j ≤ 1 := (lt_of_lt_of_le htpre ht0_pre_le).le
  have hL := AgentS45.logFactor_pos htpos ht1
  have hFTp : ∀ (k : ℕ) (ω : RandomSources (Torus d m) M) (q : S45.Sequence (Port d m)),
      slotSeq P j T M x k ω = some q →
      (q.state q.length).live.Nonempty →
      ((q.state q.length).state (portR (sweepTheta P.u m j) x.r)).g.IsSymm ∧
      ∀ cols, FTHyp_a2 (sweepScale P.u m j) C4 Cfam
        ((q.state q.length).state (portR (sweepTheta P.u m j) x.r))
        (slotPorts_a2 P j T x (q.state q.length).live (tileRemaining P j T M k ω)) cols
        (fun a j_col => ((P.cover j).cover.coords T).B a.1 j_col) := by
    intro k ω q hq hne
    obtain ⟨u0, hu0⟩ := hne
    obtain ⟨Λ, hpre, hrow, hBq, hBd⟩ := hPF m P j T M x hu hj hjm hx htpre k ω q hq hu0
    refine ⟨hpre.symmetric, fun cols Ω _ μ _ ξ hmom => ?_⟩
    have hpre' := prestate_mono_a2 hpre (by linarith) hC4_pre
    refine hfam (q.state q.length).live (Fin (localDim P j T)) Ω μ (sweepScale P.u m j) _
      (fun y => max (Λ y) 0)
      (fun f => max (S45.qform (((q.state q.length).state
        (portR (sweepTheta P.u m j) x.r)).D (sweepScale P.u m j)) f) 0) _ _ cols _ ξ htf hpre'
      (hrow.trans (mul_le_mul_of_nonneg_right hC4_row hL.le)) hmom ?_ ?_ ?_
    · intro f
      exact (le_max_left _ _).trans (le_mul_of_one_le_left (le_max_right _ _) hC4_1)
    · intro v
      exact max_le ((hBq v).trans (mul_le_mul_of_nonneg_right hC4_q (l2sq_nonneg_a2 v)))
        (mul_nonneg (by linarith) (l2sq_nonneg_a2 v))
    · intro y hy
      refine (hBd y hy).trans (mul_le_mul_of_nonneg_right hC4_d ?_)
      have hp1 := power_nonneg_a2 (l1_nonneg_a2 y) (4 / 3)
      have hp2 := power_nonneg_a2 (l2sq_nonneg_a2 y) (1 / 3)
      have := l2sq_nonneg_a2 y
      have : 0 ≤ 4 * C * sweepScale P.u m j := by positivity
      positivity
  dsimp only
  refine ⟨fun k _ => tileRun_predictable P j T M x k,
    fun i k y => tileEval_stronglyMeasurable P j T M x i k y,
    fun i k ω y z => tileEval_isHermitian P j T M x i k ω y z, ?_, ?_, ?_⟩
  · intro i k _ ω hr
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hr : (slotSeq P j T M x k ω).isSome = true)
    exact (slot_bounds_a2 P j T M x C4 Cfam (max Cfam 2) hC4_2 hCfam (le_max_left _ _) htpos ht1
      k ω q hq (hFTp k ω q hq) i).1
  · intro i k _ ω hr
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hr : (slotSeq P j T M x k ω).isSome = true)
    exact (slot_bounds_a2 P j T M x C4 Cfam (max Cfam 2) hC4_2 hCfam (le_max_left _ _) htpos ht1
      k ω q hq (hFTp k ω q hq) i).2.1
  · intro i k _ ω hr
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hr : (slotSeq P j T M x k ω).isSome = true)
    exact (slot_bounds_a2 P j T M x C4 Cfam (max Cfam 2) hC4_2 hCfam (le_max_left _ _) htpos ht1
      k ω q hq (hFTp k ω q hq) i).2.2

end Main

end AndersonAC.AgentS78
