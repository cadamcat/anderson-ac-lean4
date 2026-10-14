import AndersonAC.S45.TrialInputsProof

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

section Kernel

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable (m μ) in
/-- The regular conditional law of `Y` given the sub-σ-algebra `m`. -/
def condLaw (Y : Ω → S) (ω : Ω) : Measure S :=
  @condDistrib Ω Ω S _ _ _ mΩ m Y id μ _ ω

theorem condLaw_isProb (Y : Ω → S) (ω : Ω) : IsProbabilityMeasure (condLaw m μ Y ω) := by
  unfold condLaw
  haveI : IsMarkovKernel (@condDistrib Ω Ω S _ _ _ mΩ m Y id μ _) := by infer_instance
  exact this.isProbabilityMeasure ω

theorem condExp_eq_integral_condLaw (hm : m ≤ mΩ) {Y : Ω → S} (hY : Measurable Y)
    {F : Ω × S → E} (hF : @StronglyMeasurable _ _ _ (m.prod inferInstance) F)
    (hint : Integrable (fun ω => F (ω, Y ω)) μ) :
    μ[fun ω => F (ω, Y ω) | m] =ᵐ[μ] fun ω => ∫ y, F (ω, y) ∂(condLaw m μ Y ω) := by
  have hX : @Measurable Ω Ω mΩ m id := fun s hs => hm s hs
  have h := @condExp_prod_ae_eq_integral_condDistrib Ω Ω S E _ _ _ _ mΩ μ _ id Y m F _ _ hX
    hY.aemeasurable hF hint
  rw [MeasurableSpace.comap_id] at h
  exact h

end Kernel

/-! ### Loewner order and integrals of matrices -/

section MatOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

instance matPosSMulMono : PosSMulMono ℝ (Matrix d d ℂ) :=
  ⟨fun a ha b₁ b₂ hb => by
    rw [Matrix.le_iff] at hb ⊢
    rw [← smul_sub]
    exact hb.smul ha⟩

instance matSMulPosMono : SMulPosMono ℝ (Matrix d d ℂ) :=
  ⟨fun b hb a₁ a₂ ha => by
    rw [Matrix.le_iff, sub_zero] at hb
    rw [Matrix.le_iff, ← sub_smul]
    exact hb.smul (sub_nonneg.2 ha)⟩

instance matIsOrderedModule : IsOrderedModule ℝ (Matrix d d ℂ) := {}

end MatOrder

/-! ### The conditional slot law at a fixed history -/

section SlotLaw

open scoped ENNReal

variable {n : ℕ}

/-- The normalized law of the scalar given the slot `x`. -/
def slotLaw (κ : Measure (Fin n × ℝ)) (rem : Finset (Fin n)) (x : Fin n) : Measure ℝ :=
  if x ∈ rem then ((rem.card : ℝ≥0∞) • (κ.restrict {y | y.1 = x}).map Prod.snd)
  else Measure.dirac 0

theorem measurableSet_slot (x : Fin n) : MeasurableSet {y : Fin n × ℝ | y.1 = x} :=
  measurable_fst (measurableSet_singleton x)

theorem integral_slotLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : Measure (Fin n × ℝ)) (rem : Finset (Fin n)) {x : Fin n} (hx : x ∈ rem)
    {g : ℝ → E} (hg : StronglyMeasurable g) :
    ∫ z, g z ∂slotLaw κ rem x = (rem.card : ℝ) • ∫ y, (if y.1 = x then g y.2 else 0) ∂κ := by
  simp only [slotLaw, if_pos hx]
  rw [integral_smul_measure, integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,
    ← integral_indicator (measurableSet_slot x)]
  simp only [ENNReal.toReal_natCast]
  congr 2
  funext y
  simp only [Set.indicator, Set.mem_setOf_eq]

/-- The conditional moment facts at one history. -/
structure SlotHyp (κ : Measure (Fin n × ℝ)) (rem : Finset (Fin n)) (t C : ℝ) : Prop where
  prob : IsProbabilityMeasure κ
  card : 0 < rem.card
  mass : ∀ x, ∫ y, (if y.1 = x then (1 : ℝ) else 0) ∂κ = if x ∈ rem then 1 / (rem.card : ℝ) else 0
  mean : ∀ x, ∫ y, (if y.1 = x then y.2 else 0) ∂κ = 0
  var : ∀ x, ∫ y, (if y.1 = x then y.2 ^ 2 else 0) ∂κ = if x ∈ rem then t / (rem.card : ℝ) else 0
  bdd : ∀ᵐ y ∂κ, |y.2| ≤ C * Real.sqrt t

namespace SlotHyp

variable {κ : Measure (Fin n × ℝ)} {rem : Finset (Fin n)} {t C : ℝ}

theorem real_slot (h : SlotHyp κ rem t C) (x : Fin n) :
    κ.real {y | y.1 = x} = if x ∈ rem then 1 / (rem.card : ℝ) else 0 := by
  haveI := h.prob
  rw [← h.mass x, ← integral_indicator_one (measurableSet_slot x)]
  congr 1
  funext y
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]

theorem slot_null (h : SlotHyp κ rem t C) {x : Fin n} (hx : x ∉ rem) :
    κ {y | y.1 = x} = 0 := by
  haveI := h.prob
  have := h.real_slot x
  rw [if_neg hx, measureReal_eq_zero_iff (measure_ne_top _ _)] at this
  exact this

theorem isProb (h : SlotHyp κ rem t C) (x : Fin n) : IsProbabilityMeasure (slotLaw κ rem x) := by
  haveI := h.prob
  by_cases hx : x ∈ rem
  · constructor
    simp only [slotLaw, if_pos hx]
    rw [Measure.smul_apply, Measure.map_apply measurable_snd MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hr := h.real_slot x
    rw [if_pos hx] at hr
    have hc : (0 : ℝ) < rem.card := by exact_mod_cast h.card
    rw [← ENNReal.ofReal_toReal (measure_ne_top κ {y : Fin n × ℝ | y.1 = x})]
    rw [show (κ {y : Fin n × ℝ | y.1 = x}).toReal = κ.real {y | y.1 = x} from rfl, hr,
      smul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [mul_one_div_cancel (ne_of_gt hc), ENNReal.ofReal_one]
  · simp only [slotLaw, if_neg hx]
    infer_instance

theorem ae_bdd (h : SlotHyp κ rem t C) {x : Fin n} (hx : x ∈ rem) :
    ∀ᵐ z ∂slotLaw κ rem x, |z| ≤ C * Real.sqrt t := by
  simp only [slotLaw, if_pos hx]
  refine Measure.ae_smul_measure ?_ _
  have hS : MeasurableSet {z : ℝ | |z| ≤ C * Real.sqrt t} :=
    measurableSet_le continuous_abs.measurable measurable_const
  rw [ae_map_iff measurable_snd.aemeasurable hS]
  exact ae_restrict_of_ae h.bdd

theorem momentLaw (h : SlotHyp κ rem t C) {x : Fin n} (hx : x ∈ rem) :
    MomentLaw (slotLaw κ rem x) t C id := by
  have hc : (0 : ℝ) < rem.card := by exact_mod_cast h.card
  refine ⟨measurable_id, ?_, ?_, ?_⟩
  · rw [integral_slotLaw κ rem hx stronglyMeasurable_id]
    simp only [id]
    rw [h.mean x, smul_zero]
  · rw [integral_slotLaw κ rem hx (by fun_prop : Continuous fun z : ℝ => (id z) ^ 2).stronglyMeasurable]
    simp only [id]
    rw [h.var x, if_pos hx, smul_eq_mul]
    field_simp
  · exact h.ae_bdd hx

theorem integral_decomp (h : SlotHyp κ rem t C) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (G : Fin n → ℝ → E) (hG : ∀ x, StronglyMeasurable (G x))
    (B : ℝ) (hGb : ∀ x ∈ rem, ∀ z, |z| ≤ C * Real.sqrt t → ‖G x z‖ ≤ B) :
    ∫ y, G y.1 y.2 ∂κ = (1 / (rem.card : ℝ)) • ∑ x ∈ rem, ∫ z, G x z ∂slotLaw κ rem x := by
  haveI := h.prob
  have hc : (0 : ℝ) < rem.card := by exact_mod_cast h.card
  have hsplit : (fun y : Fin n × ℝ => G y.1 y.2) =
      fun y => ∑ x, (if y.1 = x then G x y.2 else 0) := by
    funext y
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hpiece_meas : ∀ x, StronglyMeasurable (fun y : Fin n × ℝ => if y.1 = x then G x y.2 else 0) :=
    fun x => StronglyMeasurable.ite (measurableSet_slot x) ((hG x).comp_measurable measurable_snd)
      stronglyMeasurable_const
  have hzero : ∀ x, x ∉ rem → (fun y : Fin n × ℝ => if y.1 = x then G x y.2 else 0) =ᵐ[κ] 0 := by
    intro x hx
    have hnull := h.slot_null hx
    rw [measure_eq_zero_iff_ae_notMem] at hnull
    filter_upwards [hnull] with y hy
    have hy' : ¬ y.1 = x := hy
    simp only [hy', if_false, Pi.zero_apply]
  have hint : ∀ x, Integrable (fun y : Fin n × ℝ => if y.1 = x then G x y.2 else 0) κ := by
    intro x
    by_cases hx : x ∈ rem
    · refine Integrable.of_bound (hpiece_meas x).aestronglyMeasurable (max B 0) ?_
      filter_upwards [h.bdd] with y hy
      by_cases hyx : y.1 = x
      · rw [if_pos hyx]
        exact (hGb x hx y.2 hy).trans (le_max_left _ _)
      · rw [if_neg hyx, norm_zero]; exact le_max_right _ _
    · exact (integrable_zero _ _ κ).congr (hzero x hx).symm
  rw [hsplit, integral_finsetSum _ fun x _ => hint x]
  have hterm : ∀ x, ∫ y, (if y.1 = x then G x y.2 else 0) ∂κ =
      if x ∈ rem then (1 / (rem.card : ℝ)) • ∫ z, G x z ∂slotLaw κ rem x else 0 := by
    intro x
    by_cases hx : x ∈ rem
    · rw [if_pos hx, integral_slotLaw κ rem hx (hG x), smul_smul, one_div,
        inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    · rw [if_neg hx, integral_eq_zero_of_ae (hzero x hx)]
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.smul_sum]

end SlotHyp

theorem stack_integral {d : ℕ} (ρ : Fin n → Measure ℝ) [∀ x, IsProbabilityMeasure (ρ x)]
    (rem : Finset (Fin n)) (t C σ B : ℝ)
    (hb : ∀ x ∈ rem, ∀ᵐ z ∂ρ x, |z| ≤ C * Real.sqrt t)
    (G : Fin n → ℝ → CMat (Fin d)) (hG : ∀ x, StronglyMeasurable (G x))
    (hGb : ∀ x ∈ rem, ∀ z, |z| ≤ C * Real.sqrt t → ‖G x z‖ ≤ B)
    (hstack : ∀ z : Fin n → ℝ, (∀ x ∈ rem, |z x| ≤ C * Real.sqrt t) →
      (∑ x ∈ rem, G x (z x)) ≤ σ • (1 : CMat (Fin d))) :
    (∑ x ∈ rem, ∫ z, G x z ∂ρ x) ≤ σ • (1 : CMat (Fin d)) := by
  set ν := Measure.pi ρ with hνdef
  have hν1 : ∀ x ∈ rem, ∀ᵐ z ∂ν, |z x| ≤ C * Real.sqrt t := fun x hx =>
    (measurePreserving_eval ρ x).quasiMeasurePreserving.ae (hb x hx)
  have hν : ∀ᵐ z ∂ν, ∀ x ∈ rem, |z x| ≤ C * Real.sqrt t := by
    have : ∀ᵐ z ∂ν, ∀ x : Fin n, x ∈ rem → |z x| ≤ C * Real.sqrt t :=
      ae_all_iff.2 fun x => by
        by_cases hx : x ∈ rem
        · exact (hν1 x hx).mono fun z hz _ => hz
        · exact ae_of_all _ fun z h => absurd h hx
    exact this
  have hint : ∀ x ∈ rem, Integrable (fun z : Fin n → ℝ => G x (z x)) ν := by
    intro x hx
    refine Integrable.of_bound ((hG x).comp_measurable (measurable_pi_apply x)).aestronglyMeasurable
      B ?_
    filter_upwards [hν1 x hx] with z hz
    exact hGb x hx (z x) hz
  have e1 : (∑ x ∈ rem, ∫ z, G x z ∂ρ x) = ∫ z, ∑ x ∈ rem, G x (z x) ∂ν := by
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (integral_comp_eval (hG x).aestronglyMeasurable).symm
  rw [e1]
  calc ∫ z, ∑ x ∈ rem, G x (z x) ∂ν ≤ ∫ _z, σ • (1 : CMat (Fin d)) ∂ν :=
        integral_mono_ae (integrable_finsetSum _ hint) (integrable_const _)
          (hν.mono fun z hz => hstack z hz)
    _ = σ • (1 : CMat (Fin d)) := by
        rw [integral_const]; simp

end SlotLaw

/-! ### Conditional slot laws from `UniformSlotLaw` -/

section Uniform

set_option linter.unusedSectionVars false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {n M : ℕ} {t C : ℝ} {run : ℕ → Ω → Bool}
  {remaining : ℕ → Ω → Finset (Fin n)} {slot : ℕ → Ω → Fin n} {ξ : ℕ → Ω → ℝ}

/-- The pair (slot, scalar) at step `k`. -/
def pairY (slot : ℕ → Ω → Fin n) (ξ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : Fin n × ℝ :=
  (slot k ω, ξ k ω)

theorem measurableSet_run (hlaw : UniformSlotLaw μ ℱ M t C run remaining slot ξ) {k : ℕ}
    (hk : k < M) : MeasurableSet[ℱ k] {ω | run k ω = true} := by
  have h := hlaw.run_predictable k hk
  exact h (show MeasurableSet[⊤] ({true} : Set Bool) from MeasurableSpace.measurableSet_top)

theorem measurable_pairY (hlaw : UniformSlotLaw μ ℱ M t C run remaining slot ξ) {k : ℕ}
    (hk : k < M) : @Measurable Ω (Fin n × ℝ) (ℱ (k + 1)) _ (pairY slot ξ k) :=
  (hlaw.slot_adapted k hk).prodMk (hlaw.scalar_adapted k hk)

/-- Kernel form of a conditional-expectation identity. -/
theorem kernel_ae_of_condExp [Nonempty (Fin n)]
    (hlaw : UniformSlotLaw μ ℱ M t C run remaining slot ξ) {k : ℕ} (hk : k < M)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Ω × (Fin n × ℝ) → E}
    (hF : @StronglyMeasurable _ _ _ ((ℱ k : MeasurableSpace Ω).prod inferInstance) F)
    (hint : Integrable (fun ω => F (ω, pairY slot ξ k ω)) μ) {g : Ω → E}
    (hg : μ[fun ω => F (ω, pairY slot ξ k ω) | ℱ k] =ᵐ[μ] g) :
    ∀ᵐ ω ∂μ, ∫ y, F (ω, y) ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) = g ω := by
  have hY : Measurable (pairY slot ξ k) := (measurable_pairY hlaw hk).mono (ℱ.le _) le_rfl
  have h := condExp_eq_integral_condLaw (m := ℱ k) (μ := μ) (ℱ.le k) hY hF hint
  filter_upwards [h, hg] with ω h1 h2
  rw [← h1, h2]

theorem measurable_graph (hlaw : UniformSlotLaw μ ℱ M t C run remaining slot ξ) {k : ℕ}
    (hk : k < M) : @Measurable Ω (Ω × (Fin n × ℝ)) mΩ ((ℱ k : MeasurableSpace Ω).prod inferInstance)
      (fun ω => (ω, pairY slot ξ k ω)) := by
  have h1 : @Measurable Ω Ω mΩ (ℱ k) id := fun s hs => ℱ.le k s hs
  have h2 : Measurable (pairY slot ξ k) := (measurable_pairY hlaw hk).mono (ℱ.le _) le_rfl
  exact h1.prodMk h2

theorem slotHyp_ae [Nonempty (Fin n)] (hlaw : UniformSlotLaw μ ℱ M t C run remaining slot ξ)
    {k : ℕ} (hk : k < M) :
    ∀ᵐ ω ∂μ, run k ω = true →
      SlotHyp (condLaw (ℱ k) μ (pairY slot ξ k) ω) (remaining k ω) t C := by
  have hR := measurableSet_run hlaw hk
  have hgr := measurable_graph hlaw hk
  set m : MeasurableSpace (Ω × (Fin n × ℝ)) := (ℱ k : MeasurableSpace Ω).prod inferInstance
    with hmdef
  have hS : ∀ x : Fin n, MeasurableSet[m] {p : Ω × (Fin n × ℝ) | run k p.1 = true ∧ p.2.1 = x} :=
    fun x => hR.prod (measurableSet_slot x)
  have hsnd : @Measurable _ ℝ m _ (fun p : Ω × (Fin n × ℝ) => p.2.2) :=
    @Measurable.snd _ _ _ m _ _ _ (@measurable_snd Ω (Fin n × ℝ) (ℱ k) _)
  have hbd := hlaw.bounded k hk
  -- mass
  have hmass : ∀ x : Fin n, ∀ᵐ ω ∂μ,
      ∫ y, (if run k ω = true ∧ y.1 = x then (1 : ℝ) else 0)
        ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) =
      if run k ω = true ∧ x ∈ remaining k ω then 1 / ((remaining k ω).card : ℝ) else 0 := by
    intro x
    refine kernel_ae_of_condExp (F := fun p => if run k p.1 = true ∧ p.2.1 = x then (1 : ℝ) else 0)
      hlaw hk (StronglyMeasurable.ite (hS x) stronglyMeasurable_const
        stronglyMeasurable_const) ?_ (hlaw.uniform k hk x)
    refine Integrable.of_bound ((StronglyMeasurable.ite (hS x)
      stronglyMeasurable_const stronglyMeasurable_const).comp_measurable hgr).aestronglyMeasurable
      1 (ae_of_all _ fun ω => ?_)
    split_ifs <;> simp
  -- mean
  have hmean : ∀ x : Fin n, ∀ᵐ ω ∂μ,
      ∫ y, (if run k ω = true ∧ y.1 = x then y.2 else 0)
        ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) = 0 := by
    intro x
    have hF : @StronglyMeasurable _ ℝ _ m
        (fun p : Ω × (Fin n × ℝ) => if run k p.1 = true ∧ p.2.1 = x then p.2.2 else 0) :=
      StronglyMeasurable.ite (hS x) hsnd.stronglyMeasurable stronglyMeasurable_const
    refine kernel_ae_of_condExp hlaw hk hF ?_ (hlaw.mean k hk x)
    refine Integrable.of_bound (hF.comp_measurable hgr).aestronglyMeasurable
      (max (C * Real.sqrt t) 0) ?_
    filter_upwards [hbd] with ω hω
    show ‖(if run k ω = true ∧ slot k ω = x then ξ k ω else 0)‖ ≤ _
    split
    next h => rw [Real.norm_eq_abs]; exact (hω h.1).trans (le_max_left _ _)
    next => simp
  -- variance
  have hvar : ∀ x : Fin n, ∀ᵐ ω ∂μ,
      ∫ y, (if run k ω = true ∧ y.1 = x then y.2 ^ 2 else 0)
        ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) =
      if run k ω = true ∧ x ∈ remaining k ω then t / ((remaining k ω).card : ℝ) else 0 := by
    intro x
    have hF : @StronglyMeasurable _ ℝ _ m
        (fun p : Ω × (Fin n × ℝ) => if run k p.1 = true ∧ p.2.1 = x then p.2.2 ^ 2 else 0) :=
      StronglyMeasurable.ite (hS x) (hsnd.pow_const 2).stronglyMeasurable
        stronglyMeasurable_const
    refine kernel_ae_of_condExp hlaw hk hF ?_ (hlaw.variance k hk x)
    refine Integrable.of_bound (hF.comp_measurable hgr).aestronglyMeasurable
      (max (C * Real.sqrt t) 0 ^ 2) ?_
    filter_upwards [hbd] with ω hω
    show ‖(if run k ω = true ∧ slot k ω = x then ξ k ω ^ 2 else 0)‖ ≤ _
    split
    next h =>
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((hω h.1).trans (le_max_left _ _)) 2
    next => simp
  -- boundedness
  have hbig : ∀ᵐ ω ∂μ,
      ∫ y, (if run k ω = true ∧ C * Real.sqrt t < |y.2| then (1 : ℝ) else 0)
        ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) = 0 := by
    have hSb : MeasurableSet[m]
        {p : Ω × (Fin n × ℝ) | run k p.1 = true ∧ C * Real.sqrt t < |p.2.2|} :=
      hR.prod (measurable_snd (measurableSet_lt measurable_const continuous_abs.measurable))
    have hF : @StronglyMeasurable _ ℝ _ m
        (fun p : Ω × (Fin n × ℝ) =>
          if run k p.1 = true ∧ C * Real.sqrt t < |p.2.2| then (1 : ℝ) else 0) :=
      StronglyMeasurable.ite hSb stronglyMeasurable_const stronglyMeasurable_const
    have hz : (fun ω => (fun p : Ω × (Fin n × ℝ) =>
        if run k p.1 = true ∧ C * Real.sqrt t < |p.2.2| then (1 : ℝ) else 0)
          (ω, pairY slot ξ k ω)) =ᵐ[μ] 0 := by
      filter_upwards [hbd] with ω hω
      show (if run k ω = true ∧ C * Real.sqrt t < |ξ k ω| then (1 : ℝ) else 0) = 0
      split
      next h => exact absurd (hω h.1) (not_le.2 h.2)
      next => rfl
    have hint : Integrable (fun ω => (fun p : Ω × (Fin n × ℝ) =>
        if run k p.1 = true ∧ C * Real.sqrt t < |p.2.2| then (1 : ℝ) else 0)
          (ω, pairY slot ξ k ω)) μ := (integrable_zero _ _ μ).congr hz.symm
    have hg : μ[fun ω => (fun p : Ω × (Fin n × ℝ) =>
        if run k p.1 = true ∧ C * Real.sqrt t < |p.2.2| then (1 : ℝ) else 0)
          (ω, pairY slot ξ k ω) | ℱ k] =ᵐ[μ] (0 : Ω → ℝ) := by
      refine (condExp_congr_ae hz).trans ?_
      rw [condExp_zero]
    exact kernel_ae_of_condExp hlaw hk hF hint hg
  filter_upwards [ae_all_iff.2 hmass, ae_all_iff.2 hmean, ae_all_iff.2 hvar, hbig] with
    ω h1 h2 h3 h4 hrun
  haveI hprob : IsProbabilityMeasure (condLaw (ℱ k) μ (pairY slot ξ k) ω) := condLaw_isProb _ _
  refine ⟨hprob, ?_, fun x => ?_, fun x => ?_, fun x => ?_, ?_⟩
  · exact Finset.card_pos.2 (hlaw.nonempty k hk ω hrun)
  · have := h1 x
    simp only [hrun, true_and] at this
    exact this
  · have := h2 x
    simp only [hrun, true_and] at this
    exact this
  · have := h3 x
    simp only [hrun, true_and] at this
    exact this
  · have h4' := h4
    simp only [hrun, true_and] at h4'
    have hset : MeasurableSet {y : Fin n × ℝ | C * Real.sqrt t < |y.2|} :=
      measurable_snd (measurableSet_lt measurable_const continuous_abs.measurable)
    have e : (fun y : Fin n × ℝ => if C * Real.sqrt t < |y.2| then (1 : ℝ) else 0) =
        Set.indicator {y : Fin n × ℝ | C * Real.sqrt t < |y.2|} 1 := by
      funext y; simp [Set.indicator]
    rw [e, integral_indicator_one hset, measureReal_eq_zero_iff (measure_ne_top _ _)] at h4'
    rw [ae_iff]
    simpa [not_le] using h4'

theorem slot_mem_ae (hlaw : UniformSlotLaw μ ℱ M t C run remaining slot ξ) {k : ℕ}
    (hk : k < M) : ∀ᵐ ω ∂μ, run k ω = true → slot k ω ∈ remaining k ω := by
  have hx : ∀ x : Fin n, ∀ᵐ ω ∂μ, x ∉ remaining k ω → ¬ (run k ω = true ∧ slot k ω = x) := by
    intro x
    set f : Ω → ℝ := fun ω => if run k ω = true ∧ slot k ω = x then 1 else 0 with hfdef
    have hA : MeasurableSet[ℱ k] {ω | x ∉ remaining k ω} :=
      hlaw.remaining_measurable k hk
        (show MeasurableSet[⊤] {s : Finset (Fin n) | x ∉ s} from MeasurableSpace.measurableSet_top)
    have hA' : MeasurableSet {ω | x ∉ remaining k ω} := ℱ.le k _ hA
    have hfm : StronglyMeasurable f := by
      have hR : MeasurableSet {ω | run k ω = true ∧ slot k ω = x} := by
        have h1 := (measurableSet_run hlaw hk)
        have h2 : MeasurableSet[ℱ (k + 1)] {ω | slot k ω = x} :=
          hlaw.slot_adapted k hk (show MeasurableSet[⊤] ({x} : Set (Fin n)) from
            MeasurableSpace.measurableSet_top)
        exact (ℱ.le k _ h1).inter (ℱ.le (k + 1) _ h2)
      exact StronglyMeasurable.ite hR stronglyMeasurable_const stronglyMeasurable_const
    have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simp only [hfdef]; split <;> simp)
    have hint : ∫ ω in {ω | x ∉ remaining k ω}, f ω ∂μ = 0 := by
      rw [← setIntegral_condExp (ℱ.le k) hfi hA]
      refine integral_eq_zero_of_ae ?_
      rw [EventuallyEq, ae_restrict_iff' hA']
      filter_upwards [hlaw.uniform k hk x] with ω hω hmem
      rw [hω]
      have hmem' : x ∉ remaining k ω := hmem
      simp [hmem']
    have hnn : 0 ≤ᵐ[μ.restrict {ω | x ∉ remaining k ω}] f :=
      ae_of_all _ fun ω => by simp only [hfdef, Pi.zero_apply]; split <;> simp
    have h0 := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hfi.integrableOn).1 hint
    rw [EventuallyEq, ae_restrict_iff' hA'] at h0
    filter_upwards [h0] with ω hω hmem hc
    have := hω hmem
    simp only [hfdef, Pi.zero_apply, if_pos hc] at this
    exact one_ne_zero this
  filter_upwards [ae_all_iff.2 hx] with ω hω hrun
  by_contra hc
  exact hω (slot k ω) hc ⟨hrun, rfl⟩

end Uniform

/-! ### `ordered_raw_bounds` -/

/-- The raw ordered increments. -/
def rawOf {Ω : Type*} {n s M : ℕ} {dim : Fin s → ℕ} (run : ℕ → Ω → Bool)
    (slot : ℕ → Ω → Fin n) (ξ : ℕ → Ω → ℝ)
    (eval : ∀ i : Fin s, ℕ → Ω → Fin n → ℝ → CMat (Fin (dim i))) (i : Fin s) :
    ℕ → Ω → CMat (Fin (dim i))
  | 0 => fun _ => 0
  | k + 1 => fun ω => if k < M ∧ run k ω = true then eval i k ω (slot k ω) (ξ k ω) else 0

theorem ordered_raw_bounds_proof {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (n s M : ℕ) (t C : ℝ) (kind : Fin s → MonitorKind) (dim : Fin s → ℕ)
    (run : ℕ → Ω → Bool) (remaining : ℕ → Ω → Finset (Fin n))
    (slot : ℕ → Ω → Fin n) (ξ : ℕ → Ω → ℝ)
    (eval : ∀ i : Fin s, ℕ → Ω → Fin n → ℝ → CMat (Fin (dim i)))
    (hscale : 0 < t ∧ t < 1) (hC : 1 ≤ C)
    (hlaw : UniformSlotLaw μ ℱ M t C run remaining slot ξ)
    (hcount : ∀ k < M, ∀ ω, run k ω = true → (remaining k ω).card = M - k)
    (hmeas : ∀ i k x, @StronglyMeasurable (Ω × ℝ) (CMat (Fin (dim i))) _
      ((ℱ k).prod (borel ℝ)) (fun a => eval i k a.1 x a.2))
    (hherm : ∀ i k ω x z, (eval i k ω x z).IsHermitian)
    (hmean : ∀ i k, k < M → ∀ ω, run k ω = true →
      ∀ (ρ : Fin n → Measure ℝ), (∀ x, IsProbabilityMeasure (ρ x)) →
      (∀ x ∈ remaining k ω, MomentLaw (ρ x) t C id) →
      ‖∑ x ∈ remaining k ω, ∫ z, eval i k ω x z ∂(ρ x)‖ ≤
        C * monitorBias t (kind i) / logFactor t)
    (hstack : ∀ i k, k < M → ∀ ω, run k ω = true → ∀ z : Fin n → ℝ,
      (∀ x ∈ remaining k ω, |z x| ≤ C * Real.sqrt t) →
      (∑ x ∈ remaining k ω, (eval i k ω x (z x))^2) ≤
        (C * monitorVariance t (kind i) / logFactor t) • (1 : CMat (Fin (dim i))))
    (hjump : ∀ i k, k < M → ∀ ω, run k ω = true → ∀ x ∈ remaining k ω,
      ∀ z, |z| ≤ C * Real.sqrt t → ‖eval i k ω x z‖ ≤ C * monitorJump t (kind i)) :
    ∃ a : OrderedRawBounds μ ℱ s M t C,
      a.kind = kind ∧ a.dimension = dim ∧
      ∀ i k ω, HEq (a.raw i (k + 1) ω)
        (if k < M ∧ run k ω = true then eval i k ω (slot k ω) (ξ k ω) else 0) := by
  obtain ⟨ht, ht1⟩ := hscale
  have hC0 : 0 < C := by linarith
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  haveI : Nonempty (Fin n) := ⟨slot 0 (Classical.arbitrary Ω)⟩
  have hL := logFactor_pos ht ht1.le
  have hmon := fun i => monitor_nonneg ht ht1.le (kind i)
  have hJ0 : ∀ i, 0 ≤ C * monitorJump t (kind i) := fun i => mul_nonneg hC0.le (hmon i).1
  -- the joint integrands
  let F : ∀ i, ℕ → Ω × (Fin n × ℝ) → CMat (Fin (dim i)) := fun i k p =>
    if run k p.1 = true then eval i k p.1 p.2.1 p.2.2 else 0
  have hFsm : ∀ i k, k < M →
      @StronglyMeasurable _ _ _ ((ℱ k : MeasurableSpace Ω).prod inferInstance) (F i k) := by
    intro i k hk
    set m : MeasurableSpace (Ω × (Fin n × ℝ)) := (ℱ k : MeasurableSpace Ω).prod inferInstance
    have hproj : @Measurable (Ω × (Fin n × ℝ)) (Ω × ℝ) m ((ℱ k : MeasurableSpace Ω).prod (borel ℝ))
        (fun p => (p.1, p.2.2)) := by
      have h1 : @Measurable (Ω × (Fin n × ℝ)) Ω m (ℱ k) Prod.fst :=
        @measurable_fst Ω (Fin n × ℝ) (ℱ k) _
      have h2 : @Measurable (Ω × (Fin n × ℝ)) ℝ m (borel ℝ) (fun p => p.2.2) :=
        (@measurable_snd Ω (Fin n × ℝ) (ℱ k) _).snd
      exact h1.prodMk h2
    have hE : @StronglyMeasurable _ _ _ m (fun p : Ω × (Fin n × ℝ) => eval i k p.1 p.2.1 p.2.2) := by
      have hsum : (fun p : Ω × (Fin n × ℝ) => eval i k p.1 p.2.1 p.2.2) =
          fun p => ∑ x, (if p.2.1 = x then eval i k p.1 x p.2.2 else 0) := by
        funext p; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      rw [hsum]
      refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
      have hset : MeasurableSet[m] {p : Ω × (Fin n × ℝ) | p.2.1 = x} :=
        (@measurable_snd Ω (Fin n × ℝ) (ℱ k) _).fst (measurableSet_singleton x)
      exact StronglyMeasurable.ite hset ((hmeas i k x).comp_measurable hproj)
        stronglyMeasurable_const
    have hR : MeasurableSet[m] {p : Ω × (Fin n × ℝ) | run k p.1 = true} :=
      (@measurable_fst Ω (Fin n × ℝ) (ℱ k) _) (measurableSet_run hlaw hk)
    exact StronglyMeasurable.ite hR hE stronglyMeasurable_const
  have hraw : ∀ i k, k < M → rawOf (M := M) run slot ξ eval i (k + 1) =
      fun ω => F i k (ω, pairY slot ξ k ω) := by
    intro i k hk; funext ω; simp [rawOf, F, pairY, hk]
  have hraw0 : ∀ i k, ¬ k < M → rawOf (M := M) run slot ξ eval i (k + 1) = fun _ => 0 := by
    intro i k hk; funext ω; simp [rawOf, hk]
  -- adaptedness
  have hadapt : ∀ i k, StronglyMeasurable[ℱ k] (rawOf (M := M) run slot ξ eval i k) := by
    intro i k
    cases k with
    | zero => exact stronglyMeasurable_const
    | succ k =>
      by_cases hk : k < M
      · rw [hraw i k hk]
        have hg : @Measurable Ω (Ω × (Fin n × ℝ)) (ℱ (k + 1))
            ((ℱ k : MeasurableSpace Ω).prod inferInstance) (fun ω => (ω, pairY slot ξ k ω)) := by
          have h1 : @Measurable Ω Ω (ℱ (k + 1)) (ℱ k) id :=
            fun s hs => ℱ.mono (Nat.le_succ k) s hs
          exact h1.prodMk (measurable_pairY hlaw hk)
        exact (hFsm i k hk).comp_measurable hg
      · rw [hraw0 i k hk]; exact stronglyMeasurable_const
  -- jumps
  have hjumpae : ∀ i k, ∀ᵐ ω ∂μ,
      ‖rawOf (M := M) run slot ξ eval i (k + 1) ω‖ ≤ C * monitorJump t (kind i) := by
    intro i k
    by_cases hk : k < M
    · filter_upwards [slot_mem_ae hlaw hk, hlaw.bounded k hk] with ω h1 h2
      simp only [rawOf, hk, true_and]
      split
      next hr => exact hjump i k hk ω hr _ (h1 hr) _ (h2 hr)
      next => rw [norm_zero]; exact hJ0 i
    · exact ae_of_all _ fun ω => by rw [hraw0 i k hk, norm_zero]; exact hJ0 i
  have hint : ∀ i k, Integrable (rawOf (M := M) run slot ξ eval i (k + 1)) μ := fun i k =>
    Integrable.of_bound (((hadapt i (k + 1)).mono (ℱ.le _)).aestronglyMeasurable) _ (hjumpae i k)
  have hint2 : ∀ i k, Integrable (fun ω => (rawOf (M := M) run slot ξ eval i (k + 1) ω) ^ 2) μ := by
    intro i k
    refine Integrable.of_bound ((((hadapt i (k + 1)).mono (ℱ.le _)).pow 2).aestronglyMeasurable)
      ((C * monitorJump t (kind i)) ^ 2) ?_
    filter_upwards [hjumpae i k] with ω hω
    have h2 : ‖(rawOf (M := M) run slot ξ eval i (k + 1) ω) ^ 2‖ ≤
        ‖rawOf (M := M) run slot ξ eval i (k + 1) ω‖ ^ 2 := by
      rw [pow_two, pow_two]; exact norm_mul_le _ _
    exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) hω 2)
  refine ⟨{ kind := kind
            dimension := dim
            raw := rawOf (M := M) run slot ξ eval
            adapted := fun i k => hadapt i k
            measurable := fun i k => ((hadapt i k).mono (ℱ.le k)).aestronglyMeasurable
            hermitian := fun i k => ae_of_all _ fun ω => ?_
            finite_horizon := fun i k hk ω => ?_
            jump := hjumpae
            mean := fun i k hk => ?_
            square := fun i k hk => ?_ }, rfl, rfl, fun i k ω => ?_⟩
  · simp only [rawOf]
    split
    · exact hherm _ _ _ _ _
    · exact isHermitian_zero
  · rw [hraw0 i k (not_lt.2 hk)]
  · -- mean
    have hY : Measurable (pairY slot ξ k) := (measurable_pairY hlaw hk).mono (ℱ.le _) le_rfl
    have hce := condExp_eq_integral_condLaw (m := ℱ k) (μ := μ) (ℱ.le k) hY (hFsm i k hk)
      (by rw [← hraw i k hk]; exact hint i k)
    rw [hraw i k hk]
    filter_upwards [hce, slotHyp_ae hlaw hk] with ω h1 h2
    rw [h1]
    have hrhs : 0 ≤ C * monitorBias t (kind i) / logFactor t / ((M - k : ℕ) : ℝ) := by
      have := (hmon i).2.2; positivity
    by_cases hr : run k ω = true
    · have hS := h2 hr
      have hGsm : ∀ x, StronglyMeasurable (fun z => eval i k ω x z) := fun x => by
        have hz : @Measurable ℝ (Ω × ℝ) _ ((ℱ k : MeasurableSpace Ω).prod (borel ℝ))
            (fun z => (ω, z)) := by
          have h1 : @Measurable ℝ Ω _ (ℱ k) (fun _ => ω) := measurable_const
          have h2 : @Measurable ℝ ℝ _ (borel ℝ) (fun z => z) := measurable_id
          exact h1.prodMk h2
        exact (hmeas i k x).comp_measurable hz
      have e1 : ∫ y, F i k (ω, y) ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) =
          ∫ y, eval i k ω y.1 y.2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) := by
        congr 1; funext y; simp [F, hr]
      rw [e1, hS.integral_decomp (fun x z => eval i k ω x z) hGsm (C * monitorJump t (kind i))
        (fun x hx z hz => hjump i k hk ω hr x hx z hz)]
      have hm := hmean i k hk ω hr (slotLaw (condLaw (ℱ k) μ (pairY slot ξ k) ω) (remaining k ω))
        hS.isProb (fun x hx => hS.momentLaw hx)
      rw [norm_smul, Real.norm_eq_abs, hcount k hk ω hr]
      have hc : (0 : ℝ) < ((M - k : ℕ) : ℝ) := by
        have := hcount k hk ω hr ▸ hS.card
        exact_mod_cast this
      rw [abs_of_nonneg (by positivity), one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hm hc.le
    · have e1 : ∫ y, F i k (ω, y) ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) = 0 := by
        simp [F, hr]
      rw [e1, norm_zero]; exact hrhs
  · -- square
    have hY : Measurable (pairY slot ξ k) := (measurable_pairY hlaw hk).mono (ℱ.le _) le_rfl
    have hF2 : @StronglyMeasurable _ _ _ ((ℱ k : MeasurableSpace Ω).prod inferInstance)
        (fun p => (F i k p) ^ 2) := (hFsm i k hk).pow 2
    have hce := condExp_eq_integral_condLaw (m := ℱ k) (μ := μ) (ℱ.le k) hY hF2
      (by
        have := hint2 i k
        rw [hraw i k hk] at this
        exact this)
    rw [hraw i k hk]
    filter_upwards [hce, slotHyp_ae hlaw hk] with ω h1 h2
    rw [h1]
    set σ := C * monitorVariance t (kind i) / logFactor t with hσdef
    have hσ : 0 ≤ σ := by have := (hmon i).2.1; positivity
    by_cases hr : run k ω = true
    · have hS := h2 hr
      have hGsm : ∀ x, StronglyMeasurable (fun z => (eval i k ω x z) ^ 2) := fun x => by
        have hz : @Measurable ℝ (Ω × ℝ) _ ((ℱ k : MeasurableSpace Ω).prod (borel ℝ))
            (fun z => (ω, z)) := by
          have h1 : @Measurable ℝ Ω _ (ℱ k) (fun _ => ω) := measurable_const
          have h2 : @Measurable ℝ ℝ _ (borel ℝ) (fun z => z) := measurable_id
          exact h1.prodMk h2
        exact ((hmeas i k x).comp_measurable hz).pow 2
      have hbd2 : ∀ x ∈ remaining k ω, ∀ z, |z| ≤ C * Real.sqrt t →
          ‖(eval i k ω x z) ^ 2‖ ≤ (C * monitorJump t (kind i)) ^ 2 := by
        intro x hx z hz
        have h := hjump i k hk ω hr x hx z hz
        have h2 : ‖(eval i k ω x z) ^ 2‖ ≤ ‖eval i k ω x z‖ ^ 2 := by
          rw [pow_two, pow_two]; exact norm_mul_le _ _
        exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) h 2)
      have e1 : ∫ y, (F i k (ω, y)) ^ 2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) =
          ∫ y, (eval i k ω y.1 y.2) ^ 2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) := by
        congr 1; funext y; simp [F, hr]
      rw [e1, hS.integral_decomp (fun x z => (eval i k ω x z) ^ 2) hGsm _ hbd2]
      have hst := @stack_integral n (dim i) (slotLaw (condLaw (ℱ k) μ (pairY slot ξ k) ω)
        (remaining k ω)) (fun x => hS.isProb x) (remaining k ω) t C σ _
        (fun x hx => hS.ae_bdd hx) (fun x z => (eval i k ω x z) ^ 2) hGsm hbd2
        (fun z hz => hstack i k hk ω hr z hz)
      have hc : (0 : ℝ) < ((M - k : ℕ) : ℝ) := by
        have := hcount k hk ω hr ▸ hS.card
        exact_mod_cast this
      have hmono := smul_le_smul_of_nonneg_left hst
        (by positivity : (0 : ℝ) ≤ 1 / ((remaining k ω).card : ℝ))
      refine hmono.trans (le_of_eq ?_)
      rw [smul_smul, hcount k hk ω hr, one_div_mul_eq_div]
    · have e1 : ∫ y, (F i k (ω, y)) ^ 2 ∂(condLaw (ℱ k) μ (pairY slot ξ k) ω) = 0 := by
        simp [F, hr]
      rw [e1, Matrix.nonneg_iff_posSemidef]
      have hc : (0 : ℝ) ≤ σ / ((M - k : ℕ) : ℝ) := by positivity
      exact Matrix.PosSemidef.one.smul hc
  · exact HEq.rfl

end AndersonAC.AgentS45
