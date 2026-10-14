import AndersonAC.AgentS78.Construction.Freezing

/-!
# Independence of events on disjoint source coordinates

agent-s78retry (2026-10-14), for `tileRetry_of_trialBound` (TileTrialRetry.lean).
Paper: 05-local-sweeps.tex:940–961 (successive retries read new independent permutations and
fresh auxiliary families).

The source law `sourcesLaw ι M` is a product of independent coordinates (signs and orders).
* `iIndep_coord`: the coordinate σ-algebras are independent.
* `measure_inter_of_depOn`: two measurable events, each decided by its own set of coordinates,
  the two sets disjoint, are independent.
* `measurePreserving_relabel`: relabelling the coordinates by a permutation of the sign
  indices and a permutation of the order indices that preserves the order sizes preserves
  `sourcesLaw`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace AndersonAC.AgentS78.Retry

open AndersonAC.S2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

/-- Coordinates of the source space: sign indices and order indices. -/
abbrev Coord (ι : Type) := SignIndex ι ⊕ ℕ

/-- The σ-algebra of one coordinate. -/
def coordSpace (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) :
    Coord ι → MeasurableSpace (RandomSources ι M)
  | Sum.inl z => MeasurableSpace.comap (fun ω : RandomSources ι M => ω.1 z) inferInstance
  | Sum.inr o => MeasurableSpace.comap (fun ω : RandomSources ι M => ω.2 o) inferInstance

theorem measurable_sign (z : SignIndex ι) :
    Measurable (fun ω : RandomSources ι M => ω.1 z) :=
  (measurable_pi_apply z).comp measurable_fst

theorem measurable_order (o : ℕ) :
    Measurable (fun ω : RandomSources ι M => ω.2 o) :=
  (measurable_pi_apply o).comp measurable_snd

theorem coordSpace_le (i : Coord ι) :
    coordSpace ι M i ≤ (inferInstance : MeasurableSpace (RandomSources ι M)) := by
  cases i with
  | inl z => exact (measurable_sign z).comap_le
  | inr o => exact (measurable_order o).comap_le

theorem preimage_image_of_comap {α β : Type} [MeasurableSpace β] (g : α → β) (A : Set α)
    (hA : MeasurableSet[MeasurableSpace.comap g inferInstance] A) : g ⁻¹' (g '' A) = A := by
  obtain ⟨t, -, rfl⟩ := hA
  ext ω
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨ω', hω', he⟩; rw [← he]; exact hω'
  · intro h; exact ⟨ω, h, rfl⟩

theorem signsLaw_eval (z : SignIndex ι) (t : Set Bool) :
    signsLaw ι (Function.eval z ⁻¹' t) = (PMF.uniformOfFintype Bool).toMeasure t := by
  unfold signsLaw
  rw [← Measure.map_apply (measurable_pi_apply z) (MeasurableSpace.measurableSet_top),
    (measurePreserving_eval_infinitePi _ z).map_eq]

theorem ordersLaw_eval (o : ℕ) (t : Set (Order (M o))) :
    ordersLaw M (Function.eval o ⁻¹' t) = (PMF.uniformOfFintype (Order (M o))).toMeasure t := by
  unfold ordersLaw
  rw [← Measure.map_apply (measurable_pi_apply o) (MeasurableSpace.measurableSet_top),
    (measurePreserving_eval_infinitePi _ o).map_eq]

theorem sourcesLaw_sign (z : SignIndex ι) (t : Set Bool) :
    sourcesLaw ι M ((fun ω : RandomSources ι M => ω.1 z) ⁻¹' t) =
      (PMF.uniformOfFintype Bool).toMeasure t := by
  have : (fun ω : RandomSources ι M => ω.1 z) ⁻¹' t =
      (Function.eval z ⁻¹' t) ×ˢ (Set.univ : Set ((o : ℕ) → Order (M o))) := by
    ext ω; simp
  rw [this, sourcesLaw, Measure.prod_prod, measure_univ, mul_one, signsLaw_eval]

theorem sourcesLaw_order (o : ℕ) (t : Set (Order (M o))) :
    sourcesLaw ι M ((fun ω : RandomSources ι M => ω.2 o) ⁻¹' t) =
      (PMF.uniformOfFintype (Order (M o))).toMeasure t := by
  have : (fun ω : RandomSources ι M => ω.2 o) ⁻¹' t =
      (Set.univ : Set (SignIndex ι → Bool)) ×ˢ (Function.eval o ⁻¹' t) := by
    ext ω; simp
  rw [this, sourcesLaw, Measure.prod_prod, measure_univ, one_mul, ordersLaw_eval]

/-- **The coordinates are independent** under `sourcesLaw`. -/
theorem iIndep_coord : iIndep (coordSpace ι M) (sourcesLaw ι M) := by
  classical
  rw [iIndep_iff]
  intro s f hf
  set tL : SignIndex ι → Set Bool := fun z => (fun ω : RandomSources ι M => ω.1 z) '' f (Sum.inl z)
  set tR : (o : ℕ) → Set (Order (M o)) :=
    fun o => (fun ω : RandomSources ι M => ω.2 o) '' f (Sum.inr o)
  have hfL : ∀ z ∈ s.toLeft, f (Sum.inl z) = (fun ω : RandomSources ι M => ω.1 z) ⁻¹' tL z :=
    fun z hz => (preimage_image_of_comap _ _ (hf _ (Finset.mem_toLeft.mp hz))).symm
  have hfR : ∀ o ∈ s.toRight, f (Sum.inr o) = (fun ω : RandomSources ι M => ω.2 o) ⁻¹' tR o :=
    fun o ho => (preimage_image_of_comap _ _ (hf _ (Finset.mem_toRight.mp ho))).symm
  have hinter : (⋂ i ∈ s, f i) =
      (Set.pi (s.toLeft : Set (SignIndex ι)) tL) ×ˢ (Set.pi (s.toRight : Set ℕ) tR) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_prod, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro h
      refine ⟨fun z hz => ?_, fun o ho => ?_⟩
      · have := h _ (Finset.mem_toLeft.mp hz); rw [hfL z hz] at this; exact this
      · have := h _ (Finset.mem_toRight.mp ho); rw [hfR o ho] at this; exact this
    · rintro ⟨hL, hR⟩ i hi
      cases i with
      | inl z =>
        have hz : z ∈ s.toLeft := Finset.mem_toLeft.mpr hi
        rw [hfL z hz]; exact hL z hz
      | inr o =>
        have ho : o ∈ s.toRight := Finset.mem_toRight.mpr hi
        rw [hfR o ho]; exact hR o ho
  rw [hinter, sourcesLaw, Measure.prod_prod, signsLaw, ordersLaw,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSpace.measurableSet_top),
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSpace.measurableSet_top)]
  rw [← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disjSum]
  simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
  congr 1
  · refine Finset.prod_congr rfl fun z hz => ?_
    rw [hfL z hz]; exact (sourcesLaw_sign (M := M) z (tL z)).symm
  · refine Finset.prod_congr rfl fun o ho => ?_
    rw [hfR o ho]; exact (sourcesLaw_order (ι := ι) o (tR o)).symm

/-- `A` is decided by the coordinates in `U`. -/
def DepOn (U : Set (Coord ι)) (A : Set (RandomSources ι M)) : Prop :=
  ∀ ω ω' : RandomSources ι M, (∀ z, Sum.inl z ∈ U → ω.1 z = ω'.1 z) →
    (∀ o, Sum.inr o ∈ U → ω.2 o = ω'.2 o) → (ω ∈ A ↔ ω' ∈ A)

/-- Keep the coordinates in `U`, reset the others. -/
def keep (U : Set (Coord ι)) (ω : RandomSources ι M) : RandomSources ι M := by
  classical
  exact (fun z => if Sum.inl z ∈ U then ω.1 z else false,
    fun o => if Sum.inr o ∈ U then ω.2 o else 1)

theorem keep_fst_of_mem {U : Set (Coord ι)} {z : SignIndex ι} (hz : Sum.inl z ∈ U)
    (ω : RandomSources ι M) : (keep U ω).1 z = ω.1 z := by
  simp [keep, hz]

theorem keep_fst_of_not_mem {U : Set (Coord ι)} {z : SignIndex ι} (hz : Sum.inl z ∉ U)
    (ω : RandomSources ι M) : (keep U ω).1 z = false := by
  simp [keep, hz]

theorem keep_snd_of_mem {U : Set (Coord ι)} {o : ℕ} (ho : Sum.inr o ∈ U)
    (ω : RandomSources ι M) : (keep U ω).2 o = ω.2 o := by
  simp [keep, ho]

theorem keep_snd_of_not_mem {U : Set (Coord ι)} {o : ℕ} (ho : Sum.inr o ∉ U)
    (ω : RandomSources ι M) : (keep U ω).2 o = 1 := by
  simp [keep, ho]

theorem keep_measurable (U : Set (Coord ι)) :
    Measurable[⨆ i ∈ U, coordSpace ι M i] (keep (M := M) U) := by
  have hL : ∀ z, Measurable[⨆ i ∈ U, coordSpace ι M i]
      (fun ω : RandomSources ι M => (keep U ω).1 z) := by
    intro z
    by_cases hz : Sum.inl z ∈ U
    · have he : (fun ω : RandomSources ι M => (keep U ω).1 z) = fun ω => ω.1 z :=
        funext fun ω => keep_fst_of_mem hz ω
      rw [he]
      exact (comap_measurable (fun ω : RandomSources ι M => ω.1 z)).mono
        (le_iSup₂ (f := fun i (_ : i ∈ U) => coordSpace ι M i) _ hz) le_rfl
    · have he : (fun ω : RandomSources ι M => (keep U ω).1 z) = fun _ => false :=
        funext fun ω => keep_fst_of_not_mem hz ω
      rw [he]; exact measurable_const
  have hR : ∀ o, Measurable[⨆ i ∈ U, coordSpace ι M i]
      (fun ω : RandomSources ι M => (keep U ω).2 o) := by
    intro o
    by_cases ho : Sum.inr o ∈ U
    · have he : (fun ω : RandomSources ι M => (keep U ω).2 o) = fun ω => ω.2 o :=
        funext fun ω => keep_snd_of_mem ho ω
      rw [he]
      exact (comap_measurable (fun ω : RandomSources ι M => ω.2 o)).mono
        (le_iSup₂ (f := fun i (_ : i ∈ U) => coordSpace ι M i) _ ho) le_rfl
    · have he : (fun ω : RandomSources ι M => (keep U ω).2 o) = fun _ => 1 :=
        funext fun ω => keep_snd_of_not_mem ho ω
      rw [he]; exact measurable_const
  have piL : ∀ (m : MeasurableSpace (RandomSources ι M)) (f : RandomSources ι M → SignIndex ι → Bool),
      (∀ z, Measurable[m] fun ω => f ω z) → Measurable[m] f := fun m f h => by
    let _ := m; exact Measurable.of_eval h
  have piR : ∀ (m : MeasurableSpace (RandomSources ι M))
      (f : RandomSources ι M → (o : ℕ) → Order (M o)),
      (∀ o, Measurable[m] fun ω => f ω o) → Measurable[m] f := fun m f h => by
    let _ := m; exact Measurable.of_eval h
  exact Measurable.prodMk (piL _ _ hL) (piR _ _ hR)

theorem measurableSet_iSup_of_depOn (U : Set (Coord ι)) (A : Set (RandomSources ι M))
    (hA : MeasurableSet A) (hdep : DepOn U A) :
    MeasurableSet[⨆ i ∈ U, coordSpace ι M i] A := by
  classical
  have : keep U ⁻¹' A = A := by
    ext ω
    simp only [Set.mem_preimage]
    refine (hdep (keep U ω) ω (fun z hz => ?_) (fun o ho => ?_))
    · exact keep_fst_of_mem hz ω
    · exact keep_snd_of_mem ho ω
  rw [← this]
  exact keep_measurable U hA

/-- **Independence on disjoint coordinates.** -/
theorem measure_inter_of_depOn (U V : Set (Coord ι)) (hUV : Disjoint U V)
    (A B : Set (RandomSources ι M)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAU : DepOn U A) (hBV : DepOn V B) :
    sourcesLaw ι M (A ∩ B) = sourcesLaw ι M A * sourcesLaw ι M B := by
  have hind := indep_iSup_of_disjoint (coordSpace_le (ι := ι) (M := M)) iIndep_coord hUV
  exact (Indep_iff _ _ _).mp hind A B (measurableSet_iSup_of_depOn U A hA hAU)
    (measurableSet_iSup_of_depOn V B hB hBV)

theorem depOn_mono {U U' : Set (Coord ι)} (h : U ⊆ U') {A : Set (RandomSources ι M)}
    (hA : DepOn U A) : DepOn U' A :=
  fun ω ω' h1 h2 => hA ω ω' (fun z hz => h1 z (h hz)) (fun o ho => h2 o (h ho))

theorem depOn_inter {U : Set (Coord ι)} {A B : Set (RandomSources ι M)}
    (hA : DepOn U A) (hB : DepOn U B) : DepOn U (A ∩ B) := by
  intro ω ω' h1 h2
  simp only [Set.mem_inter_iff]
  rw [hA ω ω' h1 h2, hB ω ω' h1 h2]

/-! ## Relabelling the coordinates -/

/-- Transport of a permutation of `Fin n'` to `Fin n` along `n' = n`. -/
def castOrd {n' n : ℕ} (h : n' = n) (p : Order n') : Order n := h ▸ p

theorem castOrd_apply_val {n' n : ℕ} (h : n' = n) (p : Order n') (c : ℕ) (hc : c < n)
    (hc' : c < n') : ((castOrd h p) ⟨c, hc⟩ : ℕ) = (p ⟨c, hc'⟩ : ℕ) := by
  subst h; rfl

theorem map_castOrd {n' n : ℕ} (h : n' = n) :
    (PMF.uniformOfFintype (Order n')).toMeasure.map (castOrd h) =
      (PMF.uniformOfFintype (Order n)).toMeasure := by
  subst h
  have : castOrd (rfl : n' = n') = id := rfl
  rw [this, Measure.map_id]

/-- Relabel the coordinates: signs by `eS`, orders by `eO` (order sizes preserved). -/
def relabel (eS : Equiv.Perm (SignIndex ι)) (eO : Equiv.Perm ℕ) (hM : ∀ o, M (eO o) = M o)
    (ω : RandomSources ι M) : RandomSources ι M :=
  (fun z => ω.1 (eS z), fun o => castOrd (hM o) (ω.2 (eO o)))

theorem measurePreserving_relabel (eS : Equiv.Perm (SignIndex ι)) (eO : Equiv.Perm ℕ)
    (hM : ∀ o, M (eO o) = M o) :
    MeasurePreserving (relabel eS eO hM) (sourcesLaw ι M) (sourcesLaw ι M) := by
  have hS : MeasurePreserving (fun (a : SignIndex ι → Bool) z => a (eS z))
      (signsLaw ι) (signsLaw ι) := by
    refine ⟨by fun_prop, ?_⟩
    unfold signsLaw
    exact Measure.map_infinitePi_infinitePi_of_inj eS.injective
  have hO1 : MeasurePreserving (fun (b : (o : ℕ) → Order (M o)) o => b (eO o))
      (ordersLaw M)
      (Measure.infinitePi fun o => (PMF.uniformOfFintype (Order (M (eO o)))).toMeasure) := by
    refine ⟨by fun_prop, ?_⟩
    unfold ordersLaw
    exact Measure.map_infinitePi_infinitePi_of_inj eO.injective
  have hcast : ∀ o, Measurable (castOrd (hM o)) := fun o => measurable_from_top
  have hO2 : MeasurePreserving (fun (b : (o : ℕ) → Order (M (eO o))) o => castOrd (hM o) (b o))
      (Measure.infinitePi fun o => (PMF.uniformOfFintype (Order (M (eO o)))).toMeasure)
      (ordersLaw M) := by
    refine ⟨Measurable.of_eval fun o => (hcast o).comp (measurable_pi_apply o), ?_⟩
    rw [Measure.infinitePi_map_pi _ hcast]
    unfold ordersLaw
    congr 1
    funext o
    exact map_castOrd (hM o)
  exact hS.prod (hO2.comp hO1)

theorem relabel_fst (eS : Equiv.Perm (SignIndex ι)) (eO : Equiv.Perm ℕ)
    (hM : ∀ o, M (eO o) = M o) (ω : RandomSources ι M) (z : SignIndex ι) :
    (relabel eS eO hM ω).1 z = ω.1 (eS z) := rfl

theorem relabel_snd_val (eS : Equiv.Perm (SignIndex ι)) (eO : Equiv.Perm ℕ)
    (hM : ∀ o, M (eO o) = M o) (ω : RandomSources ι M) (o c : ℕ) (hc : c < M o) :
    (((relabel eS eO hM ω).2 o) ⟨c, hc⟩ : ℕ) = ((ω.2 (eO o)) ⟨c, (hM o).symm ▸ hc⟩ : ℕ) :=
  castOrd_apply_val (hM o) _ c hc _

end AndersonAC.AgentS78.Retry
