import AndersonAC.AgentS78.Construction.ClearingTrialZ

/-!
# WP10 construction, C4b off a null set: tools

* `flipClosure`: a measurable null superset of a null set, invariant under the site and
  single-digit sign flips (countable union of preimages under finite words of flips);
* `compTrial`: a stopped trial composed with a measurable map of the sample space (history by
  comap); with `φ = ω₀` on the closure and `id` elsewhere, the composed trial has the true
  residuals at every sample, and agrees with the original one off a null set.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.ResidualZ

open AndersonAC.S6
open AndersonAC.S2 (RandomSources sourcesLaw SignIndex)
open AndersonAC.SolS2 (signFlip signFlip_measurable signFlip_law signFlip_involutive)

/-! ## The flip closure of a null set -/

section Closure

variable (S : Type) [Fintype S] [DecidableEq S] {M : ℕ → ℕ}

/-- The generating masks: whole site suffixes and single digits. -/
def genMask : S ⊕ (S × ℕ) → Set (SignIndex S)
  | Sum.inl y => Residual.siteMask S y
  | Sum.inr p => {Sum.inl p}

/-- The flip of a word of generators. -/
def act (w : List (S ⊕ (S × ℕ))) : RandomSources S M → RandomSources S M :=
  w.foldr (fun g f => signFlip S (genMask S g) ∘ f) id

theorem act_append (w₁ w₂ : List (S ⊕ (S × ℕ))) :
    act (M := M) S (w₁ ++ w₂) = act S w₁ ∘ act S w₂ := by
  induction w₁ with
  | nil => rfl
  | cons g w ih =>
    show signFlip S (genMask S g) ∘ act S (w ++ w₂) = (signFlip S (genMask S g) ∘ act S w) ∘ act S w₂
    rw [ih]; rfl

theorem act_measurable (w : List (S ⊕ (S × ℕ))) : Measurable (act (M := M) S w) := by
  induction w with
  | nil => exact measurable_id
  | cons g w ih => exact (signFlip_measurable S (genMask S g)).comp ih

theorem act_map (w : List (S ⊕ (S × ℕ))) :
    (sourcesLaw S M).map (act S w) = sourcesLaw S M := by
  induction w with
  | nil => exact Measure.map_id
  | cons g w ih =>
    show (sourcesLaw S M).map (signFlip S (genMask S g) ∘ act S w) = _
    rw [← Measure.map_map (signFlip_measurable S _) (act_measurable S w), ih, signFlip_law]

/-- The flip closure of the measurable hull of `Z`. -/
def flipClosure (Z : Set (RandomSources S M)) : Set (RandomSources S M) :=
  ⋃ w : List (S ⊕ (S × ℕ)), act S w ⁻¹' toMeasurable (sourcesLaw S M) Z

theorem subset_flipClosure (Z : Set (RandomSources S M)) : Z ⊆ flipClosure S Z := by
  intro ω hω
  exact Set.mem_iUnion.mpr ⟨[], subset_toMeasurable _ _ hω⟩

theorem flipClosure_measurable (Z : Set (RandomSources S M)) :
    MeasurableSet (flipClosure S Z) :=
  MeasurableSet.iUnion fun w => (act_measurable S w) (measurableSet_toMeasurable _ _)

theorem flipClosure_null (Z : Set (RandomSources S M)) (hZ : sourcesLaw S M Z = 0) :
    sourcesLaw S M (flipClosure S Z) = 0 := by
  refine measure_iUnion_null fun w => ?_
  rw [← Measure.map_apply (act_measurable S w) (measurableSet_toMeasurable _ _), act_map,
    measure_toMeasurable, hZ]

theorem flipClosure_invariant (Z : Set (RandomSources S M)) (g : S ⊕ (S × ℕ)) :
    signFlip S (genMask S g) ⁻¹' flipClosure S Z = flipClosure S Z := by
  ext ω
  simp only [Set.mem_preimage, flipClosure, Set.mem_iUnion]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ++ [g], ?_⟩
    rw [act_append]
    exact hw
  · rintro ⟨w, hw⟩
    refine ⟨w ++ [g], ?_⟩
    rw [act_append]
    show act S w (signFlip S (genMask S g) (signFlip S (genMask S g) ω)) ∈ _
    rw [signFlip_involutive S _ ω]
    exact hw

theorem flipClosure_site (Z : Set (RandomSources S M)) (y : S) (ω : RandomSources S M) :
    signFlip S (Residual.siteMask S y) ω ∈ flipClosure S Z ↔ ω ∈ flipClosure S Z := by
  have := flipClosure_invariant S Z (Sum.inl y)
  rw [Set.ext_iff] at this
  exact this ω

theorem flipClosure_digit (Z : Set (RandomSources S M)) (y : S) (n : ℕ) (ω : RandomSources S M) :
    signFlip S {Sum.inl (y, n)} ω ∈ flipClosure S Z ↔ ω ∈ flipClosure S Z := by
  have := flipClosure_invariant S Z (Sum.inr (y, n))
  rw [Set.ext_iff] at this
  exact this ω

end Closure

/-! ## Composing a trial with a map of the sample space -/

section Comp

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ} {g0 : Ω → Matrix ι ι ℂ}
  {order : ι ≃ Fin (Fintype.card ι)}

/-- The comap of a filtration along a measurable map. -/
def comapFiltration (φ : Ω → Ω) (hφ : Measurable φ) (F : Filtration ℕ ‹MeasurableSpace Ω›) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := (F k).comap φ
  mono' _ _ hij := MeasurableSpace.comap_mono (F.mono hij)
  le' k := (MeasurableSpace.comap_mono (F.le k)).trans hφ.comap_le

/-- A stopped trial composed with a measurable map of the sample space. -/
def compTrial (φ : Ω → Ω) (hφ : Measurable φ) (q : StoppedTrial (Ω := Ω) core t r g0 order) :
    StoppedTrial (Ω := Ω) core t (fun ω => r (φ ω)) (fun ω => g0 (φ ω)) order where
  state k ω := q.state k (φ ω)
  ridge k ω := q.ridge k (φ ω)
  pivot k ω := q.pivot k (φ ω)
  residual k ω := q.residual k (φ ω)
  stop ω := q.stop (φ ω)
  outcome ω := q.outcome (φ ω)
  history := comapFiltration φ hφ q.history
  damping_adapted := q.damping_adapted.comp_measurable (Measurable.of_comap_le le_rfl)
  initial_active ω := q.initial_active (φ ω)
  start_entries ω := q.start_entries (φ ω)
  start_ridge ω := q.start_ridge (φ ω)
  initial_inverse ω := q.initial_inverse (φ ω)
  finite_stop ω := q.finite_stop (φ ω)
  stopping k := by
    have h := q.stopping k
    exact ⟨_, h, rfl⟩
  running_budgets k ω := q.running_budgets k (φ ω)
  running_ridge k ω := q.running_ridge k (φ ω)
  pivot_max k ω := q.pivot_max k (φ ω)
  pivot_tie k ω := q.pivot_tie k (φ ω)
  running_cap k ω := q.running_cap k (φ ω)
  heat k ω := q.heat k (φ ω)
  ridge_rule k ω := q.ridge_rule k (φ ω)
  done_iff ω := q.done_iff (φ ω)
  fail_reason ω := q.fail_reason (φ ω)
  entries_adapted k i j :=
    (q.entries_adapted k i j).comp_measurable (Measurable.of_comap_le le_rfl)
  cross_adapted k := (q.cross_adapted k).comp_measurable (Measurable.of_comap_le le_rfl)
  ridge_predictable k := (q.ridge_predictable k).comp_measurable (Measurable.of_comap_le le_rfl)
  pivot_predictable k := (q.pivot_predictable k).comp (Measurable.of_comap_le le_rfl)
  residual_revealed k :=
    (q.residual_revealed k).comp_measurable (Measurable.of_comap_le le_rfl)
  outcome_measurable := q.outcome_measurable.comp hφ

theorem queryHistory_comap (φ : Ω → Ω) (pivot : ℕ → Ω → ι) (residual : ℕ → Ω → ℝ) (k : ℕ) :
    (queryHistory ⊥ pivot residual k).comap φ =
      queryHistory ⊥ (fun j ω => pivot j (φ ω)) (fun j ω => residual j (φ ω)) k := by
  unfold queryHistory
  simp only [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup, MeasurableSpace.comap_bot,
    MeasurableSpace.comap_comp]
  rfl

theorem compTrial_history (φ : Ω → Ω) (hφ : Measurable φ) (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (hhist : ∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k) (k : ℕ) :
    (compTrial φ hφ q).history k =
      queryHistory ⊥ (compTrial φ hφ q).pivot (compTrial φ hφ q).residual k := by
  show (q.history k).comap φ = _
  rw [hhist k, queryHistory_comap]
  rfl

end Comp

end AndersonAC.AgentS78.ResidualZ
