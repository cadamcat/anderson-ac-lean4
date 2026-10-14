import AndersonAC.AgentS78.Construction.Freezing
import AndersonAC.S2Fresh.Lift

/-!
# Proof of the freezing contract (Lemma 2.2 at a retained stopping time)

`FreezingStatement` (Freezing.lean:70) is false for `p < 0`
(`not_freezingStatement`, FreezingCounterexample.lean). This file proves it with the extra
hypothesis `0 ≤ p` (`FreezingStatementNonneg`, `freezing_proof`).

Route.
1. `stopped_cyl`: on a stopped retained event `D` on which a finite cylinder's coordinates are
   a.e. unqueried, `μ(D ∩ cyl) = w · μ D` with the product weight `w`
   (`S2.conditional_freshness_ae_stopped`); `cyl_law` is the case `D = univ`, `τ = 0`.
2. Cylinders form a π-system generating the source σ-algebra.
3. For a pattern `π`, `proj π` keeps the `π`-coordinates and resets the rest. On
   `D ∩ {pattern X = π}` the law of `(X, proj π)` is the product of the law of `X` and the
   law of `proj π` (`Measure.prod_eq_generateFrom` on rectangles `s × cyl`).
4. Freezing `X` in that product gives `μ(D ∩ {pattern X = π} ∩ {ω ∈ A(X ω)}) ≤ p · μ(…)`;
   summing over the countably many patterns and the set-integral characterization of the
   conditional expectation conclude.
-/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AndersonAC.AgentS78

open AndersonAC.S2

/-- **C2, corrected.** `FreezingStatement` with the added hypothesis `0 ≤ p`. -/
def FreezingStatementNonneg : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (τ : RandomSources ι M → WithTop ℕ)
    (hτ : IsStoppingTime (retainedFiltration ι hQ) τ)
    (_hfin : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (S : Type) [MeasurableSpace S] (X : RandomSources ι M → S)
    (_hX : Measurable[hτ.measurableSpace] X)
    (pattern : S → FreshPattern ι) (_hpat : Measurable pattern)
    (A : S → Set (RandomSources ι M))
    (_hA : MeasurableSet {p : S × RandomSources ι M | p.2 ∈ A p.1})
    (_hloc : ∀ x, DependsOnly ι (pattern x) (A x))
    (_hfresh : ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι Q ((τ ω).untopD 0) (pattern (X ω)) ω)
    (good : Set S) (_hgood : ∀ᵐ ω ∂sourcesLaw ι M, X ω ∈ good)
    (p : ℝ) (_hp0 : 0 ≤ p) (_hp : ∀ x ∈ good, sourcesLaw ι M (A x) ≤ ENNReal.ofReal p),
    ∀ᵐ ω ∂sourcesLaw ι M,
      (sourcesLaw ι M)[{ω' | ω' ∈ A (X ω')}.indicator (fun _ => (1 : ℝ)) |
        hτ.measurableSpace] ω ≤ p

namespace Freeze

section Cyl
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

/-- A finite cylinder in signs and orders. -/
def cyl (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool) (O : Finset ℕ)
    (b : (o : ℕ) → Order (M o)) : Set (RandomSources ι M) :=
  signCylinder ι s a ∩ orderCylinder ι O b

/-- The product weight of a cylinder with fresh coordinates. -/
def freshWeight (M : ℕ → ℕ) (s : Finset (SignIndex ι)) (O : Finset ℕ) : ℝ :=
  (2 : ℝ) ^ (-(s.card : ℤ)) * ∏ o ∈ O, ((M o).factorial : ℝ)⁻¹

theorem cyl_measurable (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool) (O : Finset ℕ)
    (b : (o : ℕ) → Order (M o)) : MeasurableSet (cyl s a O b) :=
  (SolS2.signCylinder_measurable ι s a).inter (SolS2.orderCylinder_measurable ι O b)

theorem completionWeight_of_fresh (Q : ℕ → RandomSources ι M → Query ι) (q : ℕ)
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) (ω : RandomSources ι M)
    (h : ∀ o ∈ O, orderCount ι Q q ω o = 0) :
    completionWeight ι Q q O b ω = ∏ o ∈ O, ((M o).factorial : ℝ)⁻¹ := by
  classical
  unfold completionWeight
  refine Finset.prod_congr rfl fun o ho => ?_
  rw [h o ho]
  simp

/-- Step 1: factorization of a fresh cylinder on a stopped retained event. -/
theorem stopped_cyl {Q : ℕ → RandomSources ι M → Query ι} (hQ : ObeysQueryRules ι Q)
    (τ : RandomSources ι M → WithTop ℕ) (hτ : IsStoppingTime (retainedFiltration ι hQ) τ)
    (hfin : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[hτ.measurableSpace] D)
    (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool) (O : Finset ℕ)
    (b : (o : ℕ) → Order (M o))
    (hfr : ∀ᵐ ω ∂sourcesLaw ι M, ω ∈ D →
      (∀ x ∈ s, x ∉ queriedSigns ι Q ((τ ω).untopD 0) ω) ∧
        ∀ o ∈ O, orderCount ι Q ((τ ω).untopD 0) ω o = 0) :
    sourcesLaw ι M (D ∩ cyl s a O b) =
      ENNReal.ofReal (freshWeight M s O) * sourcesLaw ι M D := by
  set μ := sourcesLaw ι M
  have h := conditional_freshness_ae_stopped ι hQ (retainedFiltration ι hQ) (fun _ => rfl)
    τ hτ hfin D hD s a O b
  set U := {ω | ω ∈ D ∧ ω ∈ signsUnqueried ι Q ((τ ω).untopD 0) s} with hUdef
  have hU : U =ᵐ[μ] D := by
    filter_upwards [hfr] with ω hω
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, (hω h).1⟩⟩
  have hD' : MeasurableSet D := hτ.measurableSpace_le _ hD
  have hint : ∫ ω in U, completionWeight ι Q ((τ ω).untopD 0) O b ω ∂μ =
      μ.real D * ∏ o ∈ O, ((M o).factorial : ℝ)⁻¹ := by
    rw [setIntegral_congr_set hU,
      setIntegral_congr_ae (g := fun _ => ∏ o ∈ O, ((M o).factorial : ℝ)⁻¹) hD']
    · simp
    · filter_upwards [hfr] with ω hω hωD
      exact completionWeight_of_fresh Q _ O b ω (hω hωD).2
  have hcyl : μ (U ∩ signCylinder ι s a ∩ orderCylinder ι O b) = μ (D ∩ cyl s a O b) := by
    apply measure_congr
    rw [cyl, ← Set.inter_assoc]
    exact (hU.inter (ae_eq_refl _)).inter (ae_eq_refl _)
  rw [hcyl, hint] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (D ∩ cyl s a O b)), h,
    ← ENNReal.ofReal_toReal (measure_ne_top μ D), ← ENNReal.ofReal_mul (by
      unfold freshWeight; positivity)]
  congr 1
  rw [freshWeight, Measure.real]
  ring

/-- Step 1, unconditional case: the product law of a cylinder. -/
theorem cyl_law (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool) (O : Finset ℕ)
    (b : (o : ℕ) → Order (M o)) :
    sourcesLaw ι M (cyl s a O b) = ENNReal.ofReal (freshWeight M s O) := by
  let Q0 : ℕ → RandomSources ι M → Query ι := fun _ _ => Query.decision
  have hQ0 : ObeysQueryRules ι Q0 :=
    ⟨fun _ => measurable_const, fun _ _ _ hq => by simp [Q0] at hq,
      fun _ _ _ hq => by simp [Q0] at hq⟩
  have hτ : IsStoppingTime (retainedFiltration ι hQ0)
      (fun _ : RandomSources ι M => ((0 : ℕ) : WithTop ℕ)) :=
    isStoppingTime_const _ _
  have h := stopped_cyl hQ0 _ hτ (Filter.Eventually.of_forall fun _ => by simp) Set.univ
    MeasurableSet.univ s a O b (Filter.Eventually.of_forall fun ω _ =>
      ⟨fun x _ => by simp [queriedSigns], fun o _ => by simp [orderCount]⟩)
  simpa using h

/-- The cylinders. -/
def cylinders : Set (Set (RandomSources ι M)) :=
  {t | ∃ s a O b, t = cyl s a O b}

theorem isPiSystem_cylinders : IsPiSystem (cylinders (ι := ι) (M := M)) := by
  rintro _ ⟨s, a, O, b, rfl⟩ _ ⟨s', a', O', b', rfl⟩ ⟨ω, hω, hω'⟩
  refine ⟨s ∪ s', ω.1, O ∪ O', ω.2, ?_⟩
  simp only [cyl, signCylinder, orderCylinder, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω hω'
  ext ω'
  simp only [cyl, signCylinder, orderCylinder, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨fun x hx => ?_, fun o ho => ?_⟩
    · rcases hx with hx | hx
      · rw [h1 x hx, hω.1 x hx]
      · rw [h3 x hx, hω'.1 x hx]
    · rcases ho with ho | ho
      · rw [h2 o ho, hω.2 o ho]
      · rw [h4 o ho, hω'.2 o ho]
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun x hx => (h1 x (Or.inl hx)).trans (hω.1 x hx),
        fun o ho => (h2 o (Or.inl ho)).trans (hω.2 o ho)⟩,
      fun x hx => (h1 x (Or.inr hx)).trans (hω'.1 x hx),
        fun o ho => (h2 o (Or.inr ho)).trans (hω'.2 o ho)⟩

theorem univ_mem_cylinders : (Set.univ : Set (RandomSources ι M)) ∈ cylinders := by
  refine ⟨∅, fun _ => false, ∅, fun _ => 1, ?_⟩
  ext ω
  simp [cyl, signCylinder, orderCylinder]

theorem generateFrom_cylinders :
    MeasurableSpace.generateFrom (cylinders (ι := ι) (M := M)) =
      (inferInstance : MeasurableSpace (RandomSources ι M)) := by
  classical
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨s, a, O, b, rfl⟩
    exact cyl_measurable s a O b
  · refine sup_le ?_ ?_
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun x => ?_
      rw [MeasurableSpace.comap_comp]
      rintro _ ⟨u, -, rfl⟩
      have : (fun ω : RandomSources ι M => ω.1 x) ⁻¹' u =
          ⋃ v ∈ u, cyl {x} (fun _ => v) ∅ (fun _ => 1) := by
        ext ω
        simp [cyl, signCylinder, orderCylinder]
      change MeasurableSet[MeasurableSpace.generateFrom cylinders]
        ((fun ω : RandomSources ι M => ω.1 x) ⁻¹' u)
      rw [this]
      exact MeasurableSet.biUnion u.to_countable fun v _ =>
        MeasurableSpace.measurableSet_generateFrom ⟨_, _, _, _, rfl⟩
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun o => ?_
      rw [MeasurableSpace.comap_comp]
      rintro _ ⟨u, -, rfl⟩
      have : (fun ω : RandomSources ι M => ω.2 o) ⁻¹' u =
          ⋃ v ∈ u, cyl ∅ (fun _ => false) {o} (Function.update (fun _ => 1) o v) := by
        ext ω
        simp [cyl, signCylinder, orderCylinder]
      change MeasurableSet[MeasurableSpace.generateFrom cylinders]
        ((fun ω : RandomSources ι M => ω.2 o) ⁻¹' u)
      rw [this]
      exact MeasurableSet.biUnion u.to_countable fun v _ =>
        MeasurableSpace.measurableSet_generateFrom ⟨_, _, _, _, rfl⟩

end Cyl

section Proj
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

/-- Keep the pattern's coordinates, reset the others. -/
def proj (π : FreshPattern ι) (ω : RandomSources ι M) : RandomSources ι M := by
  classical
  exact (fun z => if z ∈ π.signs then ω.1 z else false,
    fun o => if o ∈ π.orders then ω.2 o else 1)

theorem proj_measurable (π : FreshPattern ι) : Measurable (proj (M := M) π) := by
  classical
  refine Measurable.prodMk (Measurable.of_eval fun z => ?_)
    (Measurable.of_eval fun o => ?_)
  · by_cases hz : z ∈ π.signs
    · simp only [hz, ite_true]
      exact (measurable_pi_apply z).comp measurable_fst
    · simp only [hz, ite_false]
      exact measurable_const
  · by_cases ho : o ∈ π.orders
    · simp only [ho, ite_true]
      exact (measurable_pi_apply o).comp measurable_snd
    · simp only [ho, ite_false]
      exact measurable_const

theorem mem_proj_iff {π : FreshPattern ι} {B : Set (RandomSources ι M)}
    (hB : DependsOnly ι π B) (ω : RandomSources ι M) : proj π ω ∈ B ↔ ω ∈ B := by
  classical
  refine hB _ _ (fun z hz => ?_) (fun o ho => ?_)
  · simp [proj, hz]
  · simp [proj, ho]

theorem proj_preimage_cyl (π : FreshPattern ι) (s : Finset (SignIndex ι))
    (a : SignIndex ι → Bool) (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    proj π ⁻¹' cyl s a O b = ∅ ∨ ∃ (s' : Finset (SignIndex ι)) (O' : Finset ℕ),
      (∀ x ∈ s', x ∈ π.signs) ∧ (∀ o ∈ O', o ∈ π.orders) ∧
        proj π ⁻¹' cyl s a O b = cyl s' a O' b := by
  classical
  by_cases hc : (∀ x ∈ s, x ∉ π.signs → false = a x) ∧ (∀ o ∈ O, o ∉ π.orders → 1 = b o)
  · refine Or.inr ⟨s.filter (· ∈ π.signs), O.filter (· ∈ π.orders),
      fun x hx => (Finset.mem_filter.mp hx).2, fun o ho => (Finset.mem_filter.mp ho).2, ?_⟩
    ext ω
    simp only [Set.mem_preimage, cyl, signCylinder, orderCylinder, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Finset.mem_filter, proj]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, fun o ho => ?_⟩
      · simpa [hx.2] using h1 x hx.1
      · simpa [ho.2] using h2 o ho.1
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, fun o ho => ?_⟩
      · by_cases hxs : x ∈ π.signs
        · simpa [hxs] using h1 x ⟨hx, hxs⟩
        · simpa [hxs] using hc.1 x hx hxs
      · by_cases hos : o ∈ π.orders
        · simpa [hos] using h2 o ⟨ho, hos⟩
        · simpa [hos] using hc.2 o ho hos
  · refine Or.inl (Set.eq_empty_of_forall_notMem fun ω hω => hc ?_)
    simp only [Set.mem_preimage, cyl, signCylinder, orderCylinder, Set.mem_inter_iff,
      Set.mem_ofPred_eq, proj] at hω
    refine ⟨fun x hx hxs => ?_, fun o ho hos => ?_⟩
    · simpa [hxs] using hω.1 x hx
    · simpa [hos] using hω.2 o ho

end Proj

instance freshPattern_countable (ι : Type) [Fintype ι] [DecidableEq ι] :
    Countable (FreshPattern ι) := by
  have hinj : Function.Injective
      (fun π : FreshPattern ι => (π.sites, π.height, π.aux, π.orders)) := by
    rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  exact hinj.countable

section Main
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}
  {Q : ℕ → RandomSources ι M → Query ι} {hQ : ObeysQueryRules ι Q}
  {τ : RandomSources ι M → WithTop ℕ} {hτ : IsStoppingTime (retainedFiltration ι hQ) τ}
  {S : Type} [MeasurableSpace S] {X : RandomSources ι M → S} {pattern : S → FreshPattern ι}

theorem patternSet_measurable (hX : Measurable[hτ.measurableSpace] X)
    (hpat : Measurable pattern) (π : FreshPattern ι) :
    MeasurableSet[hτ.measurableSpace] (X ⁻¹' (pattern ⁻¹' {π})) :=
  hX (hpat (show MeasurableSet ({π} : Set (FreshPattern ι)) from
    MeasurableSpace.measurableSet_top))

/-- Step 3: on `D ∩ {pattern X = π}`, `X` and the `π`-coordinates have product law. -/
theorem map_pair_restrict (hfin : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (hX : Measurable[hτ.measurableSpace] X) (hpat : Measurable pattern)
    (hfresh : ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι Q ((τ ω).untopD 0) (pattern (X ω)) ω)
    (π : FreshPattern ι) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[hτ.measurableSpace] D) :
    ((sourcesLaw ι M).restrict (D ∩ X ⁻¹' (pattern ⁻¹' {π}))).map
        (fun ω => (X ω, proj π ω)) =
      (((sourcesLaw ι M).restrict (D ∩ X ⁻¹' (pattern ⁻¹' {π}))).map X).prod
        ((sourcesLaw ι M).map (proj π)) := by
  set μ := sourcesLaw ι M
  set Dπ := D ∩ X ⁻¹' (pattern ⁻¹' {π}) with hDπdef
  have hle := hτ.measurableSpace_le
  have hXm : Measurable X := hX.mono hle le_rfl
  have hDπτ : MeasurableSet[hτ.measurableSpace] Dπ :=
    hD.inter (patternSet_measurable hX hpat π)
  have hDπ : MeasurableSet Dπ := hle _ hDπτ
  refine (Measure.prod_eq_generateFrom MeasurableSpace.generateFrom_measurableSet generateFrom_cylinders
    MeasurableSpace.isPiSystem_measurableSet isPiSystem_cylinders
    ((μ.restrict Dπ).map X).toFiniteSpanningSetsIn
    ⟨fun _ => Set.univ, fun _ => univ_mem_cylinders, fun _ => measure_lt_top _ _,
      Set.iUnion_const _⟩ ?_).symm
  rintro s hs _ ⟨s', a, O, b, rfl⟩
  rw [Measure.map_apply (hXm.prodMk (proj_measurable π)) (hs.prod (cyl_measurable _ _ _ _)),
    Measure.map_apply hXm hs, Measure.map_apply (proj_measurable π) (cyl_measurable _ _ _ _),
    Set.mk_preimage_prod, Measure.restrict_apply ((hXm hs).inter
      ((proj_measurable π) (cyl_measurable _ _ _ _))), Measure.restrict_apply (hXm hs)]
  rcases proj_preimage_cyl π s' a O b with h0 | ⟨s'', O', hs'', hO', heq⟩
  · rw [h0]
    simp
  · rw [heq, cyl_law]
    have hfr : ∀ᵐ ω ∂μ, ω ∈ X ⁻¹' s ∩ Dπ →
        (∀ x ∈ s'', x ∉ queriedSigns ι Q ((τ ω).untopD 0) ω) ∧
          ∀ o ∈ O', orderCount ι Q ((τ ω).untopD 0) ω o = 0 := by
      filter_upwards [hfresh] with ω hω hωD
      have hpω : pattern (X ω) = π := hωD.2.2
      rw [hpω] at hω
      exact ⟨fun x hx => hω.1 x (hs'' x hx), fun o ho => hω.2 o (hO' o ho)⟩
    have h := stopped_cyl hQ τ hτ hfin (X ⁻¹' s ∩ Dπ) ((hX hs).inter hDπτ) s'' a O' b hfr
    rw [show X ⁻¹' s ∩ cyl s'' a O' b ∩ Dπ = (X ⁻¹' s ∩ Dπ) ∩ cyl s'' a O' b by
      ext ω; simp only [Set.mem_inter_iff]; tauto, h, mul_comm]

/-- Step 4: the frozen bound on one pattern piece. -/
theorem piece_bound (hfin : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (hX : Measurable[hτ.measurableSpace] X) (hpat : Measurable pattern)
    (A : S → Set (RandomSources ι M))
    (hA : MeasurableSet {q : S × RandomSources ι M | q.2 ∈ A q.1})
    (hloc : ∀ x, DependsOnly ι (pattern x) (A x))
    (hfresh : ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι Q ((τ ω).untopD 0) (pattern (X ω)) ω)
    (good : Set S) (hgood : ∀ᵐ ω ∂sourcesLaw ι M, X ω ∈ good)
    (p : ℝ) (hp : ∀ x ∈ good, sourcesLaw ι M (A x) ≤ ENNReal.ofReal p)
    (π : FreshPattern ι) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[hτ.measurableSpace] D) :
    sourcesLaw ι M (D ∩ X ⁻¹' (pattern ⁻¹' {π}) ∩ {ω | ω ∈ A (X ω)}) ≤
      ENNReal.ofReal p * sourcesLaw ι M (D ∩ X ⁻¹' (pattern ⁻¹' {π})) := by
  set μ := sourcesLaw ι M
  set Dπ := D ∩ X ⁻¹' (pattern ⁻¹' {π}) with hDπdef
  set Â := {q : S × RandomSources ι M | q.2 ∈ A q.1}
  have hle := hτ.measurableSpace_le
  have hXm : Measurable X := hX.mono hle le_rfl
  have hDπ : MeasurableSet Dπ := hle _ (hD.inter (patternSet_measurable hX hpat π))
  have hG : Measurable (fun ω => (X ω, proj π ω)) := hXm.prodMk (proj_measurable π)
  have hloc' : ∀ ω ∈ Dπ, DependsOnly ι π (A (X ω)) := by
    intro ω hω
    have hpω : pattern (X ω) = π := hω.2
    rw [← hpω]
    exact hloc _
  have hset : Dπ ∩ {ω | ω ∈ A (X ω)} = (fun ω => (X ω, proj π ω)) ⁻¹' Â ∩ Dπ := by
    ext ω
    constructor
    · rintro ⟨hωD, hωA⟩
      exact ⟨(mem_proj_iff (hloc' ω hωD) ω).mpr hωA, hωD⟩
    · rintro ⟨hωA, hωD⟩
      exact ⟨hωD, (mem_proj_iff (hloc' ω hωD) ω).mp hωA⟩
  rw [hset, ← Measure.restrict_apply (hG hA), ← Measure.map_apply hG hA,
    map_pair_restrict hfin hX hpat hfresh π D hD, Measure.prod_apply hA,
    lintegral_map (measurable_measure_prodMk_left hA) hXm]
  calc ∫⁻ ω, (μ.map (proj π)) (Prod.mk (X ω) ⁻¹' Â) ∂(μ.restrict Dπ)
      ≤ ∫⁻ _ω, ENNReal.ofReal p ∂(μ.restrict Dπ) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hDπ, ae_restrict_of_ae hgood] with ω hωD hωg
        rw [Measure.map_apply (proj_measurable π) (hA.preimage measurable_prodMk_left)]
        have : proj π ⁻¹' (Prod.mk (X ω) ⁻¹' Â) = A (X ω) := by
          ext ω'
          exact mem_proj_iff (hloc' ω hωD) ω'
        rw [this]
        exact hp _ hωg
    _ = ENNReal.ofReal p * μ Dπ := setLIntegral_const _ _

/-- Step 5: summing over the countably many patterns. -/
theorem set_bound (hfin : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (hX : Measurable[hτ.measurableSpace] X) (hpat : Measurable pattern)
    (A : S → Set (RandomSources ι M))
    (hA : MeasurableSet {q : S × RandomSources ι M | q.2 ∈ A q.1})
    (hloc : ∀ x, DependsOnly ι (pattern x) (A x))
    (hfresh : ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι Q ((τ ω).untopD 0) (pattern (X ω)) ω)
    (good : Set S) (hgood : ∀ᵐ ω ∂sourcesLaw ι M, X ω ∈ good)
    (p : ℝ) (hp : ∀ x ∈ good, sourcesLaw ι M (A x) ≤ ENNReal.ofReal p)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[hτ.measurableSpace] D) :
    sourcesLaw ι M (D ∩ {ω | ω ∈ A (X ω)}) ≤ ENNReal.ofReal p * sourcesLaw ι M D := by
  set μ := sourcesLaw ι M
  have hle := hτ.measurableSpace_le
  have hcover : D ∩ {ω | ω ∈ A (X ω)} =
      ⋃ π, (D ∩ X ⁻¹' (pattern ⁻¹' {π}) ∩ {ω | ω ∈ A (X ω)}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨pattern (X ω), ⟨h.1, rfl⟩, h.2⟩, fun ⟨_, ⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
  have hDeq : D = ⋃ π, D ∩ X ⁻¹' (pattern ⁻¹' {π}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨pattern (X ω), h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun π : FreshPattern ι => D ∩ X ⁻¹' (pattern ⁻¹' {π}))) := by
    intro π π' hne
    refine Set.disjoint_left.mpr fun ω h h' => hne ?_
    have e1 : pattern (X ω) = π := h.2
    have e2 : pattern (X ω) = π' := h'.2
    rw [← e1, ← e2]
  calc μ (D ∩ {ω | ω ∈ A (X ω)})
      ≤ ∑' π, μ (D ∩ X ⁻¹' (pattern ⁻¹' {π}) ∩ {ω | ω ∈ A (X ω)}) := by
        rw [hcover]
        exact measure_iUnion_le _
    _ ≤ ∑' π, ENNReal.ofReal p * μ (D ∩ X ⁻¹' (pattern ⁻¹' {π})) :=
        ENNReal.tsum_le_tsum fun π =>
          piece_bound hfin hX hpat A hA hloc hfresh good hgood p hp π D hD
    _ = ENNReal.ofReal p * μ D := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hdisj fun π =>
          hle _ (hD.inter (patternSet_measurable hX hpat π)), ← hDeq]

end Main

end Freeze

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78
open AndersonAC.S2

/-- **C2 (corrected contract) proved.** -/
theorem freezing_proof : FreezingStatementNonneg := by
  intro ι _ _ M Q hQ τ hτ hfin S _ X hX pattern hpat A hA hloc hfresh good hgood p hp0 hp
  set μ := sourcesLaw ι M
  have hle := hτ.measurableSpace_le
  have hXm : Measurable X := hX.mono hle le_rfl
  set E := {ω' | ω' ∈ A (X ω')} with hEdef
  have hE : MeasurableSet E := (hXm.prodMk measurable_id) hA
  have hf : Integrable (E.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hE
  refine ae_le_of_ae_le_trim (hm := hle) ?_
  refine ae_le_of_forall_setIntegral_le
    (integrable_condExp.trim hle stronglyMeasurable_condExp) (integrable_const p) ?_
  intro s hs _
  rw [← setIntegral_trim hle stronglyMeasurable_condExp hs, setIntegral_condExp hle hf hs,
    ← setIntegral_trim hle stronglyMeasurable_const hs, setIntegral_indicator hE,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one]
  have hb := Freeze.set_bound hfin hX hpat A hA hloc hfresh good hgood p hp s hs
  have hb' := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0] at hb'
  rw [mul_comm]
  exact hb'

end AndersonAC.AgentS78
