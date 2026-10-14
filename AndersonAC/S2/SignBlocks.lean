import AndersonAC.S2.SignFreshness
import AndersonAC.S2.BinaryLaws

/-! Infinite sign-block laws obtained from the finite flip action. -/

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace AndersonAC.SolS2
open AndersonAC.S2

section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem sources_signs_map {κ : Type*} (e : κ → SignIndex ι)
    (he : Function.Injective e) :
    (sourcesLaw ι M).map (fun ω k => ω.1 (e k)) =
      Measure.infinitePi (fun _ : κ => (PMF.uniformOfFintype Bool).toMeasure) := by
  have hm : Measurable (fun a : SignIndex ι → Bool => fun k => a (e k)) :=
    Measurable.of_eval (fun k => measurable_pi_apply (e k))
  change ((signsLaw ι).prod (ordersLaw M)).map
    ((fun a : SignIndex ι → Bool => fun k => a (e k)) ∘ Prod.fst) = _
  rw [← Measure.map_map hm measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  exact Measure.map_infinitePi_infinitePi_of_inj he

theorem map_restrict_signs_of_invariant {κ : Type*} (e : κ → SignIndex ι)
    (he : Function.Injective e) (D : Set (RandomSources ι M)) (hD : MeasurableSet D)
    (hinv : ∀ mask : Set (SignIndex ι), mask ⊆ Set.range e →
      (signFlip ι mask) ⁻¹' D = D) :
    ((sourcesLaw ι M).restrict D).map (fun ω k => ω.1 (e k)) =
      sourcesLaw ι M D •
        Measure.infinitePi (fun _ : κ => (PMF.uniformOfFintype Bool).toMeasure) := by
  classical
  let μ := sourcesLaw ι M
  let X := fun ω : RandomSources ι M => fun k => ω.1 (e k)
  have hX : Measurable X :=
    Measurable.of_eval (fun k => (measurable_pi_apply (e k)).comp measurable_fst)
  let P := fun s : Finset κ => μ D •
    Measure.pi (fun _ : s => (PMF.uniformOfFintype Bool).toMeasure)
  haveI : ∀ s, IsFiniteMeasure (P s) := fun s =>
    Measure.smul_finite _ (measure_ne_top μ D)
  apply IsProjectiveLimit.unique (P := P)
  · intro s
    rw [Measure.map_map (measurable_restrict s) hX]
    apply Measure.ext_of_singleton
    intro a
    let emb : κ ↪ SignIndex ι := ⟨e, he⟩
    let r := s.map emb
    let E : s ≃ r := Finset.equivMap emb s
    let p : r → Bool := fun x => a (E.symm x)
    have hcyl : (s.restrict ∘ X) ⁻¹' {a} = finiteSignCylinder ι r p := by
      ext ω
      change (fun k : s => ω.1 (e k.val)) = a ↔ ∀ x : r, ω.1 x.val = p x
      constructor
      · intro hw x
        have hx : e (E.symm x).val = x.val := congrArg Subtype.val (E.apply_symm_apply x)
        rw [← hx]
        exact congrFun hw (E.symm x)
      · intro hw
        funext k
        have hwk := hw (E k)
        change ω.1 (e k.val) = p (E k) at hwk
        simpa only [p, E.symm_apply_apply] using hwk
    rw [Measure.map_apply ((measurable_restrict s).comp hX) (measurableSet_singleton a),
      hcyl, Measure.restrict_apply (finiteSignCylinder_measurable ι r p), Set.inter_comm]
    change μ (D ∩ finiteSignCylinder ι r p) = P s {a}
    have hinvr : ∀ mask : Set (SignIndex ι), mask ⊆ r → (signFlip ι mask) ⁻¹' D = D := by
      intro mask hmask
      apply hinv mask
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp (hmask hx)
      exact ⟨k, rfl⟩
    have hf := finiteSignCylinder_factor ι r p D hD hinvr
    have hr : r.card = s.card := Finset.card_map emb
    rw [hr] at hf
    have hright : P s {a} ≠ ∞ := measure_ne_top (P s) _
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) hright).mp
    rw [hf]
    simp [P, μ, Measure.pi_singleton,
      ENNReal.toReal_mul, zpow_neg, zpow_natCast, mul_comm]
  · intro s
    rw [Measure.map_smul _ (measurable_restrict s).aemeasurable,
      Measure.infinitePi_map_restrict]

theorem suffixesUnqueried_measurable {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (sites : Finset ι) (h : ι → ℕ) :
    MeasurableSet (suffixesUnqueried ι Q q sites h) := by
  have hglobal : ∀ j, Measurable (Q j) := fun j =>
    Measurable.of_comap_le ((hQ.1 j).comap_le.trans (retained_le ι hQ j))
  have hseen : ∀ x, MeasurableSet {ω | x ∈ queriedSigns ι Q q ω} := by
    intro x
    simp only [queriedSigns, Set.mem_iUnion, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    apply MeasurableSet.iUnion
    intro hj
    exact hglobal j (show MeasurableSet {c | x ∈ querySigns ι c} from trivial)
  simp only [suffixesUnqueried, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
      (hseen (Sum.inl (i, k))).compl

theorem retained_fresh_event_invariant {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[retained ι Q q] D)
    (sites : Finset ι) (h : ι → ℕ) (mask : Set (SignIndex ι))
    (hmask : mask ⊆ {x | ∃ i ∈ sites, ∃ k, h i ≤ k ∧ x = Sum.inl (i, k)}) :
    (signFlip ι mask) ⁻¹' (D ∩ suffixesUnqueried ι Q q sites h) =
      D ∩ suffixesUnqueried ι Q q sites h := by
  have hfwd : ∀ ω ∈ D ∩ suffixesUnqueried ι Q q sites h,
      signFlip ι mask ω ∈ D ∩ suffixesUnqueried ι Q q sites h := by
    intro ω hω
    have hd : Disjoint mask (queriedSigns ι Q q ω) := Set.disjoint_left.mpr (by
      intro x hx hseen
      obtain ⟨i, hi, k, hk, rfl⟩ := hmask hx
      exact hω.2 i hi k hk hseen)
    obtain ⟨hinfo, hseen⟩ := signFlip_retained ι Q hQ q ω mask hd
    refine ⟨(hinfo D hD).mp hω.1, ?_⟩
    intro i hi k hk
    rw [← hseen]
    exact hω.2 i hi k hk
  ext ω
  constructor
  · intro hω
    have hw := hfwd (signFlip ι mask ω) hω
    simpa only [signFlip_involutive ι mask ω] using hw
  · exact hfwd ω

end Queries
end AndersonAC.SolS2
