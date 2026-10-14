import AndersonAC.S2.Retained

/-! Measure-preserving sign flips and replay of retained adaptive queries. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AndersonAC.SolS2
open AndersonAC.S2

theorem uniformFinite_map_equiv {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (e : α ≃ α) :
    (PMF.uniformOfFintype α).toMeasure.map e = (PMF.uniformOfFintype α).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_finite e) (measurableSet_singleton a)]
  have hpre : e ⁻¹' {a} = {e.symm a} := by
    ext x
    constructor
    · intro hx
      have hh := congrArg e.symm hx
      simpa using hh
    · intro hx
      change x = e.symm a at hx
      change e x = a
      rw [hx, e.apply_symm_apply]
  rw [hpre]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

def flipSigns (mask : Set (SignIndex ι)) (ε : SignIndex ι → Bool) : SignIndex ι → Bool := by
  classical
  exact fun x => if x ∈ mask then !(ε x) else ε x

def signFlip (mask : Set (SignIndex ι)) (ω : RandomSources ι M) : RandomSources ι M :=
  (flipSigns ι mask ω.1, ω.2)

theorem flipSigns_measurable (mask : Set (SignIndex ι)) : Measurable (flipSigns ι mask) := by
  classical
  apply Measurable.of_eval
  intro x
  by_cases hx : x ∈ mask
  · simpa only [flipSigns, hx, ite_true, Function.comp_def] using
      (measurable_of_finite Bool.not).comp (measurable_pi_apply x)
  · simpa only [flipSigns, hx, ite_false] using measurable_pi_apply x

theorem signFlip_measurable (mask : Set (SignIndex ι)) :
    Measurable (signFlip (M := M) ι mask) :=
  ((flipSigns_measurable ι mask).comp measurable_fst).prodMk measurable_snd

theorem flipSigns_law (mask : Set (SignIndex ι)) :
    (signsLaw ι).map (flipSigns ι mask) = signsLaw ι := by
  classical
  let f : SignIndex ι → Bool → Bool := fun x b => if x ∈ mask then !b else b
  change (Measure.infinitePi (fun _ : SignIndex ι => (PMF.uniformOfFintype Bool).toMeasure)).map
    (fun ε x => f x (ε x)) = _
  rw [Measure.infinitePi_map_pi
    (fun _ : SignIndex ι => (PMF.uniformOfFintype Bool).toMeasure)
    (f := f) (fun x => measurable_of_finite (f x))]
  unfold signsLaw
  congr 1
  funext x
  by_cases hx : x ∈ mask
  · have he : f x = (Equiv.boolNot : Bool → Bool) := by
      funext b
      simp [f, hx]
    rw [he]
    exact uniformFinite_map_equiv Equiv.boolNot
  · have he : f x = id := by funext b; simp [f, hx]
    rw [he, Measure.map_id]

theorem signFlip_law (mask : Set (SignIndex ι)) :
    (sourcesLaw ι M).map (signFlip ι mask) = sourcesLaw ι M := by
  unfold sourcesLaw signFlip
  change ((signsLaw ι).prod (ordersLaw M)).map (Prod.map (flipSigns ι mask) id) = _
  rw [← Measure.map_prod_map _ _ (flipSigns_measurable ι mask) measurable_id,
    flipSigns_law, Measure.map_id]

theorem signFlip_involutive (mask : Set (SignIndex ι)) :
    Function.Involutive (signFlip (M := M) ι mask) := by
  classical
  intro ω
  apply Prod.ext
  · funext x
    by_cases hx : x ∈ mask <;> simp [signFlip, flipSigns, hx]
  · rfl

theorem signFlip_retained (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (ω : RandomSources ι M)
    (mask : Set (SignIndex ι)) (hfresh : Disjoint mask (queriedSigns ι Q q ω)) :
    SameInformation (retained ι Q q) ω (signFlip ι mask ω) ∧
      queriedSigns ι Q q ω = queriedSigns ι Q q (signFlip ι mask ω) := by
  classical
  have hp := retained_query_replay ι Q hQ.1 q ω (signFlip ι mask ω)
    (fun x hx => by
      have hn : x ∉ mask := fun hm => Set.disjoint_left.mp hfresh hm hx
      simp [signFlip, flipSigns, hn])
    (fun o j hj => rfl)
  constructor
  · exact transcript_sameInformation ι Q q hp.1 hp.2
  · ext x
    simp only [queriedSigns, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by simpa only [← hp.1 j hj] using hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by simpa only [hp.1 j hj] using hx⟩

end Queries
end AndersonAC.SolS2
