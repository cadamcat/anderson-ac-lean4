import AndersonAC.S2.SignBlocks

/-! Binary decoding of independent site blocks gives the true product law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AndersonAC.SolS2
open AndersonAC.S2

theorem map_binary_blocks {κ : Type*} (c : κ → ℝ) (hc : ∀ i, 0 < c i) :
    (Measure.infinitePi (fun _ : κ × ℕ => (PMF.uniformOfFintype Bool).toMeasure)).map
      (fun a i => binaryValue (c i) (fun k => a (i, k))) =
      Measure.infinitePi (fun i => uniformInterval (c i)) := by
  have hcur : Measurable (MeasurableEquiv.curry κ ℕ Bool) :=
    (MeasurableEquiv.curry κ ℕ Bool).measurable
  have hval : Measurable (fun a : κ → ℕ → Bool => fun i => binaryValue (c i) (a i)) :=
    Measurable.of_eval (fun i => (binaryValue_measurable _).comp (measurable_pi_apply i))
  change (Measure.infinitePi (fun _ : κ × ℕ => (PMF.uniformOfFintype Bool).toMeasure)).map
    ((fun a : κ → ℕ → Bool => fun i => binaryValue (c i) (a i)) ∘
      MeasurableEquiv.curry κ ℕ Bool) = _
  rw [← Measure.map_map hval hcur,
    Measure.infinitePi_map_curry (fun (_ : κ) (_ : ℕ) => (PMF.uniformOfFintype Bool).toMeasure)]
  change (Measure.infinitePi (fun _ : κ => AuxiliaryLaw)).map _ = _
  rw [Measure.infinitePi_map_pi (fun _ : κ => AuxiliaryLaw)
    (fun i => binaryValue_measurable (c i))]
  congr 1
  funext i
  exact binary_uniform (hc i)

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2

theorem binary_true_product_law (d m : ℕ) (M : ℕ → ℕ) :
    (sourcesLaw (Torus d m) M).map (fun ω i =>
      binaryValue 1 (fun k => ω.1 (Sum.inl (i, k)))) =
    (torusLaw d m).map (fun ω i => (ω i : ℝ)) := by
  let X := fun ω : RandomSources (Torus d m) M => fun x : Torus d m × ℕ =>
    ω.1 (Sum.inl x)
  let V := fun a : (Torus d m × ℕ) → Bool => fun i => binaryValue 1 (fun k => a (i, k))
  have hX : Measurable X := Measurable.of_eval fun x =>
    (measurable_pi_apply (Sum.inl x)).comp measurable_fst
  have hV : Measurable V := Measurable.of_eval fun i =>
    (binaryValue_measurable 1).comp (Measurable.of_eval fun k => measurable_pi_apply (i, k))
  change (sourcesLaw (Torus d m) M).map (V ∘ X) = _
  rw [← Measure.map_map hV hX, sources_signs_map (Torus d m) Sum.inl Sum.inl_injective,
    map_binary_blocks (fun _ => (1 : ℝ)) (fun _ => by norm_num)]
  change Measure.infinitePi (fun _ : Torus d m => uniformInterval 1) =
    (Measure.pi (fun _ : Torus d m => OAI.Anderson.uniformSite)).map _
  rw [Measure.pi_map_pi (fun _ => measurable_subtype_coe.aemeasurable),
    ← Measure.infinitePi_eq_pi]
  congr 1
  funext i
  rw [OAI.Anderson.uniformSite_map_val]
  norm_num [uniformInterval]

end AndersonAC.S2
