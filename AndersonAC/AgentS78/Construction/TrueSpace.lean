import AndersonAC.S2.BinaryProduct
import AndersonAC.S2.Binary

/-!
# The enlarged probability space

02-state.tex:68–90, 126–135. The run uses the §2 query model `RandomSources (Torus d m) M`
with law `sourcesLaw` (true signs `Sum.inl (i, k)`, auxiliary signs `Sum.inr k`, uniform
orders). The true potential at `i` is the binary value of its true signs
(history-binary, with `coupling = 1`; the coupling multiplies it in the Hamiltonian).
`trueConfig_law`: its unconditional law is exactly `torusLaw d m`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2

/-- The true binary digits of site `i`. -/
def trueDigits {d m : ℕ} {M : ℕ → ℕ} (ω : RandomSources (OAI.Anderson.Torus d m) M)
    (i : OAI.Anderson.Torus d m) : ℕ → Bool := fun k => ω.1 (Sum.inl (i, k))

theorem binaryValue_one_mem (a : ℕ → Bool) : binaryValue 1 a ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := AndersonAC.S2.binaryValue_bound 1 a
  rw [abs_one] at h
  exact abs_le.mp h

/-- The true potential configuration of a sample of the enlarged space. -/
def trueConfig {d m : ℕ} {M : ℕ → ℕ} (ω : RandomSources (OAI.Anderson.Torus d m) M) :
    OAI.Anderson.TorusConfiguration d m :=
  fun i => ⟨binaryValue 1 (trueDigits ω i), binaryValue_one_mem _⟩

theorem singleSite_val_embedding (ι : Type) [Fintype ι] :
    MeasurableEmbedding (fun (c : ι → OAI.Anderson.SingleSite) i => (c i : ℝ)) := by
  have hrange : Set.range (fun (c : ι → OAI.Anderson.SingleSite) i => (c i : ℝ)) =
      Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1) := by
    ext f; constructor
    · rintro ⟨c, rfl⟩ i _; exact (c i).2
    · intro hf; exact ⟨fun i => ⟨f i, hf i (Set.mem_univ i)⟩, rfl⟩
  refine MeasurableEmbedding.of_measurable_inverse_on_range
    (g := fun f i => (⟨max (-1) (min 1 (f.1 i)), le_max_left _ _,
      max_le (by norm_num) (min_le_left _ _)⟩ : OAI.Anderson.SingleSite))
    (by fun_prop) ?_ ?_ ?_
  · rw [hrange]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  · apply Measurable.of_eval; intro i
    apply Measurable.subtype_mk
    exact (measurable_const.max (measurable_const.min
      ((measurable_pi_apply i).comp measurable_subtype_coe)))
  · intro c; funext i; apply Subtype.ext
    simp only [Set.rangeFactorization]
    rw [min_eq_right (c i).2.2, max_eq_right (c i).2.1]

theorem trueConfig_val_measurable (d m : ℕ) (M : ℕ → ℕ) :
    Measurable (fun ω : RandomSources (OAI.Anderson.Torus d m) M => fun i =>
      binaryValue 1 (fun k => ω.1 (Sum.inl (i, k)))) := by
  apply Measurable.of_eval; intro i
  exact (AndersonAC.S2.binaryValue_measurable 1).comp
    (Measurable.of_eval fun k => (measurable_pi_apply (Sum.inl (i, k))).comp measurable_fst)

theorem trueConfig_measurable (d m : ℕ) (M : ℕ → ℕ) :
    Measurable (trueConfig (d := d) (m := m) (M := M)) := by
  have he := singleSite_val_embedding (OAI.Anderson.Torus d m)
  exact (he.measurable_comp_iff).mp (trueConfig_val_measurable d m M)

/-- The true potential has the product law as its unconditional marginal. -/
theorem trueConfig_law (d m : ℕ) (M : ℕ → ℕ) :
    (sourcesLaw (OAI.Anderson.Torus d m) M).map trueConfig = OAI.Anderson.torusLaw d m := by
  have he := singleSite_val_embedding (OAI.Anderson.Torus d m)
  have h := AndersonAC.S2.binary_true_product_law d m M
  have hcomp : (fun ω : RandomSources (OAI.Anderson.Torus d m) M => fun i =>
      binaryValue 1 (fun k => ω.1 (Sum.inl (i, k)))) =
      (fun (c : OAI.Anderson.TorusConfiguration d m) i => (c i : ℝ)) ∘ trueConfig := rfl
  rw [hcomp, ← Measure.map_map he.measurable (trueConfig_measurable d m M)] at h
  rw [← he.comap_map ((sourcesLaw (OAI.Anderson.Torus d m) M).map trueConfig), h,
    he.comap_map]

end AndersonAC.AgentS78
