import AndersonAC.Blueprint.Target
import AndersonAC.Challenge

noncomputable section

open MeasureTheory ProbabilityTheory OAI.Anderson
open scoped ENNReal
open AndersonAC.Blueprint

namespace AndersonAC.MuseBridge

variable {d : ℕ} {a b : ℝ}

/-- The blueprint's uniform interval law is the conditional (uniform) law on `Icc a b`. -/
theorem uniformInterval_eq_cond (a b : ℝ) :
    uniformInterval a b = ProbabilityTheory.cond volume (Set.Icc a b) := by
  simp only [uniformInterval, ProbabilityTheory.cond, Real.volume_Icc]

/-- Each uniform coordinate has law `uniformInterval`. -/
theorem uniform_map_eq {Ω : Type} [MeasureSpace Ω] {V : Ω → ℝ} {P : Measure Ω}
    {a b : ℝ} (h : pdf.IsUniform V (Set.Icc a b) P volume) :
    P.map V = uniformInterval a b := by
  rw [uniformInterval_eq_cond]
  exact h.map_eq

/-- Joint measurability of an iid family. -/
theorem measurable_joint {Ω : Type} [MeasurableSpace Ω]
    {V : Site d → Ω → ℝ} (hmeas : ∀ n, Measurable (V n)) :
    Measurable (fun ω n => V n ω) :=
  Measurable.of_eval hmeas

/-- The joint law of an iid uniform family is the blueprint interval law. -/
theorem jointLaw_eq_intervalLaw {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {V : Site d → Ω → ℝ} (hmeas : ∀ n, Measurable (V n))
    (hiid : iIndepFun V volume)
    (huni : ∀ n, pdf.IsUniform (V n) (Set.Icc a b) volume volume) :
    (volume : Measure Ω).map (fun ω n => V n ω) = intervalLaw d a b := by
  have hmap := hiid.map_fun_eq_infinitePi_map hmeas
  rw [hmap]
  have hfun : (fun i => (volume : Measure Ω).map (V i))
      = (fun _ => uniformInterval a b) :=
    funext fun n => uniform_map_eq (huni n)
  rw [hfun]
  rfl

/-- Transfer of an `intervalLaw`-a.e. property to the original probability space. -/
theorem ae_of_intervalLaw_ae {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {V : Site d → Ω → ℝ} (hmeas : ∀ n, Measurable (V n))
    (hiid : iIndepFun V volume)
    (huni : ∀ n, pdf.IsUniform (V n) (Set.Icc a b) volume volume)
    {p : (Site d → ℝ) → Prop}
    (h : ∀ᵐ W ∂intervalLaw d a b, p W) :
    ∀ᵐ ω ∂(volume : Measure Ω), p (fun n => V n ω) := by
  have hjoint := jointLaw_eq_intervalLaw hmeas hiid huni
  rw [← hjoint] at h
  exact ae_of_ae_map (measurable_joint hmeas).aemeasurable h

instance : Countable (Site d) := by
  unfold Site
  infer_instance

/-- Each coordinate lies in `Icc a b` almost surely. -/
theorem ae_mem_Icc_of_uniform {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {V : Site d → Ω → ℝ} (hmeas : ∀ n, Measurable (V n))
    (huni : ∀ n, pdf.IsUniform (V n) (Set.Icc a b) volume volume)
    (n : Site d) :
    ∀ᵐ ω ∂(volume : Measure Ω), V n ω ∈ Set.Icc a b := by
  have hmap : (volume : Measure Ω).map (V n) = uniformInterval a b :=
    uniform_map_eq (huni n)
  have hnull : uniformInterval a b (Set.Icc a b)ᶜ = 0 := by
    simp only [uniformInterval, Measure.smul_apply, smul_eq_mul]
    have : volume.restrict (Set.Icc a b) (Set.Icc a b)ᶜ = 0 := by
      rw [Measure.restrict_apply measurableSet_Icc.compl]
      simp
    rw [this, mul_zero]
  rw [ae_iff]
  have hpre : (volume : Measure Ω) ((V n) ⁻¹' (Set.Icc a b)ᶜ) = 0 := by
    have hcongr := congrArg (· (Set.Icc a b)ᶜ) hmap
    simp only [Measure.map_apply (hmeas n) measurableSet_Icc.compl] at hcongr
    rw [hnull] at hcongr
    exact hcongr
  have heq : {ω | ¬V n ω ∈ Set.Icc a b} = (V n) ⁻¹' (Set.Icc a b)ᶜ := by
    ext ω
    simp
  rw [heq]
  exact hpre

/-- All coordinates lie in `Icc a b` simultaneously, almost surely. -/
theorem ae_forall_mem_Icc {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {V : Site d → Ω → ℝ} (hmeas : ∀ n, Measurable (V n))
    (huni : ∀ n, pdf.IsUniform (V n) (Set.Icc a b) volume volume) :
    ∀ᵐ ω ∂(volume : Measure Ω), ∀ n, V n ω ∈ Set.Icc a b :=
  ae_all_iff.mpr (fun n => ae_mem_Icc_of_uniform hmeas huni n)

/-- A uniform bound for any potential valued in `Icc a b`. -/
theorem abs_le_of_mem_Icc {x a b : ℝ} (hx : x ∈ Set.Icc a b) :
    |x| ≤ |a| + |b| := by
  rw [Set.mem_Icc] at hx
  have h1 : -|a| ≤ a := neg_abs_le a
  have h2 : a ≤ |a| := le_abs_self a
  have h3 : -|b| ≤ b := neg_abs_le b
  have h4 : b ≤ |b| := le_abs_self b
  have h5 : (0 : ℝ) ≤ |a| := abs_nonneg a
  have h6 : (0 : ℝ) ≤ |b| := abs_nonneg b
  rw [abs_le]
  constructor <;> linarith

/-- Almost every realization is uniformly bounded by `|a| + |b|`. -/
theorem ae_bounded_of_uniform {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {V : Site d → Ω → ℝ} (hmeas : ∀ n, Measurable (V n))
    (huni : ∀ n, pdf.IsUniform (V n) (Set.Icc a b) volume volume) :
    ∀ᵐ ω ∂(volume : Measure Ω), ∃ (M : ℝ) (_ : 0 ≤ M) (_ : ∀ x, |((fun n => V n ω) x)| ≤ M),
      True := by
  filter_upwards [ae_forall_mem_Icc hmeas huni] with ω hω
  exact ⟨|a| + |b|, add_nonneg (abs_nonneg _) (abs_nonneg _),
    fun x => abs_le_of_mem_Icc (hω x), trivial⟩

end AndersonAC.MuseBridge
