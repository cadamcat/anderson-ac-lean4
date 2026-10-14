import AndersonAC.S9Fin.PoissonTrace
import AndersonAC.S9Fin.ProbabilityStatements

noncomputable section
open MeasureTheory AndersonAC.S9
open scoped ENNReal

namespace AndersonAC.SolS9

universe u v
variable {n : Type u} [Fintype n] [DecidableEq n]

def finiteCountingMeasure (H : Matrix n n ℂ) (hH : H.IsHermitian) : Measure ℝ :=
  ∑ i, Measure.dirac (hH.eigenvalues i)

lemma finiteCountingMeasure_univ (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    finiteCountingMeasure H hH Set.univ = Fintype.card n := by
  simp [finiteCountingMeasure, Measure.finsetSum_apply]

instance finiteCountingMeasure_finite (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    IsFiniteMeasure (finiteCountingMeasure H hH) := by
  constructor
  rw [finiteCountingMeasure_univ]
  exact ENNReal.natCast_lt_top _

lemma finiteCountingMeasure_Icc (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) :
    finiteCountingMeasure H hH (Set.Icc (E - δ) (E + δ)) =
      (windowRank H hH E δ : ℝ≥0∞) := by
  classical
  have hm : ∀ i : n, hH.eigenvalues i ∈ Set.Icc (E - δ) (E + δ) ↔
      |hH.eigenvalues i - E| ≤ δ := by
    intro i
    simp only [Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [finiteWindowRank_eq_card, Fintype.card_subtype]
  simp only [finiteCountingMeasure, Measure.finsetSum_apply,
    Measure.dirac_apply' _ measurableSet_Icc, Set.indicator_apply, Pi.one_apply, hm]
  exact Finset.sum_boole (fun i : n => |hH.eigenvalues i - E| ≤ δ) Finset.univ

lemma finiteCountingMeasure_measurable (hRank : WindowRankMeasurableStatement.{u,v})
    {Ξ : Type v} [MeasurableSpace Ξ] (H : Ξ → Matrix n n ℂ)
    (hH : ∀ ξ, (H ξ).IsHermitian) (hM : Measurable H) :
    Measurable (fun ξ => finiteCountingMeasure (H ξ) (hH ξ)) := by
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Icc ℝ)) (isPiSystem_Icc id id)
  · rintro S ⟨a, b, hab, rfl⟩
    have hm := hRank n Ξ H hH hM ((a + b) / 2) ((b - a) / 2)
    have heq : (fun ξ => finiteCountingMeasure (H ξ) (hH ξ) (Set.Icc a b)) =
        fun ξ => ENNReal.ofReal
          (windowRank (H ξ) (hH ξ) ((a + b) / 2) ((b - a) / 2) : ℝ) := by
      funext ξ
      have ha : (a + b) / 2 - (b - a) / 2 = a := by ring
      have hb : (a + b) / 2 + (b - a) / 2 = b := by ring
      calc
        finiteCountingMeasure (H ξ) (hH ξ) (Set.Icc a b) =
            finiteCountingMeasure (H ξ) (hH ξ)
              (Set.Icc ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2)) := by
          rw [ha, hb]
        _ = _ := by rw [finiteCountingMeasure_Icc]; simp
    rw [heq]
    exact ENNReal.measurable_ofReal.comp hm
  · simp only [finiteCountingMeasure_univ]
    exact measurable_const

def averagedCountingMeasure {Ξ : Type v} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (H : Ξ → Matrix n n ℂ) (hH : ∀ ξ, (H ξ).IsHermitian) : Measure ℝ :=
  μ.bind (fun ξ => finiteCountingMeasure (H ξ) (hH ξ))

lemma averagedCountingMeasure_finite (hRank : WindowRankMeasurableStatement.{u,v})
    {Ξ : Type v} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsFiniteMeasure μ]
    (H : Ξ → Matrix n n ℂ) (hH : ∀ ξ, (H ξ).IsHermitian) (hM : Measurable H) :
    IsFiniteMeasure (averagedCountingMeasure μ H hH) := by
  have hm := finiteCountingMeasure_measurable hRank H hH hM
  constructor
  rw [averagedCountingMeasure, Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp only [finiteCountingMeasure_univ, lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (measure_lt_top μ Set.univ)

lemma averagedCountingMeasure_Icc_toReal (hRank : WindowRankMeasurableStatement.{u,v})
    {Ξ : Type v} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (H : Ξ → Matrix n n ℂ) (hH : ∀ ξ, (H ξ).IsHermitian) (hM : Measurable H) (E δ : ℝ) :
    (averagedCountingMeasure μ H hH (Set.Icc (E - δ) (E + δ))).toReal =
      ∫ ξ, (windowRank (H ξ) (hH ξ) E δ : ℝ) ∂μ := by
  have hm := finiteCountingMeasure_measurable hRank H hH hM
  rw [averagedCountingMeasure, Measure.bind_apply measurableSet_Icc hm.aemeasurable]
  have heq : (fun ξ => finiteCountingMeasure (H ξ) (hH ξ) (Set.Icc (E - δ) (E + δ))) =
      fun ξ => ENNReal.ofReal (windowRank (H ξ) (hH ξ) E δ : ℝ) := by
    funext ξ
    rw [finiteCountingMeasure_Icc]
    simp
  rw [heq]
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all μ (fun ξ => Nat.cast_nonneg (windowRank (H ξ) (hH ξ) E δ)))
    (hRank n Ξ H hH hM E δ).aestronglyMeasurable).symm

end AndersonAC.SolS9
