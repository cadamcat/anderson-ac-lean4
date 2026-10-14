import AndersonAC.S9Fin.PoissonCounting
import AndersonAC.S9Fin.Expectation
import AndersonAC.S9Fin.FiniteAveragingStatement

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9
open scoped ENNReal

namespace AndersonAC.SolS9

/-- The lead's sharp Poisson-measure contract, copied as an explicit input
without importing its statement inventory. -/
def FinitePoissonDominationInput : Prop :=
  ∀ (μ : Measure ℝ), IsFiniteMeasure μ → ∀ C : ℝ, 0 ≤ C →
    (∀ E η : ℝ, 0 < η →
      (AndersonAC.Blueprint.borelTransform μ ((E : ℂ) + η * Complex.I)).im ≤ Real.pi * C) →
    μ ≤ ENNReal.ofReal C • volume

lemma scalarQ_torus_integrable (d m : ℕ) (coupling E η : ℝ) (hη : 0 < η) (i : Torus d m) :
    Integrable (fun ω => scalarQ (periodicHamiltonian coupling ω) E η i) (torusLaw d m) := by
  refine ⟨(scalarQ_measurable _ (continuous_periodicHamiltonian d m coupling).measurable
    E η i).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := η⁻¹) ?_⟩
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans ((matrix_entry_norm_le _ i i).trans
    (matrixResolvent_norm_pos _ (periodicHamiltonian_isHermitian_proof d m coupling ω)
      E η hη))

set_option maxHeartbeats 800000 in
/-- All analytic inputs are visible; no conditioned or certificate law occurs. -/
theorem finite_wegner_of_inputs (hRank : WindowRankMeasurableStatement.{0,0})
    (hAverage : FiniteScalarAveragingStatement.{0}) (hPoisson : FinitePoissonDominationInput)
    (d m : ℕ) (coupling E δ : ℝ) (hcoupling : 0 < coupling) (hδ : 0 ≤ δ)
    (hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian) :
    ∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E δ : ℝ) ∂torusLaw d m ≤
      (Fintype.card (Torus d m) : ℝ) * δ / coupling := by
  let H := periodicHamiltonian coupling (d := d) (m := m)
  have hM : Measurable H := (continuous_periodicHamiltonian d m coupling).measurable
  let ν := averagedCountingMeasure (torusLaw d m) H hH
  have hν : IsFiniteMeasure ν := averagedCountingMeasure_finite hRank _ H hH hM
  let N : ℝ := Fintype.card (Torus d m)
  let C : ℝ := N / (2 * coupling)
  have hC : 0 ≤ C := div_nonneg (Nat.cast_nonneg _) (by positivity)
  let ω0 : TorusConfiguration d m := fun _ => ⟨0, by norm_num⟩
  let K := periodicHamiltonian (0 : ℝ) ω0
  have hK : K.IsHermitian := periodicHamiltonian_isHermitian_proof d m 0 ω0
  have hdecomp : ∀ ω : TorusConfiguration d m,
      periodicHamiltonian coupling ω =
        K + (coupling : ℂ) • Matrix.diagonal (fun i => ((ω i : ℝ) : ℂ)) := by
    intro ω
    ext i j
    by_cases hij : i = j <;>
      simp [K, periodicHamiltonian, Matrix.one_apply, Matrix.diagonal_apply, hij]
  have hdom : ν ≤ ENNReal.ofReal C • volume := hPoisson ν hν C hC (by
    intro E' η' hη'
    rw [averagedCountingMeasure_poisson hRank _ H hH hM E' η' hη']
    have hb : ∀ i : Torus d m,
        (∫ ω, scalarQ (periodicHamiltonian coupling ω) E' η' i ∂torusLaw d m) ≤
          Real.pi / (2 * coupling) := by
      intro i
      have hi := hAverage (Torus d m) K hK coupling E' η' hcoupling hη' i
      simpa only [torusLaw, hdecomp] using hi
    calc
      (∫ ω, ∑ i, scalarQ (H ω) E' η' i ∂torusLaw d m) =
          ∑ i, ∫ ω, scalarQ (H ω) E' η' i ∂torusLaw d m :=
        integral_finsetSum _ (fun i _ => scalarQ_torus_integrable d m coupling E' η' hη' i)
      _ ≤ ∑ _ : Torus d m, Real.pi / (2 * coupling) :=
        Finset.sum_le_sum (fun i _ => hb i)
      _ = Real.pi * C := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [C, N]; ring)
  have hi := hdom (Set.Icc (E - δ) (E + δ))
  have htop : (ENNReal.ofReal C • volume) (Set.Icc (E - δ) (E + δ)) ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono htop hi
  rw [averagedCountingMeasure_Icc_toReal hRank _ H hH hM E δ] at hr
  have hlen : 0 ≤ E + δ - (E - δ) := by linarith
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hlen] at hr
  calc
    (∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E δ : ℝ) ∂torusLaw d m)
        ≤ C * (E + δ - (E - δ)) := hr
    _ = (Fintype.card (Torus d m) : ℝ) * δ / coupling := by dsimp [C, N]; ring

end AndersonAC.SolS9
