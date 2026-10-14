import AndersonAC.AgentS6Budget.HeatBias
import AndersonAC.AgentS6Budget.Predictable
import AndersonAC.L64.Residual

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

def runningCoefficient (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) : Ω → ℂ :=
  {ω | k < q.stop ω}.indicator
    (fun ω => heatCoefficient t (r ω (q.pivot k ω))
      ((q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)) (q.residual k ω))

theorem runningCoefficient_of_running (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (hk : k < q.stop ω) :
    runningCoefficient q k ω = heatCoefficient t (r ω (q.pivot k ω))
      ((q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)) (q.residual k ω) := by
  exact Set.indicator_of_mem (s := {ω : Ω | k < q.stop ω}) (a := ω) hk _

theorem runningCoefficient_of_stopped (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (hk : ¬k < q.stop ω) : runningCoefficient q k ω = 0 := by
  exact Set.indicator_of_notMem (s := {ω : Ω | k < q.stop ω}) (a := ω) hk _

theorem runningCoefficient_adapted (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    StronglyMeasurable[q.history (k + 1)] (runningCoefficient q k) := by
  have hρ := (pivot_damping_adapted q k).mono (q.history.mono (by omega : k ≤ k + 1))
  have hγ := (pivot_diagonal_adapted q k).mono (q.history.mono (by omega : k ≤ k + 1))
  have hξ := Complex.continuous_ofReal.comp_stronglyMeasurable (q.residual_revealed k)
  have ha : StronglyMeasurable[q.history (k + 1)]
      (fun ω => (q.residual k ω : ℂ) + (t : ℂ) * r ω (q.pivot k ω)) :=
    hξ.add (stronglyMeasurable_const.mul hρ)
  have hrun : MeasurableSet[q.history (k + 1)] {ω | k < q.stop ω} :=
    (q.history.mono (Nat.le_succ k)) _ (running_measurableSet q k)
  unfold runningCoefficient heatCoefficient
  exact (ha.neg.div (stronglyMeasurable_const.mul
    (stronglyMeasurable_const.add (ha.mul hγ)))).indicator
      hrun

/-- A version of the scalar estimate accepting the almost-everywhere variance defect. -/
theorem masked_heatCoefficient_mean_bound_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (k : ℕ) (A : Set Ω) (hA : MeasurableSet[F k] A)
    (t C : ℝ) (hC : 1 ≤ C) (hsmall : AndersonAC.L64.Small t C)
    (ρ γ : Ω → ℂ) (ξ η : Ω → ℝ)
    (hρ : StronglyMeasurable[F k] ρ) (hγ : StronglyMeasurable[F k] γ)
    (hξm : Measurable ξ) (hξI : Integrable ξ μ)
    (hξ2I : Integrable (fun ω => ξ ω ^ 2) μ)
    (hρbound : ∀ ω ∈ A, ‖ρ ω‖ ≤ C) (hγbound : ∀ ω ∈ A, ‖γ ω‖ ≤ C)
    (hξbound : ∀ ω ∈ A, |ξ ω| ≤ C * Real.sqrt t)
    (hmean : ∀ᵐ ω ∂μ, ω ∈ A → μ[ξ | F k] ω = 0)
    (hsecond : ∀ᵐ ω ∂μ, ω ∈ A → μ[(fun ω => ξ ω ^ 2) | F k] ω = t - η ω)
    (hη : ∀ᵐ ω ∂μ, ω ∈ A → 0 ≤ η ω ∧ η ω ≤ C * t ^ 2)
    (hlag : ∀ ω ∈ A, ‖γ ω - ρ ω‖ ≤ C * t ^ betaW) :
    ∀ᵐ ω ∂μ, ω ∈ A →
      ‖μ[A.indicator (fun ω => heatCoefficient t (ρ ω) (γ ω) (ξ ω)) | F k] ω‖ ≤
        20 * C ^ 5 * Real.sqrt t * t ^ betaW := by
  let η' : Ω → ℝ := fun ω => max 0 (min (η ω) (C * t ^ 2))
  have hη' : ∀ ω ∈ A, |η' ω| ≤ C * t ^ 2 := by
    intro ω _
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by positivity) (min_le_right _ _)
  have hsec' : ∀ᵐ ω ∂μ, ω ∈ A →
      μ[(fun ω => ξ ω ^ 2) | F k] ω = t - η' ω := by
    filter_upwards [hsecond, hη] with ω hs hη hω
    have he : η' ω = η ω := by
      simp only [η', min_eq_left (hη hω).2, max_eq_right (hη hω).1]
    rw [he]
    exact hs hω
  exact masked_heatCoefficient_mean_bound μ F k A hA t C hsmall.pos hsmall.le_one hC
    hsmall ρ γ ξ η' hρ hγ hξm hξI hξ2I hρbound hγbound hξbound hmean hsec' hη' hlag

theorem runningCoefficient_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (d : ℕ) (c K Cloc C : ℝ)
    (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ)
    (hlocal : TrialLocalInput q μ d c K Cloc dist collapsed ell)
    (hC : 1 ≤ C) (hKC : K ≤ C) (hsmall : AndersonAC.L64.Small t C)
    (hpre : ∀ k ω, k < q.stop ω → HeatPrestate t C
      (fun i : {i // i ∈ (q.state k ω).active} => r ω i) (trialInverse t (r ω) (q.state k ω)))
    (hpiv : ∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2) :
    (∀ k ω, ‖runningCoefficient q k ω‖ ≤ 4 * C) ∧
    (∀ k, ∀ᵐ ω ∂μ, ‖μ[runningCoefficient q k | q.history k] ω‖ ≤
      20 * C ^ 5 * Real.sqrt t * t ^ betaW) := by
  have hC0 : 0 ≤ C := hsmall.C_nonneg
  have ht : 0 < t := hsmall.pos
  have hdiag : ∀ k ω, k < q.stop ω →
      ‖(q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)‖ ≤ C ∧
      ‖r ω (q.pivot k ω)‖ ≤ C ∧
      ‖(q.state k ω).hatG (q.pivot k ω) (q.pivot k ω) - r ω (q.pivot k ω)‖ ≤ C * t ^ betaW := by
    intro k ω hk
    have hx := (q.heat k ω hk).choose
    have heq := hatG_eq_trialInverse q k ω hk.le ⟨q.pivot k ω, hx⟩ ⟨q.pivot k ω, hx⟩
    obtain ⟨hbound, hlag, -⟩ := hpre k ω hk
    have hb := hbound ⟨q.pivot k ω, hx⟩
    have hl := hlag ⟨q.pivot k ω, hx⟩
    rw [← heq] at hb hl
    exact ⟨by linarith [norm_nonneg (r ω (q.pivot k ω))],
      by linarith [norm_nonneg ((q.state k ω).hatG (q.pivot k ω) (q.pivot k ω))], hl⟩
  have hξ : ∀ k ω, k < q.stop ω → |q.residual k ω| ≤ C * Real.sqrt t := by
    intro k ω hk
    exact (hlocal.residual_bound k ω hk (hpiv k ω hk)).trans
      (mul_le_mul_of_nonneg_right hKC (Real.sqrt_nonneg _))
  refine ⟨?_, ?_⟩
  · intro k ω
    by_cases hk : k < q.stop ω
    · rw [runningCoefficient_of_running q k ω hk]
      exact AndersonAC.L64.norm_hc_le hsmall (hdiag k ω hk).2.1 (hdiag k ω hk).1 (hξ k ω hk)
    · rw [runningCoefficient_of_stopped q k ω hk, norm_zero]
      exact mul_nonneg (by norm_num) hC0
  · intro k
    let A : Set Ω := {ω | k < q.stop ω}
    obtain ⟨η, -, hη⟩ := hlocal.residual_variance k
    have hηbound : ∀ᵐ ω ∂μ, ω ∈ A → 0 ≤ η ω ∧ η ω ≤ C * t ^ 2 := by
      filter_upwards [hη] with ω h hω
      obtain ⟨h0, h1, -⟩ := h hω (hpiv k ω hω)
      have h0' : 0 ≤ η ω := by
        have hmul := mul_nonneg h0 hsmall.pos.le
        rwa [div_mul_cancel₀ _ hsmall.pos.ne'] at hmul
      have h1' := (div_le_iff₀ hsmall.pos).mp h1
      refine ⟨h0', ?_⟩
      calc
        η ω ≤ K * t ^ 2 := by nlinarith [h1']
        _ ≤ C * t ^ 2 := mul_le_mul_of_nonneg_right hKC (sq_nonneg t)
    have hmean : ∀ᵐ ω ∂μ, ω ∈ A → μ[q.residual k | q.history k] ω = 0 := by
      filter_upwards [hlocal.residual_mean k] with ω h hω
      exact h hω (hpiv k ω hω)
    have hsecond : ∀ᵐ ω ∂μ, ω ∈ A →
        μ[(fun ω => q.residual k ω ^ 2) | q.history k] ω = t - η ω := by
      filter_upwards [hη] with ω h hω
      exact (h hω (hpiv k ω hω)).2.2
    have hb := masked_heatCoefficient_mean_bound_ae μ q.history k A (running_measurableSet q k)
      t C hC hsmall (fun ω => r ω (q.pivot k ω))
      (fun ω => (q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)) (q.residual k) η
      (pivot_damping_adapted q k) (pivot_diagonal_adapted q k)
      ((q.residual_revealed k).mono (q.history.le _)).measurable
      (hlocal.residual_integrable k) (hlocal.residual_square_integrable k)
      (fun ω hω => (hdiag k ω hω).2.1) (fun ω hω => (hdiag k ω hω).1)
      (hξ k) hmean hsecond hηbound (fun ω hω => (hdiag k ω hω).2.2)
    have hI : Integrable (runningCoefficient q k) μ := by
      apply (integrable_const (4 * C)).mono'
        ((runningCoefficient_adapted q k).mono (q.history.le _)).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        by_cases hk : k < q.stop ω
        · rw [runningCoefficient_of_running q k ω hk]
          exact AndersonAC.L64.norm_hc_le hsmall (hdiag k ω hk).2.1 (hdiag k ω hk).1 (hξ k ω hk)
        · rw [runningCoefficient_of_stopped q k ω hk, norm_zero]
          exact mul_nonneg (by norm_num) hC0
    have hmask := condExp_indicator (m := q.history k) hI (running_measurableSet q k)
    have hid : A.indicator (runningCoefficient q k) = runningCoefficient q k := by
      funext ω
      by_cases h : ω ∈ A <;> simp [runningCoefficient, A, h]
    rw [hid] at hmask
    filter_upwards [hb, hmask] with ω hb hm
    by_cases hω : ω ∈ A
    · exact hb hω
    · rw [hm, Set.indicator_of_notMem hω, norm_zero]
      positivity

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.runningCoefficient_bounds
