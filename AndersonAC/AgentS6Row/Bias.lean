import AndersonAC.AgentS6Row.TrialMoments
import AndersonAC.AgentS6Row.Integrability

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def zeroData : RowData := ⟨0, 0, 0, 0, 0⟩

def maskData (E : Set Ω) (D : Ω → RowData) (ω : Ω) : RowData where
  v := E.indicator (fun ω => (D ω).v) ω
  m := E.indicator (fun ω => (D ω).m) ω
  s := E.indicator (fun ω => (D ω).s) ω
  j := E.indicator (fun ω => (D ω).j) ω
  vn := E.indicator (fun ω => (D ω).vn) ω

lemma maskData_of_mem (E : Set Ω) (D : Ω → RowData) (ω : Ω) (hω : ω ∈ E) :
    maskData E D ω = D ω := by simp only [maskData, Set.indicator_of_mem hω]

lemma maskData_of_notMem (E : Set Ω) (D : Ω → RowData) (ω : Ω) (hω : ω ∉ E) :
    maskData E D ω = zeroData := by simp only [maskData, Set.indicator_of_notMem hω, zeroData]

lemma maskData_predictable {m : MeasurableSpace Ω} (E : Set Ω) (hE : MeasurableSet[m] E)
    (D : Ω → RowData)
    (hD : StronglyMeasurable[m] (fun ω => (D ω).v) ∧
      StronglyMeasurable[m] (fun ω => (D ω).m) ∧
      StronglyMeasurable[m] (fun ω => (D ω).s) ∧
      StronglyMeasurable[m] (fun ω => (D ω).j) ∧ StronglyMeasurable[m] (fun ω => (D ω).vn)) :
    StronglyMeasurable[m] (fun ω => (maskData E D ω).v) ∧
      StronglyMeasurable[m] (fun ω => (maskData E D ω).m) ∧
      StronglyMeasurable[m] (fun ω => (maskData E D ω).s) ∧
      StronglyMeasurable[m] (fun ω => (maskData E D ω).j) ∧
      StronglyMeasurable[m] (fun ω => (maskData E D ω).vn) :=
  ⟨hD.1.indicator hE, hD.2.1.indicator hE, hD.2.2.1.indicator hE,
    hD.2.2.2.1.indicator hE, hD.2.2.2.2.indicator hE⟩

def rowBiasConstant (K c : ℝ) : ℝ :=
  biasConstant c (remainderConstant K c) (2 * K / c) (meanConstant K) (secondConstant K)

lemma rowBiasConstant_pos {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c) : 0 < rowBiasConstant K c := by
  apply biasConstant_pos hc (remainderConstant_nonneg hK) (by positivity)
  · unfold meanConstant; positivity
  · unfold secondConstant; positivity

variable {n : ℕ} {core : Finset (Fin n)} {t : ℝ} {r : Ω → Fin n → ℂ}
  {g0 : Ω → Matrix (Fin n) (Fin n) ℂ} {order : Fin n ≃ Fin (Fintype.card (Fin n))}

set_option maxHeartbeats 1600000 in
/-- Conditional bias of a recorded fixed-ridge row change, uniform in the selected ridge. -/
theorem recorded_bias_bound (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (K c Cloc : ℝ)
    (hK : 0 ≤ K) (hc : 0 < c) (hs : Small t K) (hsθ : Real.sqrt t ≤ t ^ betaW)
    (hvnsmall : K / c * (t ^ betaW + 2 * coreCap d t * Real.sqrt (fourthCap t)) ≤ 1)
    (hfrosmall : 16 * KPhi K c * (leverageScale t) ^ 2 / t ≤ 1 / 4)
    (hcard : (core.card : ℝ) ≤ coreCap d t)
    (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ)
    (hlocal : TrialLocalInput q μ d c K Cloc dist collapsed ell)
    (hr : ∀ ω, BroadBounds c K (r ω))
    (hloc : ∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2)
    (hpre : ∀ k ω, k < q.stop ω → HeatPrestate t K
      (fun j : (q.state k ω).active => r ω j) (trialInverse t (r ω) (q.state k ω))) :
    ∀ k i, ∀ᵐ ω ∂μ, k < q.stop ω →
      |μ[(fun ω => recordedLeverageIncrement q k ω i) | q.history k] ω| ≤
        oneRowBias d t (rowBiasConstant K c) ‖heatV q k ω i‖ := by
  classical
  intro k i
  have ht : 0 < t := hs.pos
  let E := survivorEvent q k i
  have hE : MeasurableSet[q.history k] E := survivorEvent_measurable q k i
  let Draw : Ω → RowData := fun ω => trialRowData q k ω i
  let D := maskData E Draw
  let z := E.indicator (trialCoefficient q k)
  let f : Ω → ℝ := fun ω => recordedLeverageIncrement q k ω i
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos hs.pos _
  have hε := epsilonScale_lower d t hs.pos
  have hε0 : 0 ≤ epsilonScale d t := (Real.rpow_nonneg hs.pos.le betaW).trans hε.1
  have hR := remainderConstant_nonneg (c := c) hK
  have hM : 0 ≤ meanConstant K := by unfold meanConstant; positivity
  have hS : 0 ≤ secondConstant K := by unfold secondConstant; positivity
  have hRaw := fun ω (hω : ω ∈ E) => trialRowData_bounds q d K c hK hc hs hvnsmall hfrosmall hcard
    k ω i hω (hr ω) (hpre k ω hω.1)
    (hlocal.residual_bound k ω hω.1 (hloc k ω hω.1))
  have hDpred := maskData_predictable E hE Draw (trialRowData_predictable q k i)
  have hDb : ∀ ω, 0 ≤ (D ω).m ∧ (D ω).m ≤ 4 * leverageScale t ∧ ‖(D ω).v‖ ≤ 2 ∧
      ‖(D ω).s‖ ≤ 4 * leverageScale t ∧ ‖(D ω).j‖ ≤ 4 * leverageScale t / (Real.sqrt t * c) ∧
      0 ≤ (D ω).vn ∧ (D ω).vn ≤ 2 := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [show D ω = Draw ω from maskData_of_mem E Draw ω hω]
      obtain ⟨hm0, hm4, hv2, hs4, hj4, hn0, hn2, _, _⟩ := hRaw ω hω
      exact ⟨hm0, hm4, hv2, hs4, hj4, hn0, hn2⟩
    · rw [show D ω = zeroData from maskData_of_notMem E Draw ω hω]
      have h4 : 0 ≤ 4 * leverageScale t := by positivity
      have hj : 0 ≤ 4 * leverageScale t / (Real.sqrt t * c) := by positivity
      simp [zeroData, h4, hj]
  have hdev : ∀ ω ∈ E, |(D ω).vn - 1| ≤ (2 * K / c) * epsilonScale d t := by
    intro ω hω
    rw [show D ω = Draw ω from maskData_of_mem E Draw ω hω]
    obtain ⟨_, _, _, _, _, _, _, hd, _⟩ := hRaw ω hω
    exact hd
  have hfI : Integrable f μ := recorded_increment_integrable q μ k i
  have hrem : ∀ ω, |f ω - (D ω).affine (z ω)| ≤ remainderConstant K c *
      ((leverageScale t) ^ 2 * ‖(D ω).v‖ / Real.sqrt t + (leverageScale t) ^ 3 / t) := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [show D ω = Draw ω from maskData_of_mem E Draw ω hω, show z ω = trialCoefficient q k ω from Set.indicator_of_mem hω _]
      obtain ⟨_, _, _, _, _, _, _, _, hrm⟩ := hRaw ω hω
      exact hrm
    · have hf0 : f ω = 0 := by
        change recordedLeverageIncrement q k ω i = 0
        rw [congrFun (recordedIncrement_eq_indicator q k i) ω, Set.indicator_of_notMem hω]
      rw [hf0, show D ω = zeroData from maskData_of_notMem E Draw ω hω]
      simp only [zeroData, RowData.affine, RowData.a0, RowData.a2, RowData.kappa,
        norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, sub_self,
        zero_add, add_zero, Complex.zero_re, abs_zero, zero_div]
      positivity
  obtain ⟨hzm, hzb, hzmom⟩ := trial_coefficient_moments q μ d K c Cloc hK hs hsθ dist collapsed ell
    hlocal hr hloc hpre k E hE (fun ω hω => hω.1)
  have hce := conditional_row_bias μ (q.history.le k) E hE D f z t (leverageScale t) c (4 * K)
    (remainderConstant K c) (2 * K / c) (meanConstant K) (secondConstant K) (t ^ betaW) (epsilonScale d t)
    hs.pos hl.le hc (by positivity) hR (by positivity) hM hS (by positivity)
    hs.sqrt_le_one hε.1 hε.2 hDpred.1 hDpred.2.1 hDpred.2.2.1 hDpred.2.2.2.1 hDpred.2.2.2.2
    hDb hdev hzm hzb hfI hrem (hzmom.mono fun ω hh => hh.1) (hzmom.mono fun ω hh => hh.2)
  have hoff := recorded_increment_condExp_off q μ k i
  filter_upwards [hce, hoff] with ω hce hoff hk
  by_cases hω : ω ∈ E
  · have hh := hce hω
    have hv : (D ω).v = heatV q k ω i := by
      rw [show D ω = Draw ω from maskData_of_mem E Draw ω hω]
      simp only [Draw, trialRowData, runningV, if_pos hk]
    simpa only [rowBiasConstant, oneRowBias, hv] using hh
  · rw [hoff hω, abs_zero]
    unfold oneRowBias
    have hL := rowBiasConstant_pos hK hc
    positivity

end AndersonAC.AgentS6Row

#print axioms AndersonAC.AgentS6Row.recorded_bias_bound
