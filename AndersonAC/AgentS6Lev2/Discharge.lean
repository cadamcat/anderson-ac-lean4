import AndersonAC.AgentS6Lev2.Proof
import AndersonAC.AgentS6.Potential
import AndersonAC.AgentS6.Decomposition
import AndersonAC.AgentS6Row.Integrability

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open AndersonAC.S6
open scoped BigOperators

namespace AndersonAC.AgentS6Lev2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
  {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

theorem measurable_preW (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    Measurable (fun ω => AndersonAC.AgentS6.preW q k ω i) :=
  (AndersonAC.AgentS6.measurable_weights q (k := k) (j := k) le_rfl i).mono
    (q.history.le k) le_rfl

theorem measurable_postW (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    Measurable (fun ω => AndersonAC.AgentS6.postW q k ω i) :=
  (AndersonAC.AgentS6.measurable_weights q (k := k + 1) (j := k) (Nat.le_succ k) i).mono
    (q.history.le (k + 1)) le_rfl

theorem measurable_run (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    MeasurableSet {ω | k < q.stop ω} :=
  q.history.le k _ (AndersonAC.AgentS6.running_measurableSet q k)

theorem measurable_onRunning_pre (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ)
    (i : Fin n) :
    Measurable (fun ω => onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) := by
  have hpre : Measurable (fun ω => AndersonAC.AgentS6.preW q k ω i) :=
    measurable_preW q k i
  have hrun := measurable_run q k
  have heq : (fun ω => onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) =
      {ω | k < q.stop ω}.indicator (fun ω => AndersonAC.AgentS6.preW q k ω i) := by
    funext ω
    by_cases h : k < q.stop ω <;> simp [onRunning, h, Set.indicator]
  rw [heq]
  exact hpre.indicator hrun

theorem measurable_onRunning_post (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ)
    (i : Fin n) :
    Measurable (fun ω => onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) := by
  have hpost : Measurable (fun ω => AndersonAC.AgentS6.postW q k ω i) :=
    measurable_postW q k i
  have hrun := measurable_run q k
  have heq : (fun ω => onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) =
      {ω | k < q.stop ω}.indicator (fun ω => AndersonAC.AgentS6.postW q k ω i) := by
    funext ω
    by_cases h : k < q.stop ω <;> simp [onRunning, h, Set.indicator]
  rw [heq]
  exact hpost.indicator hrun

theorem leverage_mem_bounds (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω)
    (hk : k < q.stop ω) (i : Fin n) :
    0 ≤ AndersonAC.AgentS6.preW q k ω i ∧
      AndersonAC.AgentS6.preW q k ω i ≤ (core.card : ℝ) := by
  have hτ := q.running_ridge k ω hk
  have h0 := AndersonAC.AgentS6.leverage_nonneg
    (trialCross t (r ω) (q.state k ω)) hτ.le i
  have hle := AndersonAC.AgentS6Row.leverage_le_card
    (trialCross t (r ω) (q.state k ω)) (q.ridge k ω) hτ i
  rw [Fintype.card_coe] at hle
  simpa [AndersonAC.AgentS6.preW, trialWeights] using ⟨h0, hle⟩

theorem leverage_post_bounds (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω)
    (hk : k < q.stop ω) (i : Fin n) :
    0 ≤ AndersonAC.AgentS6.postW q k ω i ∧
      AndersonAC.AgentS6.postW q k ω i ≤ (core.card : ℝ) := by
  have hτ := q.running_ridge k ω hk
  have h0 := AndersonAC.AgentS6.leverage_nonneg
    (trialCross t (r ω) (q.state (k + 1) ω)) hτ.le i
  have hle := AndersonAC.AgentS6Row.leverage_le_card
    (trialCross t (r ω) (q.state (k + 1) ω)) (q.ridge k ω) hτ i
  rw [Fintype.card_coe] at hle
  simpa [AndersonAC.AgentS6.postW, trialWeights] using ⟨h0, hle⟩

theorem measurable_total_onRunning_pre (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) :
    Measurable (fun ω => totalWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω)) :=
  Finset.measurable_sum _ fun i _ => measurable_onRunning_pre q k i

theorem measurable_total_onRunning_post (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) :
    Measurable (fun ω => totalWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω)) :=
  Finset.measurable_sum _ fun i _ => measurable_onRunning_post q k i

theorem measurable_square_onRunning_pre (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) :
    Measurable (fun ω => squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω)) := by
  unfold squareWeight
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_onRunning_pre q k i).pow_const 2

theorem measurable_square_onRunning_post (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) :
    Measurable (fun ω => squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω)) := by
  unfold squareWeight
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_onRunning_post q k i).pow_const 2

theorem total_onRunning_pre_nonneg_bound (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) :
    0 ≤ totalWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) ∧
      totalWeight (onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) ≤ (core.card : ℝ) := by
  by_cases hk : k < q.stop ω
  · have hmem : ω ∈ (fun k => {ω | k < q.stop ω}) k := hk
    have heq : onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω =
        AndersonAC.AgentS6.preW q k ω := by simp [onRunning, hk]
    rw [heq]
    have hnn : ∀ i, 0 ≤ AndersonAC.AgentS6.preW q k ω i :=
      fun i => (leverage_mem_bounds q k ω hk i).1
    have hle : ∀ i, AndersonAC.AgentS6.preW q k ω i ≤ (core.card : ℝ) :=
      fun i => (leverage_mem_bounds q k ω hk i).2
    have hsum_nn : 0 ≤ totalWeight (AndersonAC.AgentS6.preW q k ω) :=
      Finset.sum_nonneg fun i _ => hnn i
    have htot : totalWeight (AndersonAC.AgentS6.preW q k ω) ≤ (core.card : ℝ) := by
      have hτ := q.running_ridge k ω hk
      have h := AndersonAC.AgentS6.totalWeight_leverage_le
        (trialCross t (r ω) (q.state k ω)) hτ
      rw [Fintype.card_coe] at h
      simpa [AndersonAC.AgentS6.preW, trialWeights, totalWeight] using h
    exact ⟨hsum_nn, htot⟩
  · have heq : onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω = 0 := by
      simp [onRunning, hk]
    rw [heq]
    simp [totalWeight]

theorem total_onRunning_post_nonneg_bound (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) :
    0 ≤ totalWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) ∧
      totalWeight (onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) ≤ (core.card : ℝ) := by
  by_cases hk : k < q.stop ω
  · have heq : onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω =
        AndersonAC.AgentS6.postW q k ω := by simp [onRunning, hk]
    rw [heq]
    have hnn : ∀ i, 0 ≤ AndersonAC.AgentS6.postW q k ω i :=
      fun i => (leverage_post_bounds q k ω hk i).1
    have hsum_nn : 0 ≤ totalWeight (AndersonAC.AgentS6.postW q k ω) :=
      Finset.sum_nonneg fun i _ => hnn i
    have htot : totalWeight (AndersonAC.AgentS6.postW q k ω) ≤ (core.card : ℝ) := by
      have hτ := q.running_ridge k ω hk
      have h := AndersonAC.AgentS6.totalWeight_leverage_le
        (trialCross t (r ω) (q.state (k + 1) ω)) hτ
      rw [Fintype.card_coe] at h
      simpa [AndersonAC.AgentS6.postW, trialWeights, totalWeight] using h
    exact ⟨hsum_nn, htot⟩
  · have heq : onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω = 0 := by
      simp [onRunning, hk]
    rw [heq]
    simp [totalWeight]

theorem square_onRunning_pre_bound (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) :
    0 ≤ squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) ∧
      squareWeight (onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) ≤ (core.card : ℝ) ^ 2 := by
  have htot := total_onRunning_pre_nonneg_bound q k ω
  have hmax : ∀ i, onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i ≤ (core.card : ℝ) := by
    intro i
    by_cases hk : k < q.stop ω
    · simp [onRunning, hk]
      exact (leverage_mem_bounds q k ω hk i).2
    · simp [onRunning, hk]
  have hnn : ∀ i, 0 ≤ onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i := by
    intro i
    by_cases hk : k < q.stop ω
    · simp [onRunning, hk]
      exact (leverage_mem_bounds q k ω hk i).1
    · simp [onRunning, hk]
  have hsq_nn : 0 ≤ squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) ≤ (core.card : ℝ) ^ 2 := by
    have hterm : ∀ i ∈ Finset.univ,
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) ^ 2 ≤
          (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) * (core.card : ℝ) := by
      intro i _
      have h0 := hnn i
      have h1 := hmax i
      nlinarith [sq_nonneg
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i)]
    have hsum : ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) ^ 2 ≤
        ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) * (core.card : ℝ) :=
      Finset.sum_le_sum fun i hi => hterm i hi
    have heq : (∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) * (core.card : ℝ)) =
        totalWeight (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) * (core.card : ℝ) := by
      simp [totalWeight, Finset.sum_mul]
    have hle : totalWeight (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) * (core.card : ℝ) ≤
        (core.card : ℝ) * (core.card : ℝ) := by
      have := htot.2
      have hcard : 0 ≤ (core.card : ℝ) := by positivity
      nlinarith
    unfold squareWeight
    calc ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) ^ 2
        ≤ ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω i) * (core.card : ℝ) := hsum
      _ = totalWeight (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω) * (core.card : ℝ) := heq
      _ ≤ (core.card : ℝ) * (core.card : ℝ) := hle
      _ = (core.card : ℝ) ^ 2 := by ring
  exact ⟨hsq_nn, hsq⟩

theorem square_onRunning_post_bound (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) :
    0 ≤ squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) ∧
      squareWeight (onRunning (fun k => {ω | k < q.stop ω})
        (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) ≤ (core.card : ℝ) ^ 2 := by
  have htot := total_onRunning_post_nonneg_bound q k ω
  have hmax : ∀ i, onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i ≤ (core.card : ℝ) := by
    intro i
    by_cases hk : k < q.stop ω
    · simp [onRunning, hk]
      exact (leverage_post_bounds q k ω hk i).2
    · simp [onRunning, hk]
  have hnn : ∀ i, 0 ≤ onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i := by
    intro i
    by_cases hk : k < q.stop ω
    · simp [onRunning, hk]
      exact (leverage_post_bounds q k ω hk i).1
    · simp [onRunning, hk]
  have hsq_nn : 0 ≤ squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) ≤ (core.card : ℝ) ^ 2 := by
    have hterm : ∀ i ∈ Finset.univ,
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) ^ 2 ≤
          (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) * (core.card : ℝ) := by
      intro i _
      have h0 := hnn i
      have h1 := hmax i
      nlinarith [sq_nonneg
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i)]
    have hsum2 : ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) ^ 2 ≤
        ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) * (core.card : ℝ) :=
      Finset.sum_le_sum fun i hi => hterm i hi
    have heq2 : (∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) * (core.card : ℝ)) =
        totalWeight (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) * (core.card : ℝ) := by
      simp [totalWeight, Finset.sum_mul]
    have hle2 : totalWeight (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) * (core.card : ℝ) ≤
        (core.card : ℝ) * (core.card : ℝ) := by
      have := htot.2
      have hcard : 0 ≤ (core.card : ℝ) := by positivity
      nlinarith
    unfold squareWeight
    calc ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) ^ 2
        ≤ ∑ i : Fin n, (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω i) * (core.card : ℝ) := hsum2
      _ = totalWeight (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω) * (core.card : ℝ) := heq2
      _ ≤ (core.card : ℝ) * (core.card : ℝ) := hle2
      _ = (core.card : ℝ) ^ 2 := by ring
  exact ⟨hsq_nn, hsq⟩

theorem integrable_total_onRunning_pre (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) :
    Integrable (fun ω => totalWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω)) μ :=
  Integrable.of_bound ((measurable_total_onRunning_pre q k).aestronglyMeasurable)
    (core.card : ℝ) (Filter.Eventually.of_forall fun ω => by
      have h := total_onRunning_pre_nonneg_bound q k ω
      simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)

theorem integrable_total_onRunning_post (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) :
    Integrable (fun ω => totalWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω)) μ :=
  Integrable.of_bound ((measurable_total_onRunning_post q k).aestronglyMeasurable)
    (core.card : ℝ) (Filter.Eventually.of_forall fun ω => by
      have h := total_onRunning_post_nonneg_bound q k ω
      simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)

theorem integrable_square_onRunning_pre (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) :
    Integrable (fun ω => squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω)) μ :=
  Integrable.of_bound ((measurable_square_onRunning_pre q k).aestronglyMeasurable)
    ((core.card : ℝ) ^ 2) (Filter.Eventually.of_forall fun ω => by
      have h := square_onRunning_pre_bound q k ω
      simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)

theorem integrable_square_onRunning_post (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) :
    Integrable (fun ω => squareWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.postW q k ω) k ω)) μ :=
  Integrable.of_bound ((measurable_square_onRunning_post q k).aestronglyMeasurable)
    ((core.card : ℝ) ^ 2) (Filter.Eventually.of_forall fun ω => by
      have h := square_onRunning_post_bound q k ω
      simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)

section Bridge

theorem damped_eq {A : Type*} [Fintype A] [DecidableEq A] (M : Matrix A A ℝ) (t : ℝ)
    (r : A → ℂ) : dampedMatrix M t r = AndersonAC.L64.damped M t r := rfl

theorem scat_eq {A : Type*} [Fintype A] [DecidableEq A] (t : ℝ) (r : A → ℂ)
    (g : Matrix A A ℂ) :
    scattering t r g = AndersonAC.L64.scat t (AndersonAC.L64.pim r) g := rfl

theorem heatCoeff_eq {A : Type*} [Fintype A] [DecidableEq A] (M : Matrix A A ℝ) (t : ℝ)
    (r : A → ℂ) (x : A) (ξ : ℝ) :
    heatCoefficient t (r x) ((AndersonAC.L64.damped M t r)⁻¹ x x) ξ =
      AndersonAC.L64.heatCoeff M t r x ξ := rfl

theorem leverage_zero_row {R B : Type*} [Fintype R] [DecidableEq R] [Fintype B]
    [DecidableEq B] (C : Matrix R B ℂ) (τ : ℝ) (i : R) (h0 : ∀ b, C i b = 0) :
    leverage C τ i = 0 := by
  simp only [leverage, ridgeProjection, Matrix.mul_apply, h0, zero_mul,
    Finset.sum_const_zero, Complex.zero_re]

theorem ridgeLev_zero_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℂ) (B R : Finset ι) (τ : ℝ) (i : ι)
    (h0 : ∀ b : {x // x ∈ B}, S i b = 0) :
    AndersonAC.L64.ridgeLev S B R τ i = 0 := by
  have hcr : AndersonAC.L64.crossRow S B i = 0 := by
    funext b
    simpa [AndersonAC.L64.crossRow] using h0 b
  simp only [AndersonAC.L64.ridgeLev, hcr, star_zero, zero_dotProduct,
    Complex.zero_re]

/-- Core as a finset of the active subtype. -/
def actCore (s : TrialState core) : Finset {i // i ∈ s.active} :=
  Finset.univ.filter (fun i => i.val ∈ core)

theorem mem_actCore_iff {s : TrialState core} {i : {i // i ∈ s.active}} :
    i ∈ actCore s ↔ i.val ∈ core := by
  simp only [actCore, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Reindexing between core and core-in-active. -/
def coreActEquiv (s : TrialState core) : {b // b ∈ core} ≃ {i // i ∈ actCore s} where
  toFun b := ⟨⟨b.val, s.core_active b.property⟩, mem_actCore_iff.mpr b.property⟩
  invFun u := ⟨u.val.val, mem_actCore_iff.mp u.property⟩
  left_inv b := by ext; rfl
  right_inv u := by ext; rfl

theorem actCore_card (s : TrialState core) : (actCore s).card = core.card := by
  have h := Fintype.card_congr (coreActEquiv s)
  rw [Fintype.card_coe, Fintype.card_coe] at h
  omega

end Bridge

/-- Pre inverse is the damped inverse. -/
theorem preInverse_eq (s : TrialState core) (rr : Fin n → ℂ) :
    trialInverse t rr s =
      (AndersonAC.L64.damped s.M t (fun i : {i // i ∈ s.active} => rr i))⁻¹ := by
  unfold trialInverse activeInverse
  rw [damped_eq]

/-- L64 cross row equals the trial cross row (reindexed). -/
theorem preCross_eq (s : TrialState core) (rr : Fin n → ℂ)
    (i : {i // i ∈ s.active}) (hi : (i.val ∉ core))
    (b : {u // u ∈ actCore s}) :
    AndersonAC.L64.crossRow
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
        (trialInverse t rr s)) (actCore s) i b =
      trialCross t rr s i.val ((coreActEquiv s).symm b) := by
  unfold AndersonAC.L64.crossRow trialCross
  rw [dif_pos i.property, if_neg hi, scat_eq]
  rfl

/-- Rows that can carry weight before the heat. -/
def F_pre (s : TrialState core) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∈ s.active ∧ i ∉ core)

theorem F_pre_mem_iff {s : TrialState core} {i : Fin n} :
    i ∈ F_pre s ↔ i ∈ s.active ∧ i ∉ core := by
  simp only [F_pre, Finset.mem_filter, Finset.mem_univ, true_and]

theorem trialW_zero_pre (s : TrialState core) (rr : Fin n → ℂ) (τ : ℝ) (i : Fin n)
    (hi : i ∉ F_pre s) : trialWeights t rr s τ i = 0 := by
  apply leverage_zero_row
  intro b
  rw [F_pre_mem_iff] at hi
  push_neg at hi
  by_cases ha : i ∈ s.active
  · have hc : i ∈ core := hi ha
    simp [trialCross, dif_pos ha, if_pos hc]
  · simp [trialCross, dif_neg ha]

/-- Trial cross rows vanish outside active-minus-core. -/
theorem trialCross_row_zero (s : TrialState core) (rr : Fin n → ℂ) (i : Fin n)
    (hi : ¬(i ∈ s.active ∧ i ∉ core)) (b : {b // b ∈ core}) :
    trialCross t rr s i b = 0 := by
  by_cases ha : i ∈ s.active
  · have hc : i ∈ core := by
      by_contra hc
      exact hi ⟨ha, hc⟩
    simp [trialCross, dif_pos ha, if_pos hc]
  · simp [trialCross, dif_neg ha]

/-- L64 cross row as a reindexed trial row (function form). -/
theorem preCross_fun_eq (s : TrialState core) (rr : Fin n → ℂ)
    (i : {i // i ∈ s.active}) (hi : i ∈ (actCore s)ᶜ) :
    AndersonAC.L64.crossRow
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
        (trialInverse t rr s)) (actCore s) i =
      (trialCross t rr s i.val) ∘ ⇑(coreActEquiv s).symm := by
  funext b
  have hc : (i.val ∉ core) :=
    fun h => (Finset.mem_compl.mp hi) (mem_actCore_iff.mpr h)
  exact preCross_eq s rr i hc b

/-- L64 gram equals the reindexed S6 gram. -/
theorem preGram_eq (s : TrialState core) (rr : Fin n → ℂ) :
    AndersonAC.L64.gram
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
        (trialInverse t rr s)) (actCore s) (actCore s)ᶜ =
      ((AndersonAC.S6.gram (trialCross t rr s)).submatrix
        ⇑(coreActEquiv s).symm ⇑(coreActEquiv s).symm) := by
  ext b1 b2
  simp only [AndersonAC.L64.gram, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.submatrix_apply, AndersonAC.S6.gram, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  have himg : F_pre s = (actCore s)ᶜ.image Subtype.val := by
    ext i
    simp only [F_pre_mem_iff, Finset.mem_image, Finset.mem_compl]
    constructor
    · rintro ⟨ha, hc⟩
      exact ⟨⟨i, ha⟩, by simpa [mem_actCore_iff] using hc, rfl⟩
    · rintro ⟨i', hi', rfl⟩
      exact ⟨i'.property, fun hc => hi' (mem_actCore_iff.mpr hc)⟩
  have hRHS : (∑ i : Fin n, star (trialCross t rr s i ((coreActEquiv s).symm b1)) *
      trialCross t rr s i ((coreActEquiv s).symm b2))
      = ∑ i ∈ F_pre s, star (trialCross t rr s i ((coreActEquiv s).symm b1)) *
        trialCross t rr s i ((coreActEquiv s).symm b2) :=
    (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      have hz1 : trialCross t rr s i ((coreActEquiv s).symm b1) = 0 :=
        trialCross_row_zero s rr i (by simpa [F_pre_mem_iff] using hi) _
      simp [hz1])).symm
  rw [hRHS, himg, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i' hi'
  have hc : (i'.val ∉ core) :=
    fun h => (Finset.mem_compl.mp hi') (mem_actCore_iff.mpr h)
  rw [preCross_eq s rr i' hc b1, preCross_eq s rr i' hc b2]

theorem F_pre_image (s : TrialState core) :
    F_pre s = (actCore s)ᶜ.image Subtype.val := by
  ext i
  simp only [F_pre_mem_iff, Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro ⟨ha, hc⟩
    exact ⟨⟨i, ha⟩, by simpa [mem_actCore_iff] using hc, rfl⟩
  · rintro ⟨i', hi', rfl⟩
    exact ⟨i'.property, fun hc => hi' (mem_actCore_iff.mpr hc)⟩

/-- Pre cross matrix with Bset columns. -/
def preCrossB (t : ℝ) (s : TrialState core) (rr : Fin n → ℂ) : Matrix (Fin n) {u // u ∈ actCore s} ℂ :=
  (trialCross t rr s).submatrix id ⇑(coreActEquiv s).symm

theorem crossEqB (s : TrialState core) (rr : Fin n → ℂ)
    (i : {i // i ∈ s.active}) (hi : i ∈ (actCore s)ᶜ) :
    AndersonAC.L64.crossRow
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
        (trialInverse t rr s)) (actCore s) i =
      preCrossB t s rr i.val := by
  funext b
  have hc : (i.val ∉ core) :=
    fun h => (Finset.mem_compl.mp hi) (mem_actCore_iff.mpr h)
  have h1 : AndersonAC.L64.crossRow
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
        (trialInverse t rr s)) (actCore s) i b =
      trialCross t rr s i.val ((coreActEquiv s).symm b) :=
    preCross_eq s rr i hc b
  simp only [preCrossB, Matrix.submatrix_apply, id_eq] at *
  exact h1

theorem gramEqB (s : TrialState core) (rr : Fin n → ℂ) :
    AndersonAC.L64.gram
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
        (trialInverse t rr s)) (actCore s) (actCore s)ᶜ =
      AndersonAC.S6.gram (preCrossB t s rr) := by
  ext b1 b2
  simp only [AndersonAC.L64.gram, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, AndersonAC.S6.gram, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  have hRHS : (∑ i : Fin n, star (preCrossB t s rr i b1) * preCrossB t s rr i b2)
      = ∑ i ∈ F_pre s, star (preCrossB t s rr i b1) * preCrossB t s rr i b2 :=
    (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      have hz1 : preCrossB t s rr i b1 = 0 := by
        simp only [preCrossB, Matrix.submatrix_apply, id_eq]
        exact trialCross_row_zero s rr i (by simpa [F_pre_mem_iff] using hi) _
      simp [hz1])).symm
  rw [hRHS, F_pre_image s, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i' hi'
  have hc : (i'.val ∉ core) :=
    fun h => (Finset.mem_compl.mp hi') (mem_actCore_iff.mpr h)
  have hfun : AndersonAC.L64.crossRow (AndersonAC.L64.scat t
      (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
      (trialInverse t rr s)) (actCore s) i'
      = preCrossB t s rr i'.val := crossEqB s rr i' hi'
  simp only [hfun]

/-- L64 pre leverage equals the trial weight. -/
theorem preLev_eq (s : TrialState core) (rr : Fin n → ℂ) (τ : ℝ)
    (i : {i // i ∈ s.active}) (hi : (i.val ∉ core)) :
    AndersonAC.L64.ridgeLev
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
        (trialInverse t rr s)) (actCore s) (actCore s)ᶜ τ i =
      trialWeights t rr s τ i.val := by
  have hi' : i ∈ (actCore s)ᶜ :=
    Finset.mem_compl.mpr (fun h => hi (mem_actCore_iff.mp h))
  have hcross : AndersonAC.L64.crossRow _ (actCore s) i = preCrossB t s rr i.val :=
    crossEqB s rr i hi'
  have hGinv : (AndersonAC.L64.gram (AndersonAC.L64.scat t
      (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr i))
      (trialInverse t rr s)) (actCore s) (actCore s)ᶜ + (τ : ℂ) • 1)⁻¹
      = (AndersonAC.S6.gram (preCrossB t s rr) + (τ : ℂ) • 1)⁻¹ := by
    rw [gramEqB s rr]
  have hTrial : trialWeights t rr s τ i.val = leverage (preCrossB t s rr) τ i.val := by
    unfold preCrossB trialWeights
    exact (AndersonAC.AgentS6.leverage_reindex _ _ _ _).symm
  rw [hTrial]
  unfold AndersonAC.L64.ridgeLev AndersonAC.S6.leverage
    AndersonAC.S6.ridgeProjection
  rw [hcross, hGinv]
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine congrArg Complex.re ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  have hR : AndersonAC.S6.ridgeGram (preCrossB t s rr) τ
      = AndersonAC.S6.gram (preCrossB t s rr) + (τ : ℂ) • 1 := rfl
  rw [hR]
  ring

theorem preA_eq_sum (s : TrialState core) (rr : Fin n → ℂ) (τ : ℝ) :
    AndersonAC.L64.preA s.M t (fun i : {i // i ∈ s.active} => rr i)
      (actCore s) τ =
      totalWeight (trialWeights t rr s τ) := by
  unfold AndersonAC.L64.preA totalWeight
  have hRHS : (∑ i : Fin n, trialWeights t rr s τ i)
      = ∑ i ∈ F_pre s, trialWeights t rr s τ i :=
    (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi =>
      trialW_zero_pre s rr τ i hi)).symm
  rw [hRHS, F_pre_image s, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i' hi'
  have hc : (i'.val ∉ core) :=
    fun h => (Finset.mem_compl.mp hi') (mem_actCore_iff.mpr h)
  unfold AndersonAC.L64.preLev
  rw [← preInverse_eq s rr]
  exact preLev_eq s rr τ i' hc

theorem preP_eq_sum (s : TrialState core) (rr : Fin n → ℂ) (τ : ℝ) :
    AndersonAC.L64.preP s.M t (fun i : {i // i ∈ s.active} => rr i)
      (actCore s) τ =
      squareWeight (trialWeights t rr s τ) := by
  unfold AndersonAC.L64.preP squareWeight
  have hRHS : (∑ i : Fin n, trialWeights t rr s τ i ^ 2)
      = ∑ i ∈ F_pre s, trialWeights t rr s τ i ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      rw [trialW_zero_pre s rr τ i hi]; simp)).symm
  rw [hRHS, F_pre_image s, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i' hi'
  have hc : (i'.val ∉ core) :=
    fun h => (Finset.mem_compl.mp hi') (mem_actCore_iff.mpr h)
  have hterm : AndersonAC.L64.preLev s.M t
      (fun i : {i // i ∈ s.active} => rr i) (actCore s) τ i' =
      trialWeights t rr s τ i'.val := by
    unfold AndersonAC.L64.preLev
    rw [← preInverse_eq s rr]
    exact preLev_eq s rr τ i' hc
  rw [hterm]

/-- Rows that can carry weight after the heat. -/
def F_post (s' : TrialState core) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∈ s'.active ∧ i ∉ core)

theorem F_post_mem_iff {s' : TrialState core} {i : Fin n} :
    i ∈ F_post s' ↔ i ∈ s'.active ∧ i ∉ core := by
  simp only [F_post, Finset.mem_filter, Finset.mem_univ, true_and]

theorem trialW_zero_post (s' : TrialState core) (rr : Fin n → ℂ) (τ : ℝ) (i : Fin n)
    (hi : i ∉ F_post s') : trialWeights t rr s' τ i = 0 := by
  apply leverage_zero_row
  intro b
  rw [F_post_mem_iff] at hi
  push_neg at hi
  by_cases ha : i ∈ s'.active
  · have hc : i ∈ core := hi ha
    simp [trialCross, dif_pos ha, if_pos hc]
  · simp [trialCross, dif_neg ha]

/-- Trial cross rows vanish outside post-heat active-minus-core. -/
theorem trialCross_row_zero_post (s' : TrialState core) (rr : Fin n → ℂ) (i : Fin n)
    (hi : ¬(i ∈ s'.active ∧ i ∉ core)) (b : {b // b ∈ core}) :
    trialCross t rr s' i b = 0 := by
  by_cases ha : i ∈ s'.active
  · have hc : i ∈ core := by
      by_contra hc
      exact hi ⟨ha, hc⟩
    simp [trialCross, dif_pos ha, if_pos hc]
  · simp [trialCross, dif_neg ha]

theorem F_post_image (s s' : TrialState core) (x : Fin n) (hx : x ∈ s.active)
    (hxcore : x ∉ core) (hact : s'.active = s.active.erase x) :
    F_post s' = ((actCore s)ᶜ.erase ⟨x, hx⟩).image Subtype.val := by
  ext i
  simp only [F_post_mem_iff, Finset.mem_image, Finset.mem_erase, Finset.mem_compl]
  constructor
  · rintro ⟨ha, hc⟩
    rw [hact] at ha
    rw [Finset.mem_erase] at ha
    exact ⟨⟨i, ha.2⟩,
      ⟨fun he => ha.1 (congrArg Subtype.val he),
        by simpa [mem_actCore_iff] using hc⟩, rfl⟩
  · rintro ⟨i', hi', rfl⟩
    have h1 : i'.val ∈ s'.active := by
      rw [hact, Finset.mem_erase]
      exact ⟨fun he => hi'.1 (Subtype.ext he), i'.property⟩
    have h2 : i'.val ∉ core := fun h => hi'.2 (mem_actCore_iff.mpr h)
    exact ⟨h1, h2⟩

/-- Post inverse entries on kept pairs equal the trial inverse after the heat. -/
theorem postInverse_eq (s s' : TrialState core) (rr : Fin n → ℂ) (x : Fin n) (ξ : ℝ)
    (hr : ∀ i, 0 < (rr i).im) (ht : 0 < t)
    (h : HeatTransition t rr s s' x ξ) (hx : x ∈ s.active)
    (i j : {i // i ∈ s'.active}) (hi : (i.val ∈ s.active)) (hj : (j.val ∈ s.active)) :
    (AndersonAC.L64.dampedPost s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
      ⟨x, hx⟩ ξ)⁻¹ ⟨i.val, hi⟩ ⟨j.val, hj⟩
      = trialInverse t rr s' i j := by
  classical
  set r' : {i // i ∈ s.active} → ℂ := fun i => rr (i : Fin n) with hr'def
  set xA : {i // i ∈ s.active} := ⟨x, hx⟩ with xAdef
  obtain ⟨hx', hq, hSM⟩ := AndersonAC.AgentS6.trial_heat_step ht rr hr h
  have hD : IsUnit (AndersonAC.L64.damped s.M t r').det :=
    AndersonAC.AgentS6.damped_isUnit s.M s.symmetric ht _ (fun i => hr ↑i)
  have hq' : 1 + (((ξ : ℂ) + (t : ℂ) * r' xA) *
      (AndersonAC.L64.damped s.M t r')⁻¹ xA xA) ≠ 0 := by
    have h1 := hq
    rw [preInverse_eq s rr] at h1
    exact h1
  have hSMmat := AndersonAC.L64.sherman_morrison (AndersonAC.L64.damped s.M t r') hD xA _ hq'
  rw [hSM i j hi hj, preInverse_eq s rr]
  unfold AndersonAC.L64.dampedPost
  rw [hSMmat]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- Post cross matrix with pre-heat Bset columns. -/
def postCrossB (t : ℝ) (s s' : TrialState core) (rr : Fin n → ℂ) :
    Matrix (Fin n) {u // u ∈ actCore s} ℂ :=
  (trialCross t rr s').submatrix id ⇑(coreActEquiv s).symm

/-- L64 post cross entry equals the post-heat trial cross entry. -/
theorem postCross_entry (s s' : TrialState core) (rr : Fin n → ℂ) (x : Fin n) (ξ : ℝ)
    (hr : ∀ i, 0 < (rr i).im) (ht : 0 < t)
    (h : HeatTransition t rr s s' x ξ) (hx : x ∈ s.active) (hxcore : x ∉ core)
    (i : {i // i ∈ s.active}) (hne : i ≠ ⟨x, hx⟩) (hnc : (i.val ∉ core))
    (b : {u // u ∈ actCore s}) :
    AndersonAC.L64.crossRow
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr (i : Fin n)))
        (AndersonAC.L64.dampedPost s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
          ⟨x, hx⟩ ξ)⁻¹) (actCore s) i b =
      trialCross t rr s' i.val ((coreActEquiv s).symm b) := by
  classical
  have hheat := h
  obtain ⟨hx', hxcore', hact, hP, hM', hhat⟩ := h
  have hival : i.val ∈ s'.active := by
    rw [hact, Finset.mem_erase]
    exact ⟨fun he => hne (Subtype.ext he), i.property⟩
  have hne_b : i.val ≠ ((coreActEquiv s).symm b).val :=
    fun he => hnc (he ▸ ((coreActEquiv s).symm b).property)
  have hbi : i ≠ b.val :=
    fun he => hnc (congrArg Subtype.val he ▸ mem_actCore_iff.mp b.property)
  have hbi' : (⟨i.val, hival⟩ : {i // i ∈ s'.active}) ≠
      ⟨((coreActEquiv s).symm b).val, s'.core_active ((coreActEquiv s).symm b).property⟩ := by
    intro he
    apply hne_b
    simpa using congrArg Subtype.val he
  have hiB : (i.val ∈ s.active) := i.property
  have hjB : ((((coreActEquiv s).symm b).val : Fin n) ∈ s.active) :=
    s.core_active ((coreActEquiv s).symm b).property
  simp only [AndersonAC.L64.crossRow]
  rw [AndersonAC.L64.scat_apply_ne _ _ _ hbi]
  unfold trialCross
  rw [dif_pos hival, if_neg hnc, scat_eq,
    AndersonAC.L64.scat_apply_ne _ _ _ hbi',
    ← postInverse_eq s s' rr x ξ hr ht hheat hx _ _ hiB hjB]
  rfl

/-- L64 post cross row equals the post-heat trial row (function form). -/
theorem postCrossRow_eq (s s' : TrialState core) (rr : Fin n → ℂ) (x : Fin n) (ξ : ℝ)
    (hr : ∀ i, 0 < (rr i).im) (ht : 0 < t)
    (h : HeatTransition t rr s s' x ξ) (hx : x ∈ s.active) (hxcore : x ∉ core)
    (i : {i // i ∈ s.active}) (hne : i ≠ ⟨x, hx⟩) (hnc : (i.val ∉ core)) :
    AndersonAC.L64.crossRow
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr (i : Fin n)))
        (AndersonAC.L64.dampedPost s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
          ⟨x, hx⟩ ξ)⁻¹) (actCore s) i =
      postCrossB t s s' rr i.val := by
  funext b
  have hentry := postCross_entry s s' rr x ξ hr ht h hx hxcore i hne hnc b
  have hsub : postCrossB t s s' rr i.val b
      = trialCross t rr s' i.val ((coreActEquiv s).symm b) := by
    simp only [postCrossB, Matrix.submatrix_apply, id_eq]
  rw [hsub]
  exact hentry

/-- L64 post gram equals the S6 gram of the post-heat trial cross. -/
theorem postGramEqB (s s' : TrialState core) (rr : Fin n → ℂ) (x : Fin n) (ξ : ℝ)
    (hr : ∀ i, 0 < (rr i).im) (ht : 0 < t)
    (h : HeatTransition t rr s s' x ξ) (hx : x ∈ s.active) (hxcore : x ∉ core) :
    AndersonAC.L64.gram
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr (i : Fin n)))
        (AndersonAC.L64.dampedPost s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
          ⟨x, hx⟩ ξ)⁻¹) (actCore s) ((actCore s)ᶜ.erase ⟨x, hx⟩) =
      AndersonAC.S6.gram (postCrossB t s s' rr) := by
  classical
  have hheat := h
  obtain ⟨hx', hxcore', hact, hP, hM', hhat⟩ := h
  ext b1 b2
  simp only [AndersonAC.L64.gram, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, AndersonAC.S6.gram, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  have hRHS : (∑ i : Fin n, star (postCrossB t s s' rr i b1) * postCrossB t s s' rr i b2)
      = ∑ i ∈ F_post s', star (postCrossB t s s' rr i b1) * postCrossB t s s' rr i b2 :=
    (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      have hz1 : postCrossB t s s' rr i b1 = 0 := by
        simp only [postCrossB, Matrix.submatrix_apply, id_eq]
        exact trialCross_row_zero_post s' rr i (by simpa [F_post_mem_iff] using hi) _
      simp [hz1])).symm
  rw [hRHS, F_post_image s s' x hx hxcore hact,
    Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i' hi'
  have hne : i' ≠ ⟨x, hx⟩ := (Finset.mem_erase.mp hi').1
  have hnc : (i'.val ∉ core) :=
    fun h => (Finset.mem_compl.mp (Finset.mem_erase.mp hi').2) (mem_actCore_iff.mpr h)
  have e1 := postCross_entry s s' rr x ξ hr ht hheat hx hxcore i' hne hnc b1
  have e2 := postCross_entry s s' rr x ξ hr ht hheat hx hxcore i' hne hnc b2
  have hfun := postCrossRow_eq s s' rr x ξ hr ht hheat hx hxcore i' hne hnc
  have c1 : AndersonAC.L64.crossRow _ (actCore s) i' b1 =
      postCrossB t s s' rr i'.val b1 := congrFun hfun b1
  have c2 : AndersonAC.L64.crossRow _ (actCore s) i' b2 =
      postCrossB t s s' rr i'.val b2 := congrFun hfun b2
  rw [c1, c2]

/-- Dot-product ridge form equals the matrix leverage form. -/
theorem ridgeLev_eq_leverage {B : Type*} [Fintype B] [DecidableEq B]
    (C : Matrix (Fin n) B ℂ) (τ : ℝ) (j : Fin n)
    (u : B → ℂ) (H : Matrix B B ℂ)
    (hu : u = fun b => C j b) (hH : H = (AndersonAC.S6.gram C + (τ : ℂ) • 1)⁻¹) :
    (dotProduct u (Matrix.mulVec H (star u))).re
      = AndersonAC.S6.leverage C τ j := by
  rw [hu, hH]
  unfold AndersonAC.S6.leverage AndersonAC.S6.ridgeProjection
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine congrArg Complex.re ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  have hR : AndersonAC.S6.ridgeGram C τ
      = AndersonAC.S6.gram C + (τ : ℂ) • 1 := rfl
  rw [hR]
  ring

/-- L64 post leverage equals the post-heat trial weight. -/
theorem postLev_eq (s s' : TrialState core) (rr : Fin n → ℂ) (x : Fin n) (ξ : ℝ)
    (hr : ∀ i, 0 < (rr i).im) (ht : 0 < t)
    (h : HeatTransition t rr s s' x ξ) (hx : x ∈ s.active) (hxcore : x ∉ core)
    (τ : ℝ) (i : {i // i ∈ s.active}) (hne : i ≠ ⟨x, hx⟩) (hnc : (i.val ∉ core)) :
    AndersonAC.L64.postLev s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
      (actCore s) ⟨x, hx⟩ τ ξ i =
      trialWeights t rr s' τ i.val := by
  have hrow := postCrossRow_eq s s' rr x ξ hr ht h hx hxcore i hne hnc
  have hgram : (AndersonAC.L64.gram
      (AndersonAC.L64.scat t
        (AndersonAC.L64.pim (fun i : {i // i ∈ s.active} => rr (i : Fin n)))
        (AndersonAC.L64.dampedPost s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
          ⟨x, hx⟩ ξ)⁻¹) (actCore s) ((actCore s)ᶜ.erase ⟨x, hx⟩) + (τ : ℂ) • 1)⁻¹
      = (AndersonAC.S6.gram (postCrossB t s s' rr) + (τ : ℂ) • 1)⁻¹ := by
    rw [postGramEqB s s' rr x ξ hr ht h hx hxcore]
  have hTrial : trialWeights t rr s' τ i.val
      = leverage (postCrossB t s s' rr) τ i.val := by
    unfold postCrossB trialWeights
    exact (AndersonAC.AgentS6.leverage_reindex _ _ _ _).symm
  have hcalc := ridgeLev_eq_leverage (postCrossB t s s' rr) τ i.val _ _ hrow hgram
  unfold AndersonAC.L64.postLev AndersonAC.L64.ridgeLev
  rw [hTrial]
  exact hcalc

theorem postA_eq_sum (s s' : TrialState core) (rr : Fin n → ℂ) (x : Fin n) (ξ : ℝ)
    (hr : ∀ i, 0 < (rr i).im) (ht : 0 < t)
    (h : HeatTransition t rr s s' x ξ) (hx : x ∈ s.active) (hxcore : x ∉ core)
    (τ : ℝ) :
    AndersonAC.L64.postA s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
      (actCore s) ⟨x, hx⟩ τ ξ =
      totalWeight (trialWeights t rr s' τ) := by
  classical
  have hheat := h
  obtain ⟨hx', hxcore', hact, hP, hM', hhat⟩ := h
  unfold AndersonAC.L64.postA totalWeight
  have hRHS : (∑ i : Fin n, trialWeights t rr s' τ i)
      = ∑ i ∈ F_post s', trialWeights t rr s' τ i :=
    (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi =>
      trialW_zero_post s' rr τ i hi)).symm
  rw [hRHS, F_post_image s s' x hx hxcore hact,
    Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i' hi'
  have hne : i' ≠ ⟨x, hx⟩ := (Finset.mem_erase.mp hi').1
  have hnc : (i'.val ∉ core) :=
    fun h => (Finset.mem_compl.mp (Finset.mem_erase.mp hi').2) (mem_actCore_iff.mpr h)
  exact postLev_eq s s' rr x ξ hr ht hheat hx hxcore τ i' hne hnc

theorem postP_eq_sum (s s' : TrialState core) (rr : Fin n → ℂ) (x : Fin n) (ξ : ℝ)
    (hr : ∀ i, 0 < (rr i).im) (ht : 0 < t)
    (h : HeatTransition t rr s s' x ξ) (hx : x ∈ s.active) (hxcore : x ∉ core)
    (τ : ℝ) :
    AndersonAC.L64.postP s.M t (fun i : {i // i ∈ s.active} => rr (i : Fin n))
      (actCore s) ⟨x, hx⟩ τ ξ =
      squareWeight (trialWeights t rr s' τ) := by
  classical
  have hheat := h
  obtain ⟨hx', hxcore', hact, hP, hM', hhat⟩ := h
  unfold AndersonAC.L64.postP squareWeight
  have hRHS : (∑ i : Fin n, trialWeights t rr s' τ i ^ 2)
      = ∑ i ∈ F_post s', trialWeights t rr s' τ i ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      rw [trialW_zero_post s' rr τ i hi]; simp)).symm
  rw [hRHS, F_post_image s s' x hx hxcore hact,
    Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i' hi'
  have hne : i' ≠ ⟨x, hx⟩ := (Finset.mem_erase.mp hi').1
  have hnc : (i'.val ∉ core) :=
    fun h => (Finset.mem_compl.mp (Finset.mem_erase.mp hi').2) (mem_actCore_iff.mpr h)
  have hterm := postLev_eq s s' rr x ξ hr ht hheat hx hxcore τ i' hne hnc
  rw [hterm]

/-- Pre-heat total weight is history-measurable (for the condExp pull-out). -/
theorem measurable_history_total_pre (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) :
    Measurable[(q.history k)] (fun ω => totalWeight (AndersonAC.AgentS6.preW q k ω)) :=
  Finset.measurable_sum _ fun i _ =>
    AndersonAC.AgentS6.measurable_weights q (k := k) (j := k) le_rfl i

/-- On the running event, the max onRunning pre weight is the pivot pre leverage. -/
theorem maxWeight_onRunning_pre_eq (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (hk : k < q.stop ω) (hx : q.pivot k ω ∈ (q.state k ω).active)
    (hxcore : q.pivot k ω ∉ core) :
    maxWeight (onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω)
      = AndersonAC.L64.preLev ((q.state k ω).M) t
        (fun i : {i // i ∈ (q.state k ω).active} => r ω (i : Fin n))
        (actCore (q.state k ω)) (q.ridge k ω) ⟨q.pivot k ω, hx⟩ := by
  have hrun : onRunning (fun k => {ω | k < q.stop ω})
      (fun k ω => AndersonAC.AgentS6.preW q k ω) k ω =
      AndersonAC.AgentS6.preW q k ω := by simp [onRunning, hk]
  rw [hrun]
  have hpiv := q.pivot_max k ω hk
  have hlev : AndersonAC.L64.preLev ((q.state k ω).M) t
      (fun i : {i // i ∈ (q.state k ω).active} => r ω (i : Fin n))
      (actCore (q.state k ω)) (q.ridge k ω) ⟨q.pivot k ω, hx⟩ =
      trialWeights t (r ω) (q.state k ω) (q.ridge k ω) (q.pivot k ω) :=
    preLev_eq _ _ _ _ hxcore
  show maxWeight (trialWeights t (r ω) (q.state k ω) (q.ridge k ω)) = _
  rw [← hpiv, ← hlev]

end AndersonAC.AgentS6Lev2
