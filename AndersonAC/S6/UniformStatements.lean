import AndersonAC.S6.Preparation

/-! Explicit fixed-threshold forms used to move the Proposition 6.6 scale below the
sample-space and probability-measure binders. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace AndersonAC.S6

universe u

/-- A failure-mode tail with a specified threshold, for one probability space. -/
def ModeTailBelow {Ω : Type u} [MeasurableSpace Ω]
    (d : ℕ) (c K Cloc cConc : ℝ) (μ : Measure Ω) (qlag ε : ℝ → ℝ)
    (mode : AndersonAC.AgentS6.TrialMode Ω) (t0 : ℝ) : Prop :=
  ∀ (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
    (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
    (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
    t < t0 →
    AndersonAC.AgentS6.PrepHyp d c K Cloc cConc μ qlag ε core t r g0 order q dist collapsed ell →
    ∃ G : Set Ω, MeasurableSet G ∧
      (∀ ω, mode n core t r g0 order q ω → ω ∈ G) ∧
      ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) G ω ≤
        (1 / 3) * Real.exp (-t ^ (-clearingExponent d))

/-- A failure-mode tail whose threshold is shared by all probability spaces. -/
def UniformModeTailStatement (d : ℕ) (c K Cloc cConc : ℝ) (qlag ε : ℝ → ℝ)
    (mode : ∀ {Ω : Type} [MeasurableSpace Ω], AndersonAC.AgentS6.TrialMode Ω) : Prop :=
  AndersonAC.Blueprint.WardInput →
    ∃ t0 : ℝ, 0 < t0 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ModeTailBelow d c K Cloc cConc μ qlag ε (mode (Ω := Ω)) t0

/-- Single-row leverage estimates with one pair of constants valid for every probability space. -/
def UniformLeverageOneRowStatement (d : ℕ) (c K Cloc : ℝ) : Prop :=
  ∃ L t0 : ℝ, 0 < L ∧ 0 < t0 ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → (core.card : ℝ) ≤ coreCap d t →
      (∀ ω, BroadBounds c K (r ω)) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      (∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2) →
      (∀ k ω, k < q.stop ω → HeatPrestate t K
        (fun i : {i // i ∈ (q.state k ω).active} => r ω i)
        (trialInverse t (r ω) (q.state k ω))) →
      ∀ k i, (∀ᵐ ω ∂μ, k < q.stop ω →
        |μ[(fun ω => recordedLeverageIncrement q k ω i) | q.history k] ω| ≤
          oneRowBias d t L ‖heatV q k ω i‖) ∧
        (∀ ω, k < q.stop ω →
          |recordedLeverageIncrement q k ω i| ≤ oneRowJump t L ‖heatV q k ω i‖)

/-- Proposition 6.6 with its scale threshold chosen before the probability space and measure,
with both conclusions of `Planned.preparation_of_small_component`. -/
def PreparationUniformFullStatement : Prop :=
  ∀ (d : ℕ) (_hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc) (_hConc : 0 < cConc)
    (qlag ε : ℝ → ℝ)
    (_hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (_hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (_hεpos : ∀ t, 0 ≤ ε t),
    0 < clearingExponent d ∧ ∃ t0 : ℝ, 0 < t0 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
        (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
        (q : StoppedTrial (Ω := Ω) core t r g0 order)
        (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
        0 < t → t < t0 → 1 ≤ core.card → (core.card : ℝ) ≤ coreCap d t →
        (∀ ω, BroadBounds c K (r ω)) →
        (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
        (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
        TrialLocalInput q μ d c K Cloc dist collapsed ell →
        VectorConcentrationInput μ q.history cConc →
        LeverageDriftInput μ q.history (ε t) (fun k => {ω | k < q.stop ω})
          (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω)))
          (onRunning (fun k => {ω | k < q.stop ω})
            (fun k ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω))) →
        (∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) {ω | q.outcome ω = .fail} ω ≤
          Real.exp (-t ^ (-clearingExponent d))) ∧
        (∀ ω, q.outcome ω = .done →
          q.stop ω < heatLimit t ∧ BudgetsHold t (g0 ω) (q.state (q.stop ω) ω).hatG ∧
          projectionReady t (r ω) (q.state (q.stop ω) ω) ∧
          ((q.state 0 ω).active \ (q.state (q.stop ω) ω).active).card = q.stop ω)

/-- Proposition 6.6 (06-clearing.tex:826–850) with `t0` chosen before the probability space:
"the constants are independent of the torus volume and of the component".
This is verbatim the consumer's `AndersonAC.AgentS78.PreparationUniformStatement`
(lane/agent-s78clrtrial 0cfb85f, AgentS78/Construction/ClearingTrialH.lean:339). -/
def PreparationUniformStatement : Prop :=
  ∀ (d : ℕ) (_hd : 3 ≤ d) (c K Cloc cConc : ℝ) (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc)
    (_hConc : 0 < cConc) (qlag ε : ℝ → ℝ) (_hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (_hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) (_hεpos : ∀ t, 0 ≤ ε t),
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → 1 ≤ core.card → (core.card : ℝ) ≤ coreCap d t →
      (∀ ω, BroadBounds c K (r ω)) →
      (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
      (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      VectorConcentrationInput μ q.history cConc →
      LeverageDriftInput μ q.history (ε t) (fun k => {ω | k < q.stop ω})
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω)))
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω))) →
      ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) {ω | q.outcome ω = .fail} ω ≤
        Real.exp (-t ^ (-clearingExponent d))

end AndersonAC.S6
