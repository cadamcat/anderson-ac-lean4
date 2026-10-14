import AndersonAC.AgentS6.Decomposition

/-! Frozen helper contracts of lane agent-s6 for Proposition 6.6 (06-clearing.tex:826–1123).
Each is a proposition, never an assumed theorem. A helper proves exactly one of them as
`AndersonAC.AgentS6.<name>_proof : <Name>Statement` in its own module, with only
`propext`, `Classical.choice`, `Quot.sound`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Topology

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

/-- Distortion-budget failure (06-clearing.tex:788–800, 852–960, 1060–1110): entries, rows and
Frobenius vector of `ĥ - h⁰`, compressed to the cube `Q`, concentrate by the vector Lemma 5.6
(`VectorConcentrationInput`) with the displayed bias/variance/jump margins; outside `Q` the
collapsed-distance resolvent decay and shell counts give deterministic tails. -/
def BudgetTailStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (d : ℕ) (_hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc) (_hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (_hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)) (_hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (_hεpos : ∀ t, 0 ≤ ε t),
    ModeTail d c K Cloc cConc μ qlag ε budgetMode

/-- Leverage-cap failure (06-clearing.tex:962–1056, 1060–1110): the recorded fixed-ridge
row changes form one varying-ridge stream; both signs of the maximal inequality plus the
bias margins keep every constant-ridge interval change below `l_*`, so no row exceeds `3 l_*`.
Outside the cube `Q` projection decay rules out a crossing deterministically. -/
def CapTailStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (d : ℕ) (_hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc) (_hConc : 0 < cConc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (_hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)) (_hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (_hεpos : ∀ t, 0 ≤ ε t),
    ModeTail d c K Cloc cConc μ qlag ε capMode

/-- Conditional form of Lemma 6.4 for the stopped trial: discharge `LeverageDriftInput` from
`AndersonAC.L64.leverage_drift`, applied pointwise to the regular conditional law of the
queried residual given `q.history k` (Mathlib `condExp_prod_ae_eq_integral_condDistrib`
with `X = id : Ω → (Ω, q.history k)`), see opus-l64 REPORT.md "sol-s6 alignment".
The prestate hypotheses of Lemma 6.4 at running prestates come from the budgets and the start
slack (`Planned.prestate_from_budgets`), `running_cap`, `pivot_max`, the core bound, and the
residual inputs of `TrialLocalInput` after the pivot-location step (Lemma 6.2 with the §2 Ward
input and `metric`/`range_geometry`). The uniform `ε` comes from Lemma 6.4.
The weights are restricted to the running event (`onRunning`): after the stop the trial's
ridge is unconstrained, so unrestricted integrability can fail (luna-s6lev, 3d63b8e). -/
def LeverageDriftDischargeStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (_hWard : AndersonAC.Blueprint.WardInput)
    (d : ℕ) (_hd : 3 ≤ d) (c K Cloc : ℝ) (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag : ℝ → ℝ)
    (_hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)),
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ (∀ t, 0 ≤ ε t) ∧ ∃ t0 : ℝ, 0 < t0 ∧
      ∀ (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
        (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
        (q : StoppedTrial (Ω := Ω) core t r g0 order)
        (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → 1 ≤ core.card → (core.card : ℝ) ≤ coreCap d t → (∀ ω, BroadBounds c K (r ω)) →
      (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
      (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      LeverageDriftInput μ q.history (ε t) (fun k => {ω | k < q.stop ω})
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω)))
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω)))

/-- Vector Lemma 5.6 from the blueprint matrix inequality (sol-s6 PLAN "Architecture
correspondence": Hermitian dilation and conditionalization), with a uniform constant. Needed by
WP10 to supply the `VectorConcentrationInput` hypothesis of Proposition 6.6. Route: Hermitian
dilation `𝒟(z) = [[0, z*], [z, 0]]` of size `D+1` (opNorm `‖z‖`, `𝒟(z)² ≤ ‖z‖² I`),
truncation after `N`, and conditioning on `F 0` by applying `maximal` to the normalized
restrictions `μ(· ∩ A)/μ(A)`, `A ∈ F 0`, then `μ(E ∩ A) ≤ B μ(A)` for all such `A` gives the
a.e. conditional bound. -/
def VectorConcentrationBridgeStatement : Prop :=
  AndersonAC.Blueprint.ConcentrationInput →
    ∃ c : ℝ, 0 < c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (F : Filtration ℕ ‹MeasurableSpace Ω›), VectorConcentrationInput μ F c

end AndersonAC.AgentS6
