import AndersonAC.AgentS6Lev2.Law
import AndersonAC.AgentS6Lev2.Transfer

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Topology

namespace AndersonAC.AgentS6
open AndersonAC.S6 AndersonAC.AgentS6Lev2

universe u

/-- The drift modulus and threshold are uniform over probability spaces and trials. -/
def LeverageDriftUniformStatement : Prop :=
  ∀ (_hWard : AndersonAC.Blueprint.WardInput)
    (d : ℕ) (_hd : 3 ≤ d) (c K Cloc : ℝ) (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc)
    (qlag : ℝ → ℝ) (_hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)),
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ (∀ t, 0 ≤ ε t) ∧ ∃ t0 : ℝ, 0 < t0 ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
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

theorem leverageDriftUniform_proof : LeverageDriftUniformStatement.{u} := by
  intro hWard d hd c K Cloc hc hK hCloc qlag hqlag
  let P : ℝ → ℝ → Prop := fun t e =>
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (core : Finset (Fin n)) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      1 ≤ core.card → (core.card : ℝ) ≤ coreCap d t → (∀ ω, BroadBounds c K (r ω)) →
      (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
      (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      LeverageDriftInput μ q.history e (fun k => {ω | k < q.stop ω})
        (onRunning (fun k => {ω | k < q.stop ω}) (preW q))
        (onRunning (fun k => {ω | k < q.stop ω}) (postW q))
  have hP : ∀ e > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → P t e := by
    intro e he
    obtain ⟨td, htd, hlaw⟩ := conditional_l64_bounds d hd c K hc hK e he
    obtain ⟨tp, htp, hpre⟩ := trial_running_prestate K hK c qlag hqlag
    obtain ⟨tl, htl, hloc⟩ := trial_pivots_located hWard d c K Cloc hc
    refine ⟨min td (min tp tl), lt_min htd (lt_min htp htl), ?_⟩
    intro t ht htt Ω _ μ _ n core r g0 order q dist collapsed ell _ hcard hb hfour hlag hin
    have httd : t < td := htt.trans_le (min_le_left _ _)
    have htlower := htt.trans_le (min_le_right _ _)
    have hprestate := hpre n core t r g0 order q ht
      (htlower.trans_le (min_le_left _ _)) hb hfour hlag
    have hpiv := hloc μ n core t r g0 order q dist collapsed ell ht
      (htlower.trans_le (min_le_right _ _)) hb hin
    have hbounds := hlaw μ q Cloc dist collapsed ell ht httd hcard hb hprestate hin hpiv
    have hr : ∀ ω i, 0 < (r ω i).im := fun ω i => hc.trans_le ((hb ω).2 i).2.1
    refine ⟨integrable_total_onRunning_pre q μ, integrable_total_onRunning_post q μ,
      integrable_square_onRunning_pre q μ, integrable_square_onRunning_post q μ, ?_, ?_⟩
    · intro k
      filter_upwards [hbounds k, condExp_trialDelta false μ q ht hr k] with ω hbound hce hk
      obtain ⟨hx, hA, -⟩ := hbound hk
      have hfun : (fun y => kernelFn false q k (ω, y)) =
          fun y => l64Delta false (q.state k ω).M t
            (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω))
            ⟨q.pivot k ω, hx⟩ (q.ridge k ω) y := by
        funext y; exact kernelFn_eq_running false q k ω hk hx ht (hr ω) y
      have hmax : maxWeight (onRunning (fun k => {ω | k < q.stop ω}) (preW q) k ω) =
          maxWeight (preW q k ω) := by simp [onRunning, hk]
      rw [hmax]
      change |μ[trialDelta false q k | q.history k] ω| ≤ _
      rw [hce, hfun]
      exact hA
    · intro k
      filter_upwards [hbounds k, condExp_trialDelta true μ q ht hr k] with ω hbound hce hk
      obtain ⟨hx, -, hP⟩ := hbound hk
      have hfun : (fun y => kernelFn true q k (ω, y)) =
          fun y => l64Delta true (q.state k ω).M t
            (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω))
            ⟨q.pivot k ω, hx⟩ (q.ridge k ω) y := by
        funext y; exact kernelFn_eq_running true q k ω hk hx ht (hr ω) y
      have hmax : maxWeight (onRunning (fun k => {ω | k < q.stop ω}) (preW q) k ω) =
          maxWeight (preW q k ω) := by simp [onRunning, hk]
      rw [hmax]
      change μ[trialDelta true q k | q.history k] ω ≤ _
      rw [hce, hfun]
      exact hP
  obtain ⟨ε, hε, hεpos, t0, ht0, hmod⟩ := exists_tendsto_error_modulus hP
  refine ⟨ε, hε, hεpos, t0, ht0, ?_⟩
  intro Ω _ μ _ n core t r g0 order q dist collapsed ell ht htt hcore hcard hb hfour hlag hin
  exact hmod t ht htt μ n core r g0 order q dist collapsed ell hcore hcard hb hfour hlag hin

theorem leverageDriftDischarge_proof : LeverageDriftDischargeStatement.{u} := by
  intro Ω _ hWard d hd c K Cloc hc hK hCloc μ _ qlag hqlag
  obtain ⟨ε, hε, hpos, t0, ht0, h⟩ := leverageDriftUniform_proof.{u} hWard d hd c K Cloc hc hK hCloc qlag hqlag
  exact ⟨ε, hε, hpos, t0, ht0, h μ⟩

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.leverageDriftUniform_proof
#print axioms AndersonAC.AgentS6.leverageDriftDischarge_proof
