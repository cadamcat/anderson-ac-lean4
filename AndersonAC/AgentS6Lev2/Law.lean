import AndersonAC.AgentS6Lev2.Kernel

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Topology

namespace AndersonAC.AgentS6Lev2
open AndersonAC.S6 AndersonAC.AgentS6

universe u

/-- L64 at the regular conditional residual law, with a threshold independent of the trial. -/
theorem conditional_l64_bounds (d : ℕ) (hd : 3 ≤ d) (c K : ℝ) (hc : 0 < c)
    (hK : 1 ≤ K) (e : ℝ) (he : 0 < e) :
    ∃ t0 > 0, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
      {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
      {order : Fin n ≃ Fin (Fintype.card (Fin n))}
      (q : StoppedTrial (Ω := Ω) core t r g0 order) (Cloc : ℝ)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → (core.card : ℝ) ≤ coreCap d t →
      (∀ ω, BroadBounds c K (r ω)) →
      (∀ k ω, k < q.stop ω → HeatPrestate t (3 * K + 1)
        (fun i : (q.state k ω).active => r ω i) (trialInverse t (r ω) (q.state k ω))) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      (∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2) →
      ∀ k, ∀ᵐ ω ∂μ, ∀ hk : k < q.stop ω,
        ∃ hx : q.pivot k ω ∈ (q.state k ω).active,
          |∫ y, l64Delta false (q.state k ω).M t
            (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω))
            ⟨q.pivot k ω, hx⟩ (q.ridge k ω) y ∂residualLaw μ q k ω| ≤
              e * maxWeight (preW q k ω) ∧
          (∫ y, l64Delta true (q.state k ω).M t
            (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω))
            ⟨q.pivot k ω, hx⟩ (q.ridge k ω) y ∂residualLaw μ q k ω) ≤
              -(1 - e) * (maxWeight (preW q k ω)) ^ 2 := by
  obtain ⟨hν0, hν1, he0, he1, hβ0, hβ1, -⟩ := parameter_margins d hd
  obtain ⟨t0, ht0, hL64⟩ := AndersonAC.L64.leverage_drift (C := 3 * K + 1)
    hc hν0 hν1 he0 he1 hβ0 hβ1 e he
  refine ⟨t0, ht0, ?_⟩
  intro Ω _ μ _ n core t r g0 order q Cloc dist collapsed ell ht htt hcard hb hpre hlocal hloc k
  have hmean : ∀ᵐ ω ∂μ, k < q.stop ω → μ[q.residual k | q.history k] ω = 0 := by
    filter_upwards [hlocal.residual_mean k] with ω hω hk
    exact hω hk (hloc k ω hk)
  obtain ⟨η, hηm, hη⟩ := hlocal.residual_variance k
  have hsecond : ∀ᵐ ω ∂μ, k < q.stop ω →
      μ[(fun ω => (q.residual k ω) ^ 2) | q.history k] ω = t - η ω := by
    filter_upwards [hη] with ω hω hk
    exact (hω hk (hloc k ω hk)).2.2
  have hmoment := condDistrib_moments_of_condExp μ (q.history k) (q.residual k)
    {ω | k < q.stop ω} (q.history.le k) (hlocal.residual_integrable k)
    (hlocal.residual_square_integrable k) t η hmean hsecond
  have hbound := condDistrib_bound_on_event μ (q.history k) (q.residual k)
    {ω | k < q.stop ω} (q.history.le k) (running_measurableSet q k)
    ((q.residual_revealed k).measurable.mono (q.history.le (k + 1)) le_rfl)
    (K * Real.sqrt t) (fun ω hk => hlocal.residual_bound k ω hk (hloc k ω hk))
  filter_upwards [hmoment, hbound, hη] with ω hm hboundω hηω hk
  obtain ⟨hx, hxcore, -⟩ := q.heat k ω hk
  let κ := residualLaw μ q k ω
  haveI : IsProbabilityMeasure κ := by
    dsimp only [κ, residualLaw]
    infer_instance
  have hKC : K ≤ 3 * K + 1 := by linarith
  have hp : ∀ i : (q.state k ω).active, c ≤ (r ω i).im ∧ (r ω i).im ≤ 3 * K + 1 :=
    fun i => ⟨((hb ω).2 i).2.1, ((hb ω).2 i).2.2.trans hKC⟩
  have hpreω := hpre k ω hk
  have hxB : (⟨q.pivot k ω, hx⟩ : (q.state k ω).active) ∉ actCore (q.state k ω) :=
    fun h => hxcore (mem_actCore_iff.mp h)
  have hpiv : AndersonAC.L64.preLev (q.state k ω).M t
      (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω)) (q.ridge k ω)
      ⟨q.pivot k ω, hx⟩ = maxWeight (preW q k ω) := by
    rw [AndersonAC.L64.preLev, ← preInverse_eq,
      preLev_eq (t := t) (q.state k ω) (r ω) (q.ridge k ω) ⟨q.pivot k ω, hx⟩ hxcore]
    exact q.pivot_max k ω hk
  have hmax : ∀ i ∈ (actCore (q.state k ω))ᶜ,
      AndersonAC.L64.preLev (q.state k ω).M t
        (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω)) (q.ridge k ω) i ≤
      AndersonAC.L64.preLev (q.state k ω).M t
        (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω)) (q.ridge k ω)
        ⟨q.pivot k ω, hx⟩ := by
    intro i hi
    have hicore : (i : Fin n) ∉ core :=
      fun h => (Finset.mem_compl.mp hi) (mem_actCore_iff.mpr h)
    rw [hpiv, AndersonAC.L64.preLev, ← preInverse_eq,
      preLev_eq (t := t) (q.state k ω) (r ω) (q.ridge k ω) i hicore]
    exact le_maxWeight _ i.val
  have hηbounds := hηω hk (hloc k ω hk)
  have hout := hL64 t ht htt (q.state k ω).M
    (fun i : (q.state k ω).active => r ω i) (actCore (q.state k ω))
    ⟨q.pivot k ω, hx⟩ (q.ridge k ω) κ id (η ω)
    (q.state k ω).symmetric
    (by simpa only [preInverse_eq] using hpreω.1) hp
    (by simpa only [preInverse_eq] using hpreω.2.1)
    (by simpa only [preInverse_eq, fourthRow, fourthCap, scaledInverse, Matrix.smul_apply, smul_eq_mul]
      using hpreω.2.2)
    (by simpa only [actCore_card, coreCap] using hcard) hxB (q.running_ridge k ω hk) hmax
    (by rw [hpiv]; exact (q.running_cap k ω hk).1)
    (by rw [hpiv]; exact (q.running_cap k ω hk).2)
    measurable_id (hm hk).1 (hm hk).2
    (by filter_upwards [hboundω hk] with y hy; exact hy.trans (mul_le_mul_of_nonneg_right hKC (Real.sqrt_nonneg t)))
    hηbounds.1 (hηbounds.2.1.trans (mul_le_mul_of_nonneg_right hKC ht.le))
  refine ⟨hx, ?_, ?_⟩
  · simpa only [l64Delta, Bool.false_eq_true, ↓reduceIte, id_eq, hpiv] using hout.2.2.1
  · simpa only [l64Delta, ↓reduceIte, id_eq, hpiv] using hout.2.2.2

end AndersonAC.AgentS6Lev2

#print axioms AndersonAC.AgentS6Lev2.conditional_l64_bounds
