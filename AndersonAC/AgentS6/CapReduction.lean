import AndersonAC.AgentS6.TrialLocation
import AndersonAC.AgentS6.CapTelescope
import AndersonAC.AgentS6.Decomposition

/-! Reduction of the cap failure mode to finitely many monitored rows
(06-clearing.tex:1036–1056, 1060–1066): rows at ordinary distance `≥ ℓ/2` from the core have
weight `< 2 l_*` at every reached state and positive ridge (projection decay), and on the other
rows a cap failure forces a prefix sum of recorded changes above `l_*/2` before `n_h`. -/

noncomputable section
open scoped BigOperators Topology Matrix
open Filter Set MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

theorem trial_far_rows (hWard : AndersonAC.Blueprint.WardInput) (d : ℕ) (c K Cloc : ℝ)
    (hc : 0 < c) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
      (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ) (g0 : Ω → Matrix (Fin n) (Fin n) ℂ)
      (order : Fin n ≃ Fin (Fintype.card (Fin n))) (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → (∀ ω, BroadBounds c K (r ω)) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      ∀ k ω, k ≤ q.stop ω → ∀ τ, 0 < τ → ∀ i, ell / 2 ≤ distanceToCore dist core i →
        trialWeights t (r ω) (q.state k ω) τ i < 2 * leverageScale t := by
  obtain ⟨t1, ht1, hlocated⟩ := trial_pivots_located.{u} hWard d c K Cloc hc
  by_cases hcK : c ≤ K
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro Ω _ μ n core t r g0 order q dist collapsed ell _ _ hb _ k ω _ τ _ i _
    exfalso
    obtain ⟨-, hi⟩ := hb ω
    obtain ⟨-, h1, h2⟩ := hi i
    exact hcK (h1.trans h2)
  obtain ⟨a, L, ha, hL, hloc⟩ := range_localization hWard d c K hc hcK
  have hL2 : 0 < L ^ 2 := by positivity
  refine ⟨min (min (min (1 / 64) (2 * (a / 1024) / L ^ 2)) 1) t1, by positivity, ?_⟩
  intro Ω _ μ n core t r g0 order q dist collapsed ell ht htT hb hin k ω hk τ hτ i hi
  have htT' : t < min (min (1 / 64) (2 * (a / 1024) / L ^ 2)) 1 :=
    lt_of_lt_of_le htT (min_le_left _ _)
  have ht1' : t ≤ 1 := (lt_of_lt_of_le htT' (min_le_right _ _)).le
  have htp : t < min (1 / 64) (2 * (a / 1024) / L ^ 2) := lt_of_lt_of_le htT' (min_le_left _ _)
  have hs : 0 ≤ t ^ (-(103 / 100 : ℝ)) := Real.rpow_nonneg ht.le _
  have hprior : ∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2 := fun j hj =>
    hlocated μ n core t r g0 order q dist collapsed ell ht
      (lt_of_lt_of_le htT (min_le_right _ _)) hb hin j ω (by omega)
  obtain ⟨H, hgeo⟩ := hin.range_geometry k ω hk hprior
  set e : Fin (Fintype.card {b // b ∈ core}) ≃ {b // b ∈ core} := (Fintype.equivFin _).symm
  have hgeo' := exteriorGeometry_reindex e hgeo
  obtain ⟨-, hdecay⟩ := hloc (Fintype.card {b // b ∈ core}) n t (r ω) _ H _ ht ht1' (hb ω) hgeo'
  set C := trialCross t (r ω) (q.state k ω) with hC
  set m := trialWeights t (r ω) (q.state k ω) τ with hmdef
  have hmetric := distanceToCore_metric dist (collapsed k ω) core _ hs
    (hin.metric k ω hk hprior)
  have hm : ∀ j, m j ≤ L ^ 2 * Real.exp (-2 * a * t *
      max (distanceToCore dist core j / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) := by
    intro j
    have h1 : m j ≤ projectionWeight C j := ((ridge_calculus C _ hτ).2.2.2.2.1 j).2
    have h2 := hdecay j
    rw [projectionWeight_reindex] at h2
    have h3 : max (distanceToCore dist core j / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0 ≤
        max (distanceToCore (collapsed k ω) core j - 1) 0 :=
      max_le_max (by linarith [hmetric j]) le_rfl
    have h4 : Real.exp (-2 * a * t * max (distanceToCore (collapsed k ω) core j - 1) 0) ≤
        Real.exp (-2 * a * t *
          max (distanceToCore dist core j / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ 2 * a * t := by positivity
      nlinarith
    calc m j ≤ projectionWeight C j := h1
      _ ≤ _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hL2.le
  by_contra hge
  have hx : 2 * leverageScale t ≤ m i := le_of_not_gt hge
  have := pivot_location_at ha hL2 ht htp m (distanceToCore dist core) ell hin.ell_lower hm i hx
  linarith

/-- Cap failure forces a monitored row (distance `< ℓ/2`) with a prefix of recorded changes
above `l_*/2` at some `s ≤ n_h`. -/
theorem capMode_rows (hWard : AndersonAC.Blueprint.WardInput) (d : ℕ) (c K Cloc : ℝ)
    (hc : 0 < c) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
      (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ) (g0 : Ω → Matrix (Fin n) (Fin n) ℂ)
      (order : Fin n ≃ Fin (Fintype.card (Fin n))) (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → (∀ ω, BroadBounds c K (r ω)) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      ∀ ω, capMode n core t r g0 order q ω →
        ∃ i, distanceToCore dist core i < ell / 2 ∧ ∃ s ≤ heatLimit t,
          leverageScale t / 2 < |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i| := by
  obtain ⟨t1, ht1, hfar⟩ := trial_far_rows.{u} hWard d c K Cloc hc
  refine ⟨min t1 1, by positivity, ?_⟩
  intro Ω _ μ n core t r g0 order q dist collapsed ell ht htT hb hin ω hcap
  have htt1 : t < t1 := lt_of_lt_of_le htT (min_le_left _ _)
  have ht1' : t ≤ 1 := (lt_of_lt_of_le htT (min_le_right _ _)).le
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hr : ∀ i, 0 < (r ω i).im := fun i =>
    lt_of_lt_of_le (hb ω).1 ((hb ω).2 i).2.1
  unfold capMode at hcap
  rcases Nat.eq_zero_or_pos (q.stop ω) with h0 | hpos
  · have := not_capMode_stop_zero q ht ht1' ω hr h0
    linarith
  by_contra hno
  push_neg at hno
  have hpre : ∀ i, (∀ s, |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i| ≤
      leverageScale t / 2) ∨
      trialWeights t (r ω) (q.state (q.stop ω) ω) (q.ridge (q.stop ω - 1) ω) i ≤
        3 * leverageScale t := by
    intro i
    by_cases hD : distanceToCore dist core i < ell / 2
    · left
      intro s
      have hzero : ∀ k, q.stop ω ≤ k → recordedLeverageIncrement q k ω i = 0 := by
        intro k hk
        unfold recordedLeverageIncrement
        rw [if_neg (fun h => absurd h.1 (not_lt.mpr hk))]
      have hsum : ∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i =
          ∑ k ∈ Finset.range (min s (q.stop ω)), recordedLeverageIncrement q k ω i := by
        rcases le_total s (q.stop ω) with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h, ← Finset.sum_range_add_sum_Ico _ h]
          rw [Finset.sum_eq_zero (fun k hk => hzero k (Finset.mem_Ico.mp hk).1), add_zero]
      rw [hsum]
      exact hno i hD _ ((min_le_right _ _).trans (q.finite_stop ω))
    · right
      have hτ := q.running_ridge (q.stop ω - 1) ω (by omega)
      have := hfar μ n core t r g0 order q dist collapsed ell ht htt1 hb hin (q.stop ω) ω le_rfl
        _ hτ i (le_of_not_gt hD)
      linarith
  have := cap_of_prefix q ht ht1' ω hr hpos hpre
  linarith

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.trial_far_rows
#print axioms AndersonAC.AgentS6.capMode_rows
