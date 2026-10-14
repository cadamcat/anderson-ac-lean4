import AndersonAC.AgentS6Cap.StreamInputs

noncomputable section

namespace AndersonAC.AgentS6

open AndersonAC.S6 MeasureTheory

theorem broadBounds_mono_K {ι : Type*} (c K K' : ℝ) (r : ι → ℂ)
    (h : BroadBounds c K r) (hKK : K ≤ K') : BroadBounds c K' r := by
  rcases h with ⟨hc, hsite⟩
  refine ⟨hc, fun i => ?_⟩
  rcases hsite i with ⟨hnorm, hlow, hup⟩
  exact ⟨hnorm.trans hKK, hlow, hup.trans hKK⟩

theorem trialLocalInput_mono_K
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t c K K' Cloc : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    {μ : Measure Ω} {d : ℕ} {dist : Fin n → Fin n → ℝ}
    {collapsed : ℕ → Ω → Fin n → Fin n → ℝ} {ell : ℝ}
    (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (hin : TrialLocalInput q μ d c K Cloc dist collapsed ell)
    (ht : 0 < t) (hKK : K ≤ K') :
    TrialLocalInput q μ d c K' Cloc dist collapsed ell := by
  refine {
    dist_nonneg := hin.dist_nonneg
    dist_symm := hin.dist_symm
    dist_triangle := hin.dist_triangle
    dist_self := hin.dist_self
    ell_lower := hin.ell_lower
    ell_upper := hin.ell_upper
    core_ball := hin.core_ball
    shells := ?_
    volume := ?_
    metric := hin.metric
    range_geometry := hin.range_geometry
    resolvent_decay := ?_
    residual_bound := ?_
    residual_integrable := hin.residual_integrable
    residual_square_integrable := hin.residual_square_integrable
    residual_mean := hin.residual_mean
    residual_variance := ?_ }
  · intro i m
    calc
      _ ≤ K * (1 + (m : ℝ)) ^ (d - 1) := hin.shells i m
      _ ≤ K' * (1 + (m : ℝ)) ^ (d - 1) := by
        gcongr
  · intro i L hL
    calc
      _ ≤ K * (1 + L) ^ d := hin.volume i L hL
      _ ≤ K' * (1 + L) ^ d := by gcongr
  · intro k ω hk hprior i j
    calc
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) i j‖ ≤
          K / Real.sqrt t * Real.exp (-c * t * collapsed k ω i j) :=
        hin.resolvent_decay k ω hk hprior i j
      _ ≤ K' / Real.sqrt t * Real.exp (-c * t * collapsed k ω i j) := by
        gcongr
  · intro k ω hk hloc
    calc
      |q.residual k ω| ≤ K * Real.sqrt t := hin.residual_bound k ω hk hloc
      _ ≤ K' * Real.sqrt t := by gcongr
  · intro k
    obtain ⟨η, hη, hvar⟩ := hin.residual_variance k
    refine ⟨η, hη, ?_⟩
    filter_upwards [hvar] with ω hω hrun hloc
    rcases hω hrun hloc with ⟨h0, h1, h2⟩
    refine ⟨h0, ?_, h2⟩
    calc
      η ω / t ≤ K * t := h1
      _ ≤ K' * t := by gcongr

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.trialLocalInput_mono_K
