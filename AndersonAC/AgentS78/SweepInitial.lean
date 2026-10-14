import AndersonAC.AgentS78.SweepJoin

/-!
WP10: the `AssemblyInput` fields `initialRows` and `initialLag` for the post-sweep state
(`I.state 0 = sw`) from the lag and fourth-row conclusions of `S45.ordinary_sweep_endpoint`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem sweep_initial_rows_lag {d m n : ℕ} (old sw : Endpoint (Torus d m)) (rOld : Torus d m → ℂ)
    (t θ C' : ℝ) (ht : 0 < t) (hθ : 1 / 4 ≤ θ) (hθ1 : θ ≤ 1) (hC' : 0 ≤ C')
    (hzero : ∀ i j, i ∉ sw.active ∨ j ∉ sw.active → sw.g i j = 0)
    (hact : sw.active = old.active) (e : Fin n ≃ old.active)
    (hlag : ∀ i, ‖(toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).g i i -
      (toS45 old rOld e).r i‖ ≤ C' * AndersonAC.S45.power t AndersonAC.S45.beta)
    (hrows : ∀ i, (toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).fourthRow
      (θ * t) Finset.univ i < (7 / 10 : ℝ) * AndersonAC.S45.rowCap (θ * t)) :
    (∀ i, rowFour (normalizedInverse sw (θ * t)) i ≤ 0.7 * (θ * t) ^ (1 + delta)) ∧
    (∀ i ∈ sw.active, ‖sw.g i i - rOld i‖ ≤ (4 * C') * (θ * t) ^ (0.42 * delta)) := by
  set e' : Fin n ≃ sw.active := e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])) with he'
  have hθt : 0 < θ * t := by positivity
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · by_cases hi : i ∈ sw.active
    · have h := hrows (e'.symm ⟨i, hi⟩)
      rw [← rowFour_eq_S45 sw rOld (θ * t) e' hzero] at h
      simp only [Equiv.apply_symm_apply] at h
      unfold AndersonAC.S45.rowCap AndersonAC.S45.power at h
      rw [Real.rpow_eq_pow] at h
      have : (1 + AndersonAC.S45.delta) = 1 + delta := by norm_num [AndersonAC.S45.delta, delta]
      rw [this] at h
      linarith
    · rw [rowFour_inactive sw (θ * t) hzero i hi]
      have := Real.rpow_nonneg hθt.le (1 + delta)
      linarith
  · have h := hlag (e'.symm ⟨i, hi⟩)
    have hv : (e (e'.symm ⟨i, hi⟩)).val = i := by
      have : (e' (e'.symm ⟨i, hi⟩)).val = i := by simp
      exact this
    simp only [toS45] at h
    have hv' : (e' (e'.symm ⟨i, hi⟩)).val = i := by simp
    rw [hv', hv] at h
    have hb : AndersonAC.S45.power t AndersonAC.S45.beta = t ^ (0.42 * delta) := by
      unfold AndersonAC.S45.power; rw [Real.rpow_eq_pow]; congr 1
      norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta, delta]
    rw [hb] at h
    -- t ≤ 4 (θ t)
    have h4 : t ≤ 4 * (θ * t) := by nlinarith
    have hexp : (0 : ℝ) ≤ 0.42 * delta := by norm_num [delta]
    have hexp1 : 0.42 * delta ≤ (1 : ℝ) := by norm_num [delta]
    have hpow : t ^ (0.42 * delta) ≤ 4 * (θ * t) ^ (0.42 * delta) := by
      calc t ^ (0.42 * delta) ≤ (4 * (θ * t)) ^ (0.42 * delta) :=
            Real.rpow_le_rpow ht.le h4 hexp
        _ = 4 ^ (0.42 * delta) * (θ * t) ^ (0.42 * delta) := by
            rw [Real.mul_rpow (by norm_num) hθt.le]
        _ ≤ 4 * (θ * t) ^ (0.42 * delta) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hθt.le _)
            calc (4 : ℝ) ^ (0.42 * delta) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1
              _ = 4 := by norm_num
    calc ‖sw.g i i - rOld i‖ ≤ C' * t ^ (0.42 * delta) := h
      _ ≤ C' * (4 * (θ * t) ^ (0.42 * delta)) := mul_le_mul_of_nonneg_left hpow hC'
      _ = 4 * C' * (θ * t) ^ (0.42 * delta) := by ring

end AndersonAC.AgentS78
