import AndersonAC.AgentS6Budget.HeatColumn
import AndersonAC.AgentS6.FarTail

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace AndersonAC.AgentS6Budget
open AndersonAC.S6 AndersonAC.AgentS6

theorem distanceToCore_triangle {ι : Type*} [Fintype ι]
    (dist : ι → ι → ℝ) (core : Finset ι) (hcore : core.Nonempty)
    (htri : ∀ i j k, dist i k ≤ dist i j + dist j k) (i x : ι) :
    distanceToCore dist core i ≤ dist i x + distanceToCore dist core x := by
  unfold distanceToCore
  rw [dif_pos hcore, dif_pos hcore]
  obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_inf' hcore (dist x)
  calc
    core.inf' hcore (dist i) ≤ dist i b := Finset.inf'_le (dist i) hb
    _ ≤ dist i x + dist x b := htri i x b
    _ = dist i x + core.inf' hcore (dist x) := by rw [he]

open Classical in
def monitoringRegion {ι : Type*} [Fintype ι] (dist : ι → ι → ℝ)
    (core : Finset ι) (t ell : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => distanceToCore dist core i ≤ ell / 2 + t ^ (-5 : ℤ) + 1)

theorem heatColumn_far_mass (d : ℕ) (c K : ℝ) (hc : 0 < c) (hK : 1 ≤ K) :
    ∃ C c' t0 : ℝ, 0 < C ∧ 0 < c' ∧ 0 < t0 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (core : Finset (Fin n))
      (t : ℝ) (r : Ω → Fin n → ℂ) (g0 : Ω → Matrix (Fin n) (Fin n) ℂ)
      (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (μ : Measure Ω) (Cloc : ℝ) (dist : Fin n → Fin n → ℝ)
      (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t ≤ 1 / 4 → t < t0 → core.Nonempty →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      (∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2) →
      ∀ k ω, ∑ i ∈ Finset.univ \ monitoringRegion dist core t ell,
        ‖heatColumn q k ω i‖ ^ 2 ≤
        C * K ^ 3 / t * t ^ (-(d : ℝ)) * Real.exp (-c' * t ^ (-4 : ℤ)) := by
  obtain ⟨C, c', t0, hC, hc', ht0, hfar⟩ := far_tail d c hc
  refine ⟨C, c', t0, hC, hc', ht0, ?_⟩
  intro Ω _ n core t r g0 order q μ Cloc dist collapsed ell ht ht4 htt hcore hloc hpiv k ω
  classical
  by_cases hk : k < q.stop ω
  · let x := q.pivot k ω
    have hx := (q.heat k ω hk).choose
    have hprior : ∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2 :=
      fun j hj => hpiv j ω (hj.trans hk)
    have hdecay : ∀ i, ‖heatColumn q k ω i‖ ≤
        K / Real.sqrt t * Real.exp (-c * t * collapsed k ω i x) := by
      intro i
      by_cases hi : ω ∈ survivorEvent q k i
      · have hia := active_antitone q ω (by omega : k ≤ k + 1) (by omega)
          ((mem_survivorEvent q k ω i).mp hi).2
        rw [heatColumn, Set.indicator_of_mem hi]
        have he : scaledInverse t (q.state k ω).hatG i x =
            scaledInverse t (trialInverse t (r ω) (q.state k ω)) ⟨i, hia⟩ ⟨x, hx⟩ := by
          simp only [scaledInverse, Matrix.smul_apply]
          rw [hatG_eq_trialInverse q k ω hk.le ⟨i, hia⟩ ⟨x, hx⟩]
        rw [he]
        exact hloc.resolvent_decay k ω hk hprior ⟨i, hia⟩ ⟨x, hx⟩
      · simp only [heatColumn, Set.indicator_of_notMem hi, norm_zero]
        exact mul_nonneg (div_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    have hquarter : ∀ i, t ^ (-5 : ℤ) ≤ dist i x → dist i x / 4 ≤ collapsed k ω i x :=
      fun i hi => collapsed_quarter ht ht4 hi (hloc.metric k ω hk.le hprior i x)
    have hshell : ∀ m : ℕ,
        ((Finset.univ.filter (fun i => (m : ℝ) ≤ dist i x ∧ dist i x < m + 1)).card : ℝ) ≤
        K * (1 + (m : ℝ)) ^ (d - 1) := by
      intro m
      simpa only [hloc.dist_symm _ x] using hloc.shells x m
    have htail := hfar t ht htt (fun i => dist i x) (fun i => collapsed k ω i x)
      (heatColumn q k ω) K K (by linarith) hshell hdecay hquarter
    have hsub : Finset.univ \ monitoringRegion dist core t ell ⊆
        Finset.univ.filter (fun i => t ^ (-5 : ℤ) + 1 ≤ dist i x) := by
      intro i hi
      have hi' : ell / 2 + t ^ (-5 : ℤ) + 1 < distanceToCore dist core i := by
        simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, monitoringRegion,
          Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi
      have htri := distanceToCore_triangle dist core hcore hloc.dist_triangle i x
      have hpx := hpiv k ω hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      linarith
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)).trans
      (by convert htail using 1 <;> ring)
  · simp only [heatColumn_eq_zero_of_not_running q k ω hk, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity

end AndersonAC.AgentS6Budget

#print axioms AndersonAC.AgentS6Budget.heatColumn_far_mass
