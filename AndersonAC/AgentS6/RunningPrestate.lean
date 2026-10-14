import AndersonAC.AgentS6.Prestate

/-! Running heat prestates of the stopped trial (06-clearing.tex:815–821, 862–870): the
bookkeeping matrix `ĥ` equals the active inverse on active pairs, and with the budgets and the
start slack every running prestate satisfies `clearing-prestate` with constant `3K+1`. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

theorem hatG_eq_trialInverse {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
    {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))} (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (hk : k ≤ q.stop ω) (i j : {i // i ∈ (q.state k ω).active}) :
    (q.state k ω).hatG i j = trialInverse t (r ω) (q.state k ω) i j := by
  cases k with
  | zero => rw [q.start_entries ω, q.initial_inverse ω]
  | succ k =>
    obtain ⟨-, -, -, -, -, hG⟩ := q.heat k ω (by omega)
    rw [hG, dif_pos i.2, dif_pos j.2]
    ring

theorem trial_running_prestate (K : ℝ) (hK : 1 ≤ K) (c : ℝ) (qlag : ℝ → ℝ)
    (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (n : ℕ)
      (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ) (g0 : Ω → Matrix (Fin n) (Fin n) ℂ)
      (order : Fin n ≃ Fin (Fintype.card (Fin n))) (q : StoppedTrial (Ω := Ω) core t r g0 order),
      0 < t → t < t0 → (∀ ω, BroadBounds c K (r ω)) →
      (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
      (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
      ∀ k ω, k < q.stop ω → HeatPrestate t (3 * K + 1)
        (fun i : {i // i ∈ (q.state k ω).active} => r ω i) (trialInverse t (r ω) (q.state k ω)) := by
  have hev := prestate_from_budgets K hK qlag hqlag
  obtain ⟨t0, ht0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨t0, ht0, ?_⟩
  intro Ω _ n core t r g0 order q ht htt hb hfourth hlag k ω hk
  have hpre := hsub ⟨ht, htt⟩ n (r ω) (g0 ω) (q.state k ω).hatG
    (fun i => ((hb ω).2 i).1) (hfourth ω) (hlag ω) (q.running_budgets k ω hk)
  obtain ⟨h1, h2, h3⟩ := hpre
  have hinv := hatG_eq_trialInverse q k ω hk.le
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [← hinv]; exact h1 i
  · rw [← hinv]; exact h2 i
  · calc fourthRow (scaledInverse t (trialInverse t (r ω) (q.state k ω))) i
        = ∑ j : {i // i ∈ (q.state k ω).active},
            ‖scaledInverse t (q.state k ω).hatG i j‖ ^ 4 := by
          unfold fourthRow
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [scaledInverse, Matrix.smul_apply, hinv]
      _ = ∑ j ∈ (q.state k ω).active, ‖scaledInverse t (q.state k ω).hatG i j‖ ^ 4 :=
          Finset.sum_coe_sort _ (fun j => ‖scaledInverse t (q.state k ω).hatG i j‖ ^ 4)
      _ ≤ ∑ j, ‖scaledInverse t (q.state k ω).hatG i j‖ ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => by positivity)
      _ ≤ fourthCap t := h3 i

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.hatG_eq_trialInverse
#print axioms AndersonAC.AgentS6.trial_running_prestate
