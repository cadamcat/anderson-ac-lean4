import AndersonAC.S6.Definitions

/-! Elementary order facts about the query history σ-algebras. -/

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6 MeasureTheory

variable {ι Ω : Type*} [MeasurableSpace ι]

theorem queryHistory_mono (F0 : MeasurableSpace Ω) (p : ℕ → Ω → ι) (ρ : ℕ → Ω → ℝ) :
    Monotone (queryHistory F0 p ρ) := by
  intro a b hab
  exact sup_le_sup_left (biSup_mono fun j hj =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hab)) _

theorem le_queryHistory (F0 : MeasurableSpace Ω) (p : ℕ → Ω → ι) (ρ : ℕ → Ω → ℝ)
    (k : ℕ) : F0 ≤ queryHistory F0 p ρ k := le_sup_left

theorem residual_le_queryHistory (F0 : MeasurableSpace Ω) (p : ℕ → Ω → ι)
    (ρ : ℕ → Ω → ℝ) (k : ℕ) :
    MeasurableSpace.comap (ρ k) (borel ℝ) ≤ queryHistory F0 p ρ (k + 1) := by
  have h : MeasurableSpace.comap (p k) ‹MeasurableSpace ι› ⊔
      MeasurableSpace.comap (ρ k) (borel ℝ) ≤ ⨆ j ∈ Finset.range (k + 1),
        (MeasurableSpace.comap (p j) ‹MeasurableSpace ι› ⊔
          MeasurableSpace.comap (ρ j) (borel ℝ)) :=
    le_iSup₂ (f := fun j (_ : j ∈ Finset.range (k + 1)) =>
      MeasurableSpace.comap (p j) ‹MeasurableSpace ι› ⊔
        MeasurableSpace.comap (ρ j) (borel ℝ)) k (Finset.mem_range.2 k.lt_succ_self)
  exact le_sup_of_le_right (le_trans le_sup_right h)

theorem measurable_residual_queryHistory (F0 : MeasurableSpace Ω) (p : ℕ → Ω → ι)
    (ρ : ℕ → Ω → ℝ) (k : ℕ) : Measurable[queryHistory F0 p ρ (k + 1)] (ρ k) :=
  Measurable.mono (comap_measurable (ρ k)) (residual_le_queryHistory F0 p ρ k) le_rfl

theorem queryHistory_le (F0 m : MeasurableSpace Ω) (p : ℕ → Ω → ι) (ρ : ℕ → Ω → ℝ)
    (hF : F0 ≤ m) (hp : ∀ j, Measurable[m] (p j)) (hρ : ∀ j, Measurable[m] (ρ j))
    (k : ℕ) : queryHistory F0 p ρ k ≤ m :=
  sup_le hF (iSup₂_le fun j _ => sup_le (hp j).comap_le (hρ j).comap_le)

end AndersonAC.AgentS6Construct
