import AndersonAC.Blueprint.Target

noncomputable section
open MeasureTheory OAI.Anderson Filter
open scoped ENNReal

namespace AndersonAC.Blueprint

/-- OAI's criterion with the missing d=3 energy window parameter restored. -/
def windowThreshold (d : ℕ) (e₂ : ℝ) (k : ℕ) : Prop :=
  10 ≤ k ∧
  ∀ n₀ : ℕ, k ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ energyWindow d e₂ →
        (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (certificateEvent d k n₀ m u E)

/-- WP10's final true-variable endpoint, uniform in u, m, and E. -/
def CertificateFamily (e₂ : ℝ) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ k : ℕ, windowThreshold d e₂ k

/-- WP12 consumes only eventually-in-m certificates for each fixed energy.
Bounds k and u are independent of energy. The full true-variable matrix and
both inverse equalities are already part of `certificateEvent`. -/
def WeakCertificates (d : ℕ) (coupling : ℝ) (I : Set ℝ) : Prop :=
  ∃ (k n₀ : ℕ) (u : ℝ), 0 < k ∧ u ∈ Set.Ioc (1 / 4 : ℝ) 1 ∧
    scaleCoupling n₀ u = coupling ∧
    ∀ E : ℝ, E ∈ I → ∀ᶠ m in atTop,
      (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (certificateEvent d k n₀ m u E)

theorem windowThreshold_iff_of_four_le {d : ℕ} (hd : 4 ≤ d)
    (e₂ : ℝ) (k : ℕ) : windowThreshold d e₂ k ↔ thresholdCriterion d k := by
  simp only [windowThreshold, thresholdCriterion, energyWindow_of_four_le hd]

theorem weakCertificates_of_windowThreshold {d k : ℕ} {e₂ coupling : ℝ}
    (h : windowThreshold d e₂ k) (hc : 0 < coupling)
    (hb : coupling < Real.sqrt 3 / (2 : ℝ) ^ k) :
    WeakCertificates d coupling (energyWindow d e₂) := by
  obtain ⟨n₀, hn, u, hu, heq⟩ := coupling_parametrization hc hb
  have hk : 0 < k := lt_of_lt_of_le (by decide : 0 < 10) h.1
  refine ⟨k, n₀, u, hk, hu, heq, ?_⟩
  intro E hE
  filter_upwards [eventually_ge_atTop (4 * n₀)] with m hm
  exact h.2 n₀ hn m hm u hu E hE

end AndersonAC.Blueprint
