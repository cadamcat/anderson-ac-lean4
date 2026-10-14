import AndersonAC.AgentS6Row.ConditionalRow

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

def meanConstant (K : ℝ) : ℝ := K + (K ^ 2 + K ^ 3 + 16 * K ^ 5)
def secondConstant (K : ℝ) : ℝ := K + K ^ 2 + 96 * K ^ 4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

def trialCoefficient (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) : ℂ :=
  hc t (r ω (q.pivot k ω)) ((q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)) (q.residual k ω)

set_option maxHeartbeats 1200000 in
lemma trial_coefficient_moments (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (K c Cloc : ℝ) (hK : 0 ≤ K)
    (hs : Small t K) (hsθ : Real.sqrt t ≤ t ^ betaW)
    (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ)
    (hlocal : TrialLocalInput q μ d c K Cloc dist collapsed ell)
    (hr : ∀ ω, BroadBounds c K (r ω))
    (hloc : ∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2)
    (hpre : ∀ k ω, k < q.stop ω → HeatPrestate t K
      (fun j : (q.state k ω).active => r ω j) (trialInverse t (r ω) (q.state k ω)))
    (k : ℕ) (E : Set Ω) (hE : MeasurableSet[q.history k] E)
    (hrun : ∀ ω ∈ E, k < q.stop ω) :
    Measurable (E.indicator (trialCoefficient q k)) ∧
      (∀ ω, ‖E.indicator (trialCoefficient q k) ω‖ ≤ 4 * K) ∧
      (∀ᵐ ω ∂μ,
        ‖μ[E.indicator (trialCoefficient q k) | q.history k] ω‖ ≤ meanConstant K * Real.sqrt t * t ^ betaW ∧
        |μ[(fun ω => ‖E.indicator (trialCoefficient q k) ω‖ ^ 2) | q.history k] ω -
          E.indicator (fun _ => (1 : ℝ)) ω| ≤ secondConstant K * Real.sqrt t) := by
  classical
  have ht : 0 < t := hs.pos
  let F := q.history
  have hm : F k ≤ mΩ := F.le k
  have hEm : MeasurableSet E := hm _ hE
  let ρ : Ω → ℂ := fun ω => r ω (q.pivot k ω)
  let γ : Ω → ℂ := fun ω => (q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)
  let ξ := q.residual k
  have hrj : ∀ j : Fin n, StronglyMeasurable[F k] (fun ω => r ω j) := fun j =>
    (continuous_apply j).comp_stronglyMeasurable
      (q.damping_adapted.mono (q.history.mono (Nat.zero_le k)))
  have hρm : StronglyMeasurable[F k] ρ := stronglyMeasurable_fin_select (q.pivot k)
    (q.pivot_predictable k) (fun j ω => r ω j) hrj
  have hγm : StronglyMeasurable[F k] γ := stronglyMeasurable_fin_select (q.pivot k)
    (q.pivot_predictable k) (fun j ω => (q.state k ω).hatG j j) (fun j => q.entries_adapted k j j)
  have hξm : Measurable ξ := ((q.residual_revealed k).mono (q.history.le (k + 1))).measurable
  have hρb : ∀ ω ∈ E, ‖ρ ω‖ ≤ K := fun ω _ => (hr ω).2 _ |>.1
  have hγb : ∀ ω ∈ E, ‖γ ω‖ ≤ K := by
    intro ω hω
    have hk := hrun ω hω
    obtain ⟨hx, _, _, _, _, _⟩ := q.heat k ω hk
    have hg := AndersonAC.AgentS6.hatG_eq_trialInverse q k ω hk.le ⟨_, hx⟩ ⟨_, hx⟩
    have hp := (hpre k ω hk).1 ⟨_, hx⟩
    dsimp [γ]
    rw [hg]
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans hp
  have hlag : ∀ ω ∈ E, ‖γ ω - ρ ω‖ ≤ K * t ^ betaW := by
    intro ω hω
    have hk := hrun ω hω
    obtain ⟨hx, _, _, _, _, _⟩ := q.heat k ω hk
    dsimp [γ, ρ]
    rw [AndersonAC.AgentS6.hatG_eq_trialInverse q k ω hk.le ⟨_, hx⟩ ⟨_, hx⟩]
    exact (hpre k ω hk).2.1 ⟨_, hx⟩
  have hξb : ∀ ω ∈ E, |ξ ω| ≤ K * Real.sqrt t := fun ω hω =>
    hlocal.residual_bound k ω (hrun ω hω) (hloc k ω (hrun ω hω))
  have hξI : Integrable ξ μ := hlocal.residual_integrable k
  have hξ2I : Integrable (fun ω => ξ ω ^ 2) μ := hlocal.residual_square_integrable k
  have hmeanE : ∀ᵐ ω ∂μ, ω ∈ E → μ[ξ | F k] ω = 0 := by
    filter_upwards [hlocal.residual_mean k] with ω hω hEω
    exact hω (hrun ω hEω) (hloc k ω (hrun ω hEω))
  obtain ⟨η, _, hη⟩ := hlocal.residual_variance k
  have hηb : ∀ᵐ ω ∂μ, ω ∈ E → |η ω| ≤ K * t ^ 2 ∧
      μ[(fun ω => ξ ω ^ 2) | F k] ω = t - η ω := by
    filter_upwards [hη] with ω hω hEω
    obtain ⟨hη0, hη1, hsec⟩ := hω (hrun ω hEω) (hloc k ω (hrun ω hEω))
    have he : η ω = (η ω / t) * t := by field_simp [hs.pos.ne']
    have hnon : 0 ≤ η ω := by rw [he]; exact mul_nonneg hη0 hs.pos.le
    have hup : η ω ≤ K * t ^ 2 := by
      calc
        η ω = (η ω / t) * t := he
        _ ≤ (K * t) * t := mul_le_mul_of_nonneg_right hη1 hs.pos.le
        _ = _ := by ring
    exact ⟨by rw [abs_of_nonneg hnon]; exact hup, hsec⟩
  let η' : Ω → ℝ := fun ω => if |η ω| ≤ K * t ^ 2 then η ω else 0
  have hη'b : ∀ ω ∈ E, |η' ω| ≤ K * t ^ 2 := by
    intro ω _
    by_cases h : |η ω| ≤ K * t ^ 2
    · simpa [η', h] using h
    · simp only [η', if_neg h, abs_zero]
      positivity
  have hsecE : ∀ᵐ ω ∂μ, ω ∈ E → μ[(fun ω => ξ ω ^ 2) | F k] ω = t - η' ω := by
    filter_upwards [hηb] with ω hω hEω
    simp only [η', if_pos (hω hEω).1]
    exact (hω hEω).2
  have hcmean := AndersonAC.AgentS6.condExp_heatCoeff_mean μ F k hE hs hρm hγm hξm
    hρb hγb hξb hξI hξ2I hmeanE hsecE hη'b
  have hcsecond := condExp_heatCoeff_second μ F k hE hs hρm hγm hξm
    hρb hγb hξb hξI hξ2I hmeanE hsecE (Filter.Eventually.of_forall hη'b)
  let z := E.indicator (trialCoefficient q k)
  have hzm : Measurable z := by
    have hρ : Measurable ρ := (hρm.mono hm).measurable
    have hγ : Measurable γ := (hγm.mono hm).measurable
    have ha : Measurable (fun ω => (ξ ω : ℂ) + (t : ℂ) * ρ ω) :=
      (Complex.measurable_ofReal.comp hξm).add (measurable_const.mul hρ)
    have hc : Measurable (fun ω => hc t (ρ ω) (γ ω) (ξ ω)) :=
      ha.neg.div (measurable_const.mul (measurable_const.add (ha.mul hγ)))
    exact hc.indicator hEm
  have hzb : ∀ ω, ‖z ω‖ ≤ 4 * K := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [show z ω = hc t (ρ ω) (γ ω) (ξ ω) from by simp [z, trialCoefficient, ρ, γ, ξ, hω]]
      exact norm_hc_le hs (hρb ω hω) (hγb ω hω) (hξb ω hω)
    · simp only [z, Set.indicator_of_notMem hω, norm_zero]
      positivity
  have hzI : Integrable z μ := Integrable.of_bound hzm.aestronglyMeasurable (4 * K)
    (Filter.Eventually.of_forall hzb)
  have hz2I : Integrable (fun ω => ‖z ω‖ ^ 2) μ := Integrable.of_bound
    (hzm.norm.pow_const 2).aestronglyMeasurable ((4 * K) ^ 2) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hzb ω) 2)
  have hzoff := condExp_supported hm E hE z hzI (fun ω hω => Set.indicator_of_notMem hω _)
  have hz2off := condExp_supported hm E hE (fun ω => ‖z ω‖ ^ 2) hz2I
    (fun ω hω => by simp [z, hω])
  have hsqeq : (fun ω => ‖z ω‖ ^ 2) = E.indicator (fun ω => ‖hc t (ρ ω) (γ ω) (ξ ω)‖ ^ 2) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [z, trialCoefficient, ρ, γ, ξ, hω]
  rw [← hsqeq] at hcsecond
  refine ⟨hzm, hzb, ?_⟩
  filter_upwards [hcmean, hcsecond, hzoff, hz2off] with ω hmω hsω hoω ho2ω
  by_cases hω : ω ∈ E
  · refine ⟨?_, ?_⟩
    swap
    · simpa only [z, F, secondConstant, Set.indicator_of_mem hω] using hsω hω
    have hb := hmω hω
    have hd := hlag ω hω
    have htn : t ≤ Real.sqrt t * t ^ betaW := by
      calc
        t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt hs.pos.le).symm
        _ ≤ Real.sqrt t * t ^ betaW := mul_le_mul_of_nonneg_left hsθ (Real.sqrt_nonneg t)
    have hroot : ‖(Real.sqrt t : ℂ) * (γ ω - ρ ω)‖ ≤ Real.sqrt t * (K * t ^ betaW) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
      exact mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg t)
    calc
      ‖μ[z | F k] ω‖ = ‖(μ[z | F k] ω - (Real.sqrt t : ℂ) * (γ ω - ρ ω)) +
          (Real.sqrt t : ℂ) * (γ ω - ρ ω)‖ := by congr 1; ring
      _ ≤ ‖μ[z | F k] ω - (Real.sqrt t : ℂ) * (γ ω - ρ ω)‖ +
          ‖(Real.sqrt t : ℂ) * (γ ω - ρ ω)‖ := norm_add_le _ _
      _ ≤ (K ^ 2 + K ^ 3 + 16 * K ^ 5) * t + Real.sqrt t * (K * t ^ betaW) := add_le_add hb hroot
      _ ≤ meanConstant K * Real.sqrt t * t ^ betaW := by
        have hh := mul_le_mul_of_nonneg_left htn
          (show 0 ≤ K ^ 2 + K ^ 3 + 16 * K ^ 5 by positivity)
        unfold meanConstant
        nlinarith
  · rw [hoω hω, ho2ω hω, Set.indicator_of_notMem hω]
    simp only [norm_zero, sub_self, abs_zero]
    constructor
    · unfold meanConstant; positivity
    · unfold secondConstant; positivity

end AndersonAC.AgentS6Row
