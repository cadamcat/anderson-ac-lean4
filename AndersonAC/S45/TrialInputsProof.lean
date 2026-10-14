import AndersonAC.S45.OneTrialProof
import Mathlib.NumberTheory.Harmonic.Bounds
import AndersonAC.S45.HelperStatements2
import AndersonAC.S45.SmallFactsProof

/-! `AndersonAC.S45.ordered_trial_inputs`: per-step ordered bounds with the
harmonic `1/(M-k)` profile give the stopped concentration inputs of one trial.
The centering identity is taken as the hypothesis `ConditionalCenteringFixed`
(corrected form of `AndersonAC.S45.conditional_centering`, helper module); `harmonic_slots` is. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

/-- `Aᴴ - A` as a continuous real-linear map. -/
def antiHerm {n : Type*} [Fintype n] [DecidableEq n] : Matrix n n ℂ →L[ℝ] Matrix n n ℂ where
  toFun A := Aᴴ - A
  map_add' A B := by rw [conjTranspose_add]; abel
  map_smul' c A := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
      mul_sub]
  cont := (continuous_id.matrix_conjTranspose).sub continuous_id

theorem condExp_hermitian {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {n : Type*} [Fintype n] [DecidableEq n] {X : Ω → Matrix n n ℂ}
    (hX : Integrable X μ) (hh : ∀ᵐ ω ∂μ, (X ω).IsHermitian) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).IsHermitian := by
  have h1 := (antiHerm (n := n)).comp_condExp_comm (m := m) hX
  have h2 : (⇑antiHerm ∘ X) =ᵐ[μ] 0 := by
    filter_upwards [hh] with ω hω
    show (X ω)ᴴ - X ω = 0
    rw [hω.eq, sub_self]
  have h3 := condExp_congr_ae (m := m) h2
  rw [condExp_zero] at h3
  filter_upwards [h1, h3] with ω e1 e3
  have : (μ[X | m] ω)ᴴ - μ[X | m] ω = 0 := by
    have := e1.trans e3
    simpa [antiHerm] using this
  exact sub_eq_zero.1 this

theorem logFactor_pos {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 0 < logFactor t :=
  lt_of_lt_of_le one_pos (logFactor_ge_one ht ht1)

theorem monitor_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k : MonitorKind) :
    0 ≤ monitorJump t k ∧ 0 ≤ monitorVariance t k ∧ 0 ≤ monitorBias t k := by
  have hL := (logFactor_pos ht ht1).le
  have hp : ∀ e, 0 ≤ power t e := fun e => (Real.rpow_pos_of_pos ht e).le
  cases k <;> simp only [monitorJump, monitorVariance, monitorBias] <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    first
    | positivity
    | exact mul_nonneg hL (hp _)
    | exact mul_nonneg (pow_nonneg hL _) (hp _)
    | exact add_nonneg (mul_nonneg (pow_nonneg hL _) (add_nonneg (hp _) (Real.sqrt_nonneg _)))
        (mul_nonneg (pow_nonneg hL _) (hp _))
    | exact hp _

/-- `(1 + log M)/logFactor t ≤ 1 + log C + 6d` from `M ≤ C t^{-6d}`. -/
theorem log_count {d M : ℕ} {C t : ℝ} (hC : 1 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1) (hM : 0 < M)
    (hMb : (M : ℝ) ≤ C * power t (-6 * (d : ℝ))) :
    1 + Real.log M ≤ (1 + Real.log C + 6 * d) * logFactor t := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogt : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hpw : Real.log (power t (-6 * (d : ℝ))) = 6 * d * Real.log (1 / t) := by
    rw [power_def, Real.log_rpow ht, one_div, Real.log_inv]; ring
  have h1 : Real.log M ≤ Real.log C + 6 * d * Real.log (1 / t) := by
    have := Real.log_le_log hMpos hMb
    have hp : 0 < power t (-6 * (d : ℝ)) := Real.rpow_pos_of_pos ht _
    rw [Real.log_mul (by linarith) (ne_of_gt hp), hpw] at this
    exact this
  unfold logFactor
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_nonneg hlogC hlogt, mul_nonneg hd hlogt]

/-- The harmonic profile: `∑_{k<n} [k<M] a/(M-k) ≤ a (1 + log M)`. -/
theorem profile_sum {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (∑ k ∈ Finset.range n, (if k < M then a / ((M - k : ℕ) : ℝ) else 0)) ≤
      a * (1 + Real.log M) := by
  have hnn : ∀ k, 0 ≤ a / ((M - k : ℕ) : ℝ) := fun k => div_nonneg ha (Nat.cast_nonneg _)
  calc (∑ k ∈ Finset.range n, (if k < M then a / ((M - k : ℕ) : ℝ) else 0))
      = ∑ k ∈ (Finset.range n).filter (· < M), a / ((M - k : ℕ) : ℝ) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.range M, a / ((M - k : ℕ) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
          exact hk.2
        · intro k _ _; exact hnn k
    _ = a * ∑ k ∈ Finset.range M, (1 : ℝ) / ((M - k : ℕ) : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ a * (1 + Real.log M) := mul_le_mul_of_nonneg_left (harmonic_slots_proof M hM) ha

theorem ordered_trial_inputs_of (hcent : ConditionalCenteringFixed) :
    ∀ (d : ℕ) (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (s M : ℕ) (t : ℝ) (a : OrderedRawBounds μ ℱ s M t C),
    0 < t → t < t0 → 0 < M → (M : ℝ) ≤ C * power t (-6 * (d : ℝ)) →
    (∑ i, (a.dimension i : ℝ)) ≤ C * power t (-6 * (d : ℝ)) →
    ∃ b : TrialInputs μ ℱ s d t C', b.kind = a.kind ∧ b.dimension = a.dimension ∧
      (∀ i k ω, HEq (b.raw i k ω) (a.raw i k ω)) := by
  intro d C hC
  have hC0 : 0 < C := by linarith
  set G : ℝ := 1 + Real.log C + 6 * d with hGdef
  have hG : 1 ≤ G := by
    have := Real.log_nonneg hC
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hGdef]; linarith
  refine ⟨2 * C * G, by positivity, 1, one_pos, ?_⟩
  intro Ω mΩ μ _ ℱ s M t a ht ht1 hM hMb hdim
  have ht1' : t ≤ 1 := ht1.le
  have hL := logFactor_pos ht ht1'
  have hlogM := log_count hC ht ht1' hM hMb
  -- the envelope
  let env : Fin s → ℕ → ℝ := fun i k =>
    if k < M then C * monitorVariance t (a.kind i) / logFactor t / ((M - k : ℕ) : ℝ) else 0
  have henv_nn : ∀ i k, 0 ≤ env i k := by
    intro i k
    simp only [env]
    split_ifs
    · have := (monitor_nonneg ht ht1' (a.kind i)).2.1
      positivity
    · exact le_rfl
  -- harmonic totals
  have htot : ∀ (x : ℝ), 0 ≤ x → ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (if k < M then C * x / logFactor t / ((M - k : ℕ) : ℝ) else 0)) ≤
        2 * C * G * x := by
    intro x hx n
    have h := profile_sum hM (a := C * x / logFactor t) (by positivity) n
    refine h.trans ?_
    have : C * x / logFactor t * (1 + Real.log M) ≤ C * x / logFactor t * (G * logFactor t) :=
      mul_le_mul_of_nonneg_left hlogM (by positivity)
    have e : C * x / logFactor t * (G * logFactor t) = C * G * x := by
      field_simp
    nlinarith [mul_nonneg (mul_nonneg hC0.le (by linarith : (0 : ℝ) ≤ G)) hx]
  -- raw facts
  have hint : ∀ i k, Integrable (a.raw i (k + 1)) μ := fun i k =>
    Integrable.of_bound (a.measurable i (k + 1)) _ (a.jump i k)
  have hcen : ∀ i k, centered μ ℱ (a.raw i) (k + 1) =
      fun ω => a.raw i (k + 1) ω - μ[a.raw i (k + 1) | ℱ k] ω := by
    intro i k; funext ω; simp [centered]
  have hcen0 : ∀ i, centered μ ℱ (a.raw i) 0 = fun _ => 0 := by
    intro i; funext ω; simp [centered]
  have hzero : ∀ i k, M ≤ k → a.raw i (k + 1) = 0 := fun i k hk =>
    funext fun ω => a.finite_horizon i k hk ω
  have hJnn : ∀ i, 0 ≤ C * monitorJump t (a.kind i) := fun i =>
    mul_nonneg hC0.le (monitor_nonneg ht ht1' (a.kind i)).1
  have hcentering := fun i k => hcent Ω (Fin (a.dimension i)) (Fin (a.dimension i)) (ℱ k) μ
    (ℱ.le k) (a.raw i (k + 1)) (C * monitorJump t (a.kind i)) (a.measurable i (k + 1))
    (hJnn i) (a.jump i k)
  have hbherm : ∀ i k, ∀ᵐ ω ∂μ, (μ[a.raw i (k + 1) | ℱ k] ω).IsHermitian := fun i k =>
    condExp_hermitian (hint i k) (a.hermitian i k)
  refine ⟨{
      kind := a.kind
      dimension := a.dimension
      raw := a.raw
      envelope := fun i k _ => env i k
      differences := fun i => ?_
      drift := fun i N => ?_
      dimensions := ?_ }, rfl, rfl, fun i k ω => HEq.rfl⟩
  · -- the martingale-difference hypotheses
    refine
      { adapted := fun k => ?_
        integrable := fun k => ?_
        square_integrable := fun k => ?_
        hermitian := fun k => ?_
        centered := fun k => ?_
        jump := fun k => ?_
        predictable := fun k => stronglyMeasurable_const
        variance_nonneg := fun k => ae_of_all _ fun _ => henv_nn i k
        variance := fun k => ?_
        total_variance := fun n => ae_of_all _ fun _ => ?_ }
    · cases k with
      | zero => rw [hcen0]; exact stronglyMeasurable_const
      | succ k =>
        rw [hcen]
        exact (a.adapted i (k + 1)).sub
          (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ k)))
    · cases k with
      | zero => rw [hcen0]; exact integrable_const _
      | succ k => rw [hcen]; exact (hint i k).sub integrable_condExp
    · have hbd : ∀ k, ∀ᵐ ω ∂μ, ‖centered μ ℱ (a.raw i) k ω‖ ≤ 2 * (C * monitorJump t (a.kind i)) := by
        intro k
        cases k with
        | zero =>
          rw [hcen0]
          exact ae_of_all _ fun _ => by
            show ‖(0 : CMat (Fin (a.dimension i)))‖ ≤ _
            rw [norm_zero]; exact mul_nonneg zero_le_two (hJnn i)
        | succ k => rw [hcen]; exact (hcentering i k).1
      have hsm : AEStronglyMeasurable (centered μ ℱ (a.raw i) k) μ := by
        cases k with
        | zero => rw [hcen0]; exact aestronglyMeasurable_const
        | succ k => rw [hcen]; exact (hint i k).1.sub integrable_condExp.1
      refine Integrable.of_bound (hsm.pow 2) ((2 * (C * monitorJump t (a.kind i))) ^ 2) ?_
      filter_upwards [hbd k] with ω hω
      have hsq : ‖(centered μ ℱ (a.raw i) k ω) ^ 2‖ ≤ ‖centered μ ℱ (a.raw i) k ω‖ ^ 2 := by
        rw [pow_two, pow_two]; exact norm_mul_le _ _
      exact hsq.trans (pow_le_pow_left₀ (norm_nonneg _) hω 2)
    · rw [hcen]
      filter_upwards [a.hermitian i k, hbherm i k] with ω h1 h2
      exact h1.sub h2
    · rw [hcen]
      have h1 := condExp_sub (m := ℱ k) (hint i k) (integrable_condExp (m := ℱ k)
        (f := a.raw i (k + 1)))
      have h2 : μ[μ[a.raw i (k + 1) | ℱ k] | ℱ k] = μ[a.raw i (k + 1) | ℱ k] :=
        condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp
      filter_upwards [h1] with ω hω
      rw [show (fun ω => a.raw i (k + 1) ω - μ[a.raw i (k + 1) | ℱ k] ω) =
        a.raw i (k + 1) - μ[a.raw i (k + 1) | ℱ k] from rfl, hω, h2]
      simp
    · rw [hcen]
      filter_upwards [(hcentering i k).1] with ω hω
      refine hω.trans ?_
      have hJ := (monitor_nonneg ht ht1' (a.kind i)).1
      have : 2 * (C * monitorJump t (a.kind i)) ≤ 2 * C * G * monitorJump t (a.kind i) := by
        nlinarith [mul_nonneg hC0.le hJ]
      exact this
    · -- variance
      by_cases hk : k < M
      · rw [hcen]
        obtain ⟨-, h2, -⟩ := hcentering i k
        have hYsq : (fun ω => (a.raw i (k + 1) ω - μ[a.raw i (k + 1) | ℱ k] ω) ^ 2) =ᵐ[μ]
            fun ω => (a.raw i (k + 1) ω - μ[a.raw i (k + 1) | ℱ k] ω) *
              (a.raw i (k + 1) ω - μ[a.raw i (k + 1) | ℱ k] ω)ᴴ := by
          filter_upwards [a.hermitian i k, hbherm i k] with ω h1 h2
          rw [pow_two, (h1.sub h2).eq]
        have hBsq : (fun ω => (a.raw i (k + 1) ω) ^ 2) =ᵐ[μ]
            fun ω => a.raw i (k + 1) ω * (a.raw i (k + 1) ω)ᴴ := by
          filter_upwards [a.hermitian i k] with ω h1
          rw [pow_two, h1.eq]
        filter_upwards [condExp_congr_ae (m := ℱ k) hYsq, condExp_congr_ae (m := ℱ k) hBsq, h2,
          a.square i k hk, hbherm i k] with ω e1 e2 e3 e4 e5
        rw [e1, e3, ← e2]
        rw [Matrix.le_iff] at e4 ⊢
        have hpsd : (μ[a.raw i (k + 1) | ℱ k] ω * (μ[a.raw i (k + 1) | ℱ k] ω)ᴴ).PosSemidef :=
          Matrix.posSemidef_self_mul_conjTranspose _
        have : env i k • (1 : CMat (Fin (a.dimension i))) -
            (μ[fun ω => a.raw i (k + 1) ω ^ 2 | ℱ k] ω -
              μ[a.raw i (k + 1) | ℱ k] ω * (μ[a.raw i (k + 1) | ℱ k] ω)ᴴ) =
            ((C * monitorVariance t (a.kind i) / logFactor t / ((M - k : ℕ) : ℝ)) •
              (1 : CMat (Fin (a.dimension i))) - μ[fun ω => a.raw i (k + 1) ω ^ 2 | ℱ k] ω) +
            μ[a.raw i (k + 1) | ℱ k] ω * (μ[a.raw i (k + 1) | ℱ k] ω)ᴴ := by
          simp only [env, if_pos hk]; abel
        rw [this]
        exact e4.add hpsd
      · push_neg at hk
        have hz := hzero i k hk
        have hc : centered μ ℱ (a.raw i) (k + 1) = fun _ => 0 := by
          rw [hcen, hz]; funext ω; simp [condExp_zero]
        rw [hc]
        have : (fun _ : Ω => (0 : CMat (Fin (a.dimension i))) ^ 2) = 0 := by
          funext ω; simp
        rw [this, condExp_zero]
        refine ae_of_all _ fun ω => ?_
        simp only [env, if_neg (not_lt.2 hk), zero_smul, Pi.zero_apply]
        exact le_rfl
    · exact htot _ (monitor_nonneg ht ht1' (a.kind i)).2.1 n
  · -- drift
    have hb : ∀ k, ∀ᵐ ω ∂μ, ‖μ[a.raw i (k + 1) | ℱ k] ω‖ ≤
        (if k < M then C * monitorBias t (a.kind i) / logFactor t / ((M - k : ℕ) : ℝ) else 0) := by
      intro k
      by_cases hk : k < M
      · simp only [if_pos hk]
        exact a.mean i k hk
      · simp only [if_neg hk]
        rw [hzero i k (not_lt.1 hk), condExp_zero]
        exact ae_of_all _ fun ω => by simp
    filter_upwards [ae_all_iff.2 hb] with ω hω
    calc ‖∑ k ∈ Finset.range N, μ[a.raw i (k + 1) | ℱ k] ω‖
        ≤ ∑ k ∈ Finset.range N, ‖μ[a.raw i (k + 1) | ℱ k] ω‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N,
          (if k < M then C * monitorBias t (a.kind i) / logFactor t / ((M - k : ℕ) : ℝ)
            else 0) := Finset.sum_le_sum fun k _ => hω k
      _ ≤ 2 * C * G * monitorBias t (a.kind i) :=
          htot _ (monitor_nonneg ht ht1' (a.kind i)).2.2 N
  · -- dimensions
    refine hdim.trans ?_
    have hp : 0 ≤ power t (-6 * (d : ℝ)) := (Real.rpow_pos_of_pos ht _).le
    have : C ≤ 2 * C * G := by nlinarith
    exact mul_le_mul_of_nonneg_right this hp

end AndersonAC.AgentS45
