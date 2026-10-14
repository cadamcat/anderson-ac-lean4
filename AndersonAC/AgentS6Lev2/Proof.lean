import AndersonAC.AgentS6.Frozen
import AndersonAC.L64.LeverageDrift
import AndersonAC.S6.Range
import AndersonAC.AgentS6.LeverageFacts
import AndersonAC.AgentS6.TrialStep
import AndersonAC.AgentS6.RunningPrestate
import AndersonAC.AgentS6.TrialLocation

noncomputable section

open Filter MeasureTheory ProbabilityTheory Topology
open AndersonAC.S6
open scoped ComplexOrder


namespace AndersonAC.AgentS6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem condExp_eq_condDistrib_id (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (Y : Ω → ℝ) (hF : F ≤ mΩ)
    (hY : Integrable Y μ) :
    μ[Y | F] =ᵐ[μ] fun ω =>
      ∫ y, y ∂ProbabilityTheory.condDistrib Y (id : Ω → Ω) μ ω := by
  have hid : @Measurable Ω Ω mΩ F (id : Ω → Ω) := by
    exact @Measurable.of_comap_le Ω Ω mΩ F (id : Ω → Ω) <| by
      simpa [MeasurableSpace.comap_id] using hF
  have h := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    (μ := μ) (X := (id : Ω → Ω)) (Y := Y) (mβ := F) hid hY.1.aemeasurable
    stronglyMeasurable_id hY
  simpa [MeasurableSpace.comap_id] using h

theorem condExp_sq_eq_condDistrib_id (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (Y : Ω → ℝ) (hF : F ≤ mΩ)
    (hY : AEMeasurable Y μ) (hY2 : Integrable (fun ω => (Y ω) ^ 2) μ) :
    μ[(fun ω => (Y ω) ^ 2) | F] =ᵐ[μ] fun ω =>
      ∫ y, y ^ 2 ∂ProbabilityTheory.condDistrib Y (id : Ω → Ω) μ ω := by
  have hid : @Measurable Ω Ω mΩ F (id : Ω → Ω) := by
    exact @Measurable.of_comap_le Ω Ω mΩ F (id : Ω → Ω) <| by
      simpa [MeasurableSpace.comap_id] using hF
  have h := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    (μ := μ) (X := (id : Ω → Ω)) (Y := Y) (mβ := F) hid hY
    (continuous_id.pow 2).stronglyMeasurable hY2
  simpa [MeasurableSpace.comap_id] using h

theorem condExp_comp_eq_condDistrib_id (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (Y : Ω → ℝ) (f : ℝ → ℝ) (hF : F ≤ mΩ)
    (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω => f (Y ω)) μ) :
    μ[(fun ω => f (Y ω)) | F] =ᵐ[μ] fun ω =>
      ∫ y, f y ∂ProbabilityTheory.condDistrib Y (id : Ω → Ω) μ ω := by
  have hid : @Measurable Ω Ω mΩ F (id : Ω → Ω) := by
    exact @Measurable.of_comap_le Ω Ω mΩ F (id : Ω → Ω) <| by
      simpa [MeasurableSpace.comap_id] using hF
  have h := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    (μ := μ) (X := (id : Ω → Ω)) (Y := Y) (mβ := F) hid hY hf hint
  simpa [MeasurableSpace.comap_id] using h

theorem condDistrib_bound_on_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : MeasurableSpace Ω) (Y : Ω → ℝ) (run : Set Ω) (hF : F ≤ mΩ)
    (hRun : MeasurableSet[F] run)
    (hY : @Measurable Ω ℝ mΩ (borel ℝ) Y) (B : ℝ)
    (hbound : ∀ ω, ω ∈ run → |Y ω| ≤ B) :
    ∀ᵐ ω ∂μ, ω ∈ run → ∀ᵐ y ∂ProbabilityTheory.condDistrib Y (id : Ω → Ω) μ ω,
      |y| ≤ B := by
  classical
  let bad : Set ℝ := {y | B < |y|}
  let f : ℝ → ℝ := bad.indicator (fun _ => (1 : ℝ))
  have hbad : MeasurableSet bad := by
    exact measurableSet_lt measurable_const continuous_abs.measurable
  have hYbad : @MeasurableSet Ω mΩ (Y ⁻¹' bad) := hY hbad
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hbad
  have hInt : Integrable (fun ω => f (Y ω)) μ := by
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const (1 : ℝ)
    have hi := hconst.indicator hYbad
    convert hi using 1
    funext ω
    simp [f, bad, Set.indicator]
  have hzero : run.indicator (fun ω => f (Y ω)) = 0 := by
    funext ω
    by_cases hω : ω ∈ run
    · have hy := hbound ω hω
      have hnot : Y ω ∉ bad := by
        exact not_lt.mpr hy
      simp [Set.indicator_of_mem hω, f, hnot]
    · simp [Set.indicator_of_notMem hω]
  have hCEind := condExp_indicator hInt hRun
  have hleft : μ[run.indicator (fun ω => f (Y ω)) | F] =ᵐ[μ] 0 := by
    rw [hzero]
    simp
  have hCEzero : ∀ᵐ ω ∂μ, ω ∈ run → μ[fun ω => f (Y ω) | F] ω = 0 := by
    filter_upwards [hCEind, hleft] with ω h1 h2 hω
    have h3 := h1.symm.trans h2
    simpa [Set.indicator_of_mem hω] using h3
  have hid : @Measurable Ω Ω mΩ F (id : Ω → Ω) := by
    exact @Measurable.of_comap_le Ω Ω mΩ F (id : Ω → Ω) <| by
      simpa [MeasurableSpace.comap_id] using hF
  have hFormula := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    (μ := μ) (X := (id : Ω → Ω)) (Y := Y) (mβ := F) hid hY.aemeasurable hf hInt
  have hFormula' := by simpa [MeasurableSpace.comap_id] using hFormula
  filter_upwards [hCEzero, hFormula'] with ω hce hform hω
  let κ := ProbabilityTheory.condDistrib Y (id : Ω → Ω) μ ω
  haveI : IsProbabilityMeasure κ := by infer_instance
  have hIntMeasure : (∫ y, f y ∂κ) = κ.real bad := by
    simpa [f] using (MeasureTheory.integral_indicator_const (μ := κ) (1 : ℝ) hbad)
  have hreal : κ.real bad = 0 := by
    calc
      κ.real bad = ∫ y, f y ∂κ := hIntMeasure.symm
      _ = 0 := by
        calc
          (∫ y, f y ∂κ) = μ[fun ω => f (Y ω) | F] ω := hform.symm
          _ = 0 := hce hω
  have hbad0 : κ bad = 0 :=
    (MeasureTheory.measureReal_eq_zero_iff (μ := κ) (s := bad)).mp hreal
  have hgood : κ badᶜ = 1 := (MeasureTheory.prob_compl_eq_one_iff hbad).2 hbad0
  have hAE : ∀ᵐ y ∂κ, y ∈ badᶜ :=
    (MeasureTheory.mem_ae_iff_prob_eq_one hbad.compl).2 hgood
  simpa [bad, not_lt] using hAE

theorem condDistrib_moments_of_condExp (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (Y : Ω → ℝ) (run : Set Ω) (hF : F ≤ mΩ)
    (hY : Integrable Y μ) (hY2 : Integrable (fun ω => (Y ω) ^ 2) μ)
    (t : ℝ) (η : Ω → ℝ)
    (hmean : ∀ᵐ ω ∂μ, ω ∈ run → μ[Y | F] ω = 0)
    (hsecond : ∀ᵐ ω ∂μ, ω ∈ run → μ[(fun ω => (Y ω) ^ 2) | F] ω = t - η ω) :
    ∀ᵐ ω ∂μ, ω ∈ run →
      (∫ y, y ∂ProbabilityTheory.condDistrib Y (id : Ω → Ω) μ ω) = 0 ∧
        (∫ y, y ^ 2 ∂ProbabilityTheory.condDistrib Y (id : Ω → Ω) μ ω) = t - η ω := by
  letI : MeasurableSpace Ω := mΩ
  have hMean := condExp_eq_condDistrib_id (μ := μ) (F := F) (Y := Y) hF hY
  have hSquare := condExp_sq_eq_condDistrib_id (μ := μ) (F := F) (Y := Y) hF
    hY.1.aemeasurable hY2
  filter_upwards [hMean, hSquare, hmean, hsecond] with ω hm hs hmeanω hsecondω hrun
  exact ⟨hm.symm.trans (hmeanω hrun), hs.symm.trans (hsecondω hrun)⟩

def zeroExtendRows {R B : Type*} (A : Finset R) [DecidablePred (· ∈ A)]
    (D : Matrix {i // i ∈ A} B ℂ) : Matrix R B ℂ := fun i j =>
  if hi : i ∈ A then D ⟨i, hi⟩ j else 0

theorem conjTranspose_mul_zeroExtendRows {R B : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] (A : Finset R) (D : Matrix {i // i ∈ A} B ℂ) :
    Matrix.conjTranspose (zeroExtendRows A D) * zeroExtendRows A D =
      Matrix.conjTranspose D * D := by
  classical
  ext b c
  change (∑ i : R, star (zeroExtendRows A D i b) * zeroExtendRows A D i c) =
    ∑ i : {i // i ∈ A}, star (D i b) * D i c
  let f : R → ℂ := fun i => if hi : i ∈ A then star (D ⟨i, hi⟩ b) * D ⟨i, hi⟩ c else 0
  have hterm (i : R) : star (zeroExtendRows A D i b) * zeroExtendRows A D i c = f i := by
    by_cases hi : i ∈ A <;> simp [zeroExtendRows, f, hi]
  calc
    (∑ i : R, star (zeroExtendRows A D i b) * zeroExtendRows A D i c) = ∑ i : R, f i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = ∑ i : R, if hi : i ∈ A then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ A <;> simp [f, hi]
    _ = ∑ i ∈ A, f i := Finset.sum_ite_mem_eq A f
    _ = ∑ i : {i // i ∈ A}, f i := Finset.sum_subtype A (by intro i; rfl) f
    _ = ∑ i : {i // i ∈ A}, star (D i b) * D i c := by
      apply Finset.sum_congr rfl
      intro i _
      simp [f]

theorem trialInverse_eq_hatG_of_running {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω)
    (hk : k < q.stop ω) :
    ∀ i j : {i // i ∈ (q.state k ω).active},
      trialInverse t (r ω) (q.state k ω) i j = (q.state k ω).hatG i j := by
  cases k with
  | zero =>
      intro i j
      calc
        trialInverse t (r ω) (q.state 0 ω) i j = g0 ω i j := q.initial_inverse ω i j
        _ = (q.state 0 ω).hatG i j := by rw [q.start_entries ω]
  | succ k =>
      have hk' : k < q.stop ω := by omega
      obtain ⟨hx, hxcore, hactive, hden, hM, hhat⟩ := q.heat k ω hk'
      intro i j
      have h := hhat i j
      simp only [dif_pos i.property, dif_pos j.property] at h
      rw [h]
      ring

theorem heatPrestate_submatrix {n : ℕ} (A : Finset (Fin n)) (t K : ℝ)
    (r : Fin n → ℂ) (g h : Matrix (Fin n) (Fin n) ℂ)
    (hpre : HeatPrestate t K r g)
    (hh : ∀ i j, i ∈ A → j ∈ A → h i j = g i j) :
    HeatPrestate t K (fun i : {i // i ∈ A} => r i)
      (h.submatrix (fun i : {i // i ∈ A} => (i : Fin n))
        (fun i : {i // i ∈ A} => (i : Fin n))) := by
  classical
  rcases hpre with ⟨hdiag, hlag, hfour⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [hh i i i.property i.property] using hdiag i
  · intro i
    simpa [hh i i i.property i.property] using hlag i
  · intro i
    let f : Fin n → ℝ := fun j => ‖((Real.sqrt t : ℝ) : ℂ) * g i j‖ ^ 4
    have hsum : (∑ j : {j : Fin n // j ∈ A}, f j) ≤ ∑ j : Fin n, f j := by
      rw [← Finset.sum_subtype A (by intro j; rfl) f]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun j _ _ => by positivity)
    have hrow : fourthRow (scaledInverse t
        (h.submatrix (fun i : {i // i ∈ A} => (i : Fin n))
          (fun i : {i // i ∈ A} => (i : Fin n)))) i =
        ∑ j : {j : Fin n // j ∈ A}, f j := by
      simp only [fourthRow, scaledInverse, Matrix.submatrix_apply, Matrix.smul_apply,
        smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hh i j i.property j.property]
    have hfull : (∑ j : Fin n, f j) = fourthRow (scaledInverse t g) i := by
      simp [fourthRow, scaledInverse, f, Matrix.smul_apply, smul_eq_mul]
    rw [hrow]
    calc
      (∑ j : {j : Fin n // j ∈ A}, f j) ≤ ∑ j : Fin n, f j := hsum
      _ = fourthRow (scaledInverse t g) i := hfull
      _ ≤ fourthCap t := hfour i

theorem running_prestate_of_full {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (K : ℝ) (k : ℕ) (ω : Ω)
    (hk : k < q.stop ω)
    (hfull : HeatPrestate t K (r ω) (q.state k ω).hatG) :
    HeatPrestate t K (fun i : {i // i ∈ (q.state k ω).active} => r ω i)
      (trialInverse t (r ω) (q.state k ω)) := by
  have hsub := heatPrestate_submatrix (q.state k ω).active t K (r ω)
    (q.state k ω).hatG (q.state k ω).hatG hfull (by intro i j hi hj; rfl)
  have hEq : trialInverse t (r ω) (q.state k ω) =
      (q.state k ω).hatG.submatrix
        (fun i : {i // i ∈ (q.state k ω).active} => (i : Fin n))
        (fun i : {i // i ∈ (q.state k ω).active} => (i : Fin n)) := by
    ext i j
    exact trialInverse_eq_hatG_of_running q k ω hk i j
  rw [hEq]
  exact hsub

theorem running_prestate_of_budgetAt {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (c K : ℝ) (qlag : ℝ → ℝ)
    (hpreAt : ∀ (r0 : Fin n → ℂ) (g0' hg : Matrix (Fin n) (Fin n) ℂ),
      (∀ i, ‖r0 i‖ ≤ K) →
      (∀ i, fourthRow (scaledInverse t g0') i ≤ (4 / 5) * fourthCap t) →
      (∀ i, ‖g0' i i - r0 i‖ ≤ qlag t * t ^ betaW) →
      BudgetsHold t g0' hg → HeatPrestate t (3 * K + 1) r0 hg)
    (hBroad : ∀ ω, BroadBounds c K (r ω))
    (hstart : ∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t)
    (hlag : ∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW)
    (k : ℕ) (ω : Ω) (hk : k < q.stop ω) :
    HeatPrestate t (3 * K + 1)
      (fun i : {i // i ∈ (q.state k ω).active} => r ω i)
      (trialInverse t (r ω) (q.state k ω)) := by
  have hfull := hpreAt (r ω) (g0 ω) (q.state k ω).hatG
    (fun i => (hBroad ω).2 i |>.1) (hstart ω) (hlag ω)
    (q.running_budgets k ω hk)
  exact running_prestate_of_full q (3 * K + 1) k ω hk hfull

theorem sum_fourth_norm_add_le {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    (∑ i, ‖x i + y i‖ ^ 4) ≤
      (11 / 10) * (∑ i, ‖x i‖ ^ 4) + (101 : ℝ) ^ 4 * (∑ i, ‖y i‖ ^ 4) := by
  classical
  have hterm (i : ι) : ‖x i + y i‖ ^ 4 ≤
      (11 / 10) * ‖x i‖ ^ 4 + (101 : ℝ) ^ 4 * ‖y i‖ ^ 4 := by
    set a := ‖x i‖ with ha
    set b := ‖y i‖ with hb
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hnorm : ‖x i + y i‖ ^ 4 ≤ (a + b) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (by simpa [a, b] using norm_add_le (x i) (y i)) 4
    calc
      ‖x i + y i‖ ^ 4 ≤ (a + b) ^ 4 := hnorm
      _ ≤ (11 / 10) * a ^ 4 + (101 : ℝ) ^ 4 * b ^ 4 := by
        by_cases hsmall : b ≤ a / 100
        · have hab : a + b ≤ (101 / 100) * a := by nlinarith
          have hp := pow_le_pow_left₀ (add_nonneg ha0 hb0) hab 4
          have hc : (101 / 100 : ℝ) ^ 4 ≤ 11 / 10 := by norm_num
          have hca := mul_le_mul_of_nonneg_right hc (pow_nonneg ha0 4)
          have hiden : ((101 / 100 : ℝ) * a) ^ 4 = (101 / 100 : ℝ) ^ 4 * a ^ 4 := by ring
          rw [hiden] at hp
          calc
            (a + b) ^ 4 ≤ (101 / 100 : ℝ) ^ 4 * a ^ 4 := hp
            _ ≤ (11 / 10) * a ^ 4 := hca
            _ ≤ (11 / 10) * a ^ 4 + (101 : ℝ) ^ 4 * b ^ 4 :=
              le_add_of_nonneg_right (mul_nonneg (by norm_num) (pow_nonneg hb0 4))
        · have hab : a + b ≤ 101 * b := by have : a / 100 < b := lt_of_not_ge hsmall; nlinarith
          have hp := pow_le_pow_left₀ (add_nonneg ha0 hb0) hab 4
          have hiden : (101 * b) ^ 4 = (101 : ℝ) ^ 4 * b ^ 4 := by ring
          rw [hiden] at hp
          calc
            (a + b) ^ 4 ≤ (101 : ℝ) ^ 4 * b ^ 4 := hp
            _ ≤ (11 / 10) * a ^ 4 + (101 : ℝ) ^ 4 * b ^ 4 :=
              le_add_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg ha0 4))
  calc
    (∑ i, ‖x i + y i‖ ^ 4) ≤
        ∑ i, ((11 / 10) * ‖x i‖ ^ 4 + (101 : ℝ) ^ 4 * ‖y i‖ ^ 4) :=
          Finset.sum_le_sum fun i _ => hterm i
    _ = (11 / 10) * (∑ i, ‖x i‖ ^ 4) + (101 : ℝ) ^ 4 * (∑ i, ‖y i‖ ^ 4) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem prestate_from_budgets_proof (K : ℝ) (hK : 1 ≤ K) (qlag : ℝ → ℝ)
    (hqlag : Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    AndersonAC.S6.Planned.prestate_from_budgets K hK qlag hqlag := by
  classical
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hid : Tendsto id F (nhds (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have htpos : ∀ᶠ t in F, 0 < t := self_mem_nhdsWithin
  have ht1 : ∀ᶠ t in F, t ≤ 1 := by
    filter_upwards [hid.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht
    exact ht.le
  have hq1 : ∀ᶠ t in F, qlag t ≤ 1 := by
    filter_upwards [hqlag.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht
    exact ht.le
  have hpow : Tendsto (fun t : ℝ => t ^ (9 / 10000 : ℝ)) F (nhds 0) := by
    exact hid.rpow_const_nhds_zero (by norm_num)
  have hmargin : ∀ᶠ t in F, (101 : ℝ) ^ 4 * t ^ (9 / 10000 : ℝ) ≤ 3 / 25 := by
    have h := (tendsto_const_nhds.mul hpow).eventually
      (Iio_mem_nhds (by norm_num : (101 : ℝ) ^ 4 * 0 < (3 / 25 : ℝ)))
    filter_upwards [h] with t ht
    exact ht.le
  unfold AndersonAC.S6.Planned.prestate_from_budgets
  filter_upwards [htpos, ht1, hq1, hmargin] with t ht htone hq hε
  intro n r g0 hg hr hstart hlag hbud
  have htentry : AndersonAC.S6.entryBudget t ≤ t ^ AndersonAC.S6.betaW := by
    unfold AndersonAC.S6.entryBudget AndersonAC.S6.betaW AndersonAC.S6.delta
    exact Real.rpow_le_rpow_of_exponent_ge ht htone (by norm_num)
  have htentry1 : AndersonAC.S6.entryBudget t ≤ 1 := by
    unfold AndersonAC.S6.entryBudget AndersonAC.S6.delta
    exact Real.rpow_le_one ht.le htone (by norm_num)
  have htbeta1 : t ^ AndersonAC.S6.betaW ≤ 1 := by
    exact Real.rpow_le_one ht.le htone (by unfold AndersonAC.S6.betaW AndersonAC.S6.delta; positivity)
  have hqt : qlag t * t ^ AndersonAC.S6.betaW ≤ 1 := by
    have hβ : 0 ≤ t ^ AndersonAC.S6.betaW := Real.rpow_nonneg ht.le _
    have h := mul_le_mul hq htbeta1 hβ (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hbudget_entries : ∀ i j, ‖hg i j - g0 i j‖ ≤ AndersonAC.S6.entryBudget t := hbud.1
  have hbudget_rows : ∀ i, AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t (hg - g0)) i ≤
      AndersonAC.S6.rowBudget t := hbud.2.1
  have hpre_diag : ∀ i, ‖hg i i‖ + ‖r i‖ ≤ 3 * K + 1 := by
    intro i
    have hdiff := hlag i
    have hstart' := hstart i
    have hnorm0 : ‖g0 i i‖ ≤ ‖r i‖ + qlag t * t ^ AndersonAC.S6.betaW := by
      have hrepr : g0 i i = (g0 i i - r i) + r i := by ring
      rw [hrepr]
      calc
        ‖(g0 i i - r i) + r i‖ ≤ ‖g0 i i - r i‖ + ‖r i‖ := norm_add_le _ _
        _ ≤ qlag t * t ^ AndersonAC.S6.betaW + ‖r i‖ := by
          nlinarith [hdiff]
        _ = ‖r i‖ + qlag t * t ^ AndersonAC.S6.betaW := by ring
    have hnormg : ‖hg i i‖ ≤ ‖g0 i i‖ + AndersonAC.S6.entryBudget t := by
      have hrepr : hg i i = g0 i i + (hg i i - g0 i i) := by ring
      rw [hrepr]
      calc
        ‖g0 i i + (hg i i - g0 i i)‖ ≤ ‖g0 i i‖ + ‖hg i i - g0 i i‖ := norm_add_le _ _
        _ ≤ ‖g0 i i‖ + AndersonAC.S6.entryBudget t := by nlinarith [hbudget_entries i i]
    have hbound' : ‖hg i i‖ + ‖r i‖ ≤ 2 * ‖r i‖ + qlag t * t ^ AndersonAC.S6.betaW +
        AndersonAC.S6.entryBudget t := by
      nlinarith [hnormg, hnorm0]
    have hbound : ‖hg i i‖ + ‖r i‖ ≤ 2 * K + 2 := by
      calc
        ‖hg i i‖ + ‖r i‖ ≤ 2 * ‖r i‖ + qlag t * t ^ AndersonAC.S6.betaW +
            AndersonAC.S6.entryBudget t := hbound'
        _ ≤ 2 * K + 2 := by nlinarith [hr i, hqt, htentry1]
    exact hbound.trans (by nlinarith)
  have hpre_lag : ∀ i, ‖hg i i - r i‖ ≤ (3 * K + 1) * t ^ AndersonAC.S6.betaW := by
    intro i
    have hdiff := hlag i
    calc
      ‖hg i i - r i‖ ≤ ‖hg i i - g0 i i‖ + ‖g0 i i - r i‖ := by
        have : hg i i - r i = (hg i i - g0 i i) + (g0 i i - r i) := by ring
        rw [this]
        exact norm_add_le _ _
      _ ≤ AndersonAC.S6.entryBudget t + qlag t * t ^ AndersonAC.S6.betaW :=
        add_le_add (hbudget_entries i i) hdiff
      _ ≤ 2 * t ^ AndersonAC.S6.betaW := by
        have hβ : 0 ≤ t ^ AndersonAC.S6.betaW := Real.rpow_nonneg ht.le _
        nlinarith [mul_le_mul_of_nonneg_right hq hβ, htentry]
      _ ≤ (3 * K + 1) * t ^ AndersonAC.S6.betaW := by
        have hβ : 0 ≤ t ^ AndersonAC.S6.betaW := Real.rpow_nonneg ht.le _
        nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 3 * K + 1 by linarith) hβ]
  have hpre_fourth : ∀ i, AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse t hg) i ≤
      AndersonAC.S6.fourthCap t := by
    intro i
    let x : Fin n → ℂ := fun j => AndersonAC.S6.scaledInverse t g0 i j
    let y : Fin n → ℂ := fun j => AndersonAC.S6.scaledInverse t (hg - g0) i j
    have hadd : ∀ j, AndersonAC.S6.scaledInverse t hg i j = x j + y j := by
      intro j
      simp [x, y, AndersonAC.S6.scaledInverse, Matrix.smul_apply, smul_eq_mul]
      ring
    have hsumAdd := sum_fourth_norm_add_le x y
    have hdiff4 : (∑ j, ‖y j‖ ^ 4) ≤
        t * (AndersonAC.S6.entryBudget t) ^ 2 * AndersonAC.S6.rowBudget t := by
      have hpoint : ∀ j, ‖y j‖ ≤ Real.sqrt t * AndersonAC.S6.entryBudget t := by
        intro j
        have h := hbudget_entries i j
        calc
          ‖y j‖ = Real.sqrt t * ‖hg i j - g0 i j‖ := by
            simp [y, AndersonAC.S6.scaledInverse, Matrix.smul_apply, smul_eq_mul,
              norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
          _ ≤ Real.sqrt t * AndersonAC.S6.entryBudget t :=
            mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg t)
      have hterm : ∀ j, ‖y j‖ ^ 4 ≤
          (Real.sqrt t * AndersonAC.S6.entryBudget t) ^ 2 * ‖y j‖ ^ 2 := by
        intro j
        have hsq : ‖y j‖ ^ 2 ≤ (Real.sqrt t * AndersonAC.S6.entryBudget t) ^ 2 := by
          have hA : 0 ≤ Real.sqrt t * AndersonAC.S6.entryBudget t :=
            mul_nonneg (Real.sqrt_nonneg t) (Real.rpow_nonneg ht.le _)
          have hdiffA : 0 ≤ Real.sqrt t * AndersonAC.S6.entryBudget t - ‖y j‖ :=
            sub_nonneg.mpr (hpoint j)
          have hsumA : 0 ≤ Real.sqrt t * AndersonAC.S6.entryBudget t + ‖y j‖ :=
            add_nonneg hA (norm_nonneg _)
          nlinarith [mul_nonneg hdiffA hsumA]
        calc
          ‖y j‖ ^ 4 = (‖y j‖ ^ 2) * (‖y j‖ ^ 2) := by ring
          _ ≤ (Real.sqrt t * AndersonAC.S6.entryBudget t) ^ 2 * ‖y j‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      calc
        (∑ j, ‖y j‖ ^ 4) ≤ ∑ j, ((Real.sqrt t * AndersonAC.S6.entryBudget t) ^ 2 * ‖y j‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => hterm j
        _ = (Real.sqrt t * AndersonAC.S6.entryBudget t) ^ 2 *
              AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t (hg - g0)) i := by
            simp [y, AndersonAC.S6.sqRow, ← Finset.mul_sum]
        _ ≤ (Real.sqrt t * AndersonAC.S6.entryBudget t) ^ 2 * AndersonAC.S6.rowBudget t :=
            mul_le_mul_of_nonneg_left (hbudget_rows i) (sq_nonneg _)
        _ = t * (AndersonAC.S6.entryBudget t) ^ 2 * AndersonAC.S6.rowBudget t := by
            rw [mul_pow, Real.sq_sqrt ht.le]
    have hratio : t * (AndersonAC.S6.entryBudget t) ^ 2 * AndersonAC.S6.rowBudget t =
        AndersonAC.S6.fourthCap t * t ^ (9 / 10000 : ℝ) := by
      let a := (42 / 100 : ℝ) * AndersonAC.S6.delta
      let b := (25 / 100 : ℝ) * AndersonAC.S6.delta
      have ha : 1 + 2 * ((42 / 100 : ℝ) * AndersonAC.S6.delta) +
          (25 / 100 : ℝ) * AndersonAC.S6.delta =
          (1 + AndersonAC.S6.delta) + 9 / 10000 := by
        norm_num [AndersonAC.S6.delta]
      calc
        t * (AndersonAC.S6.entryBudget t) ^ 2 * AndersonAC.S6.rowBudget t =
            t * (t ^ a) ^ 2 * t ^ b := by rfl
        _ = t ^ (1 + 2 * a + b) := by
          calc
            t * (t ^ a) ^ 2 * t ^ b = (t ^ (1 : ℝ)) * (t ^ (2 * a)) * t ^ b := by
              rw [Real.rpow_one, AndersonAC.L64.rpow_sq ht]
            _ = t ^ (1 + 2 * a + b) := by rw [← Real.rpow_add ht, ← Real.rpow_add ht]
        _ = t ^ ((1 + AndersonAC.S6.delta) + 9 / 10000) := by rw [ha]
        _ = AndersonAC.S6.fourthCap t * t ^ (9 / 10000 : ℝ) := by
          rw [AndersonAC.S6.fourthCap, ← Real.rpow_add ht]
    have hfour_start := hstart i
    have hsum : AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse t hg) i ≤
        (11 / 10) * AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse t g0) i +
          (101 : ℝ) ^ 4 * (∑ j, ‖y j‖ ^ 4) := by
      calc
        _ = ∑ j, ‖x j + y j‖ ^ 4 := by
          rw [AndersonAC.S6.fourthRow]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hadd j]
        _ ≤ (11 / 10) * (∑ j, ‖x j‖ ^ 4) + (101 : ℝ) ^ 4 * (∑ j, ‖y j‖ ^ 4) := hsumAdd
        _ = (11 / 10) * AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse t g0) i +
              (101 : ℝ) ^ 4 * (∑ j, ‖y j‖ ^ 4) := by rw [AndersonAC.S6.fourthRow]
    calc
      AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse t hg) i ≤
          (11 / 10) * ((4 / 5) * AndersonAC.S6.fourthCap t) +
            (101 : ℝ) ^ 4 * (t * (AndersonAC.S6.entryBudget t) ^ 2 * AndersonAC.S6.rowBudget t) := by
              exact hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hfour_start (by norm_num))
                (mul_le_mul_of_nonneg_left hdiff4 (by positivity)))
      _ ≤ AndersonAC.S6.fourthCap t := by
        rw [hratio]
        have hcap : 0 ≤ AndersonAC.S6.fourthCap t := Real.rpow_nonneg ht.le _
        have hsmall := mul_le_mul_of_nonneg_right hε hcap
        nlinarith
  exact ⟨hpre_diag, hpre_lag, hpre_fourth⟩

theorem eventually_pos_threshold {P : ℝ → Prop}
    (hP : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), P t) :
    ∃ t0, 0 < t0 ∧ ∀ t, 0 < t → t < t0 → P t := by
  obtain ⟨t0, ht0, hsub⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hP
  exact ⟨t0, ht0, fun t ht htt => hsub ⟨ht, htt⟩⟩

theorem rangeProjection_mul_eq {R B : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] (C : Matrix R B ℂ) :
    AndersonAC.S6.rangeProjection C * C = C := by
  classical
  let U := AndersonAC.S6.matrixRange C
  have hfix (v : EuclideanSpace ℂ B) : U.starProjection (Matrix.toEuclideanLin C v) =
      Matrix.toEuclideanLin C v := by
    apply U.starProjection_eq_self_iff.mpr
    exact ⟨v, rfl⟩
  have hPmap : Matrix.toEuclideanLin (AndersonAC.S6.rangeProjection C) =
      U.starProjection.toLinearMap := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    simp [U, AndersonAC.S6.rangeProjection]
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [hPmap]
  exact hfix v

theorem rangeProjection_star_eq {R B : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] (C : Matrix R B ℂ) :
    Matrix.conjTranspose (AndersonAC.S6.rangeProjection C) = AndersonAC.S6.rangeProjection C := by
  classical
  let U := AndersonAC.S6.matrixRange C
  apply (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).injective
  have hmap : Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
      (AndersonAC.S6.rangeProjection C) = U.starProjection := by
    rw [AndersonAC.S6.rangeProjection]
    exact (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).apply_symm_apply _
  calc
    Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
        (Matrix.conjTranspose (AndersonAC.S6.rangeProjection C)) =
        star (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
          (AndersonAC.S6.rangeProjection C)) :=
      map_star (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)) _
    _ = star U.starProjection := congrArg star hmap
    _ = U.starProjection := (isSelfAdjoint_starProjection U).star_eq
    _ = Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
          (AndersonAC.S6.rangeProjection C) := hmap.symm

theorem rangeProjection_idem {R B : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] (C : Matrix R B ℂ) :
    AndersonAC.S6.rangeProjection C * AndersonAC.S6.rangeProjection C =
      AndersonAC.S6.rangeProjection C := by
  classical
  let U := AndersonAC.S6.matrixRange C
  have hmap : Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
      (AndersonAC.S6.rangeProjection C) = U.starProjection := by
    rw [AndersonAC.S6.rangeProjection]
    exact (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).apply_symm_apply _
  have hUidem : U.starProjection * U.starProjection = U.starProjection := by
    apply ContinuousLinearMap.ext
    intro v
    exact U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem v)
  apply (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).injective
  calc
    Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
        (AndersonAC.S6.rangeProjection C * AndersonAC.S6.rangeProjection C) =
        Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ) (AndersonAC.S6.rangeProjection C) *
          Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ) (AndersonAC.S6.rangeProjection C) := by simp
    _ = U.starProjection * U.starProjection := by rw [hmap]
    _ = U.starProjection := hUidem
    _ = Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ) (AndersonAC.S6.rangeProjection C) := hmap.symm

theorem leverage_le_projectionWeight {R B : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] (C : Matrix R B ℂ) {τ : ℝ} (hτ : 0 < τ) (i : R) :
    AndersonAC.S6.leverage C τ i ≤ AndersonAC.S6.projectionWeight C i := by
  classical
  let P := AndersonAC.S6.rangeProjection C
  let G := AndersonAC.S6.ridgeGram C τ
  let H := AndersonAC.S6.ridgeGram (Matrix.conjTranspose C) τ
  let Q : Matrix R R ℂ := C * G⁻¹ * Matrix.conjTranspose C
  have hPstar : Matrix.conjTranspose P = P := rangeProjection_star_eq C
  have hPid : P * P = P := rangeProjection_idem C
  have hPC : P * C = C := rangeProjection_mul_eq C
  have hCHP : Matrix.conjTranspose C * P = Matrix.conjTranspose C := by
    have h := congrArg Matrix.conjTranspose hPC
    simpa [hPstar] using h
  have hPQ : P * Q = Q := by
    calc
      P * Q = (P * C) * G⁻¹ * Matrix.conjTranspose C := by
        dsimp [Q]
        simp [Matrix.mul_assoc]
      _ = Q := by rw [hPC]
  have hQP : Q * P = Q := by
    calc
      Q * P = C * G⁻¹ * (Matrix.conjTranspose C * P) := by
        dsimp [Q]
        simp [Matrix.mul_assoc]
      _ = Q := by rw [hCHP]
  have hGunit : IsUnit G.det := AndersonAC.AgentS6.ridgeGram_isUnit C hτ
  have hHunit : IsUnit H.det := AndersonAC.AgentS6.ridgeGram_isUnit (Matrix.conjTranspose C) hτ
  have hcomm : H * C = C * G := by
    dsimp [H, G, AndersonAC.S6.ridgeGram, AndersonAC.S6.gram]
    rw [Matrix.conjTranspose_conjTranspose]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
    rw [Matrix.mul_assoc]
  have hHF : H * (1 - Q) = (τ : ℂ) • (1 : Matrix R R ℂ) := by
    calc
      H * (1 - Q) = H - (H * C) * G⁻¹ * Matrix.conjTranspose C := by
        dsimp [Q]
        rw [Matrix.mul_sub, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = H - (C * G) * G⁻¹ * Matrix.conjTranspose C := by rw [hcomm]
      _ = H - C * (G * G⁻¹) * Matrix.conjTranspose C := by simp [Matrix.mul_assoc]
      _ = H - C * Matrix.conjTranspose C := by
        rw [Matrix.mul_nonsing_inv G hGunit]
        simp
      _ = (τ : ℂ) • (1 : Matrix R R ℂ) := by
        dsimp [H, AndersonAC.S6.ridgeGram, AndersonAC.S6.gram]
        simp only [Matrix.conjTranspose_conjTranspose]
        abel
  have hF : 1 - Q = (τ : ℂ) • H⁻¹ := by
    calc
      1 - Q = (H⁻¹ * H) * (1 - Q) := by
        rw [Matrix.nonsing_inv_mul H hHunit, Matrix.one_mul]
      _ = H⁻¹ * (H * (1 - Q)) := by simp [Matrix.mul_assoc]
      _ = H⁻¹ * ((τ : ℂ) • (1 : Matrix R R ℂ)) := by rw [hHF]
      _ = (τ : ℂ) • H⁻¹ := by simp [Matrix.mul_smul]
  have hHpsd : (H⁻¹).PosSemidef := by
    dsimp [H]
    exact AndersonAC.AgentS6.ridgeGram_posSemidef (Matrix.conjTranspose C) hτ.le |>.inv
  have hFpsd : (1 - Q).PosSemidef := by
    rw [hF]
    exact Matrix.PosSemidef.smul hHpsd (Complex.zero_le_real.mpr hτ.le)
  have hEq : Matrix.conjTranspose P * (1 - Q) * P = P - Q := by
    rw [hPstar]
    calc
      P * (1 - Q) * P = P * P - (P * Q) * P := by noncomm_ring
      _ = P - Q := by rw [hPid, hPQ, hQP]
  have hPQpsd : (P - Q).PosSemidef := by
    rw [← hEq]
    exact hFpsd.conjTranspose_mul_mul_same P
  have hdiag : 0 ≤ (P - Q) i i := hPQpsd.diag_nonneg
  have hdiagR : 0 ≤ (P i i).re - (Q i i).re := by
    have h := (Complex.nonneg_iff.mp hdiag).1
    simpa [Matrix.sub_apply, Complex.sub_re] using h
  unfold AndersonAC.S6.leverage AndersonAC.S6.projectionWeight
  change (Q i i).re ≤ (P i i).re
  linarith

theorem pivot_location_proof {ι : Type*} (d : ℕ) (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    AndersonAC.S6.Planned.pivot_location (ι := ι) d a L ha hL := by
  classical
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let p : ℝ := 1 + AndersonAC.S6.e0
  let s : ℝ := p / 3
  let b : ℝ := a / 1024
  have hid : Tendsto id F (nhds (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow297 : Tendsto (fun t : ℝ => t ^ (297 / 100 : ℝ)) F (nhds 0) := by
    exact hid.rpow_const_nhds_zero (by norm_num)
  have hpow4 : Tendsto (fun t : ℝ => t ^ (4 : ℝ)) F (nhds 0) := by
    exact hid.rpow_const_nhds_zero (by norm_num)
  have hsmall_power : ∀ᶠ t in F, t ^ (297 / 100 : ℝ) + t ^ (4 : ℝ) < 1 / 2048 := by
    have hsum : Tendsto (fun t : ℝ => t ^ (297 / 100 : ℝ) + t ^ (4 : ℝ)) F (nhds 0) := by
      simpa using hpow297.add hpow4
    have h := hsum.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2048))
    filter_upwards [h] with t ht
    exact ht
  have htInv : Tendsto (fun t : ℝ => t ^ (-3 : ℝ)) F atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-3 : ℝ) < 0)
  have hdecayBase : Tendsto (fun x : ℝ => x ^ s * Real.exp (-b * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b (by dsimp [b]; positivity)
  have hdecay := hdecayBase.comp htInv
  have hsmall_exp : ∀ᶠ t in F,
      (L / 2) * ((t ^ (-3 : ℝ)) ^ s * Real.exp (-b * t ^ (-3 : ℝ))) < 1 := by
    have hlim : Tendsto (fun t : ℝ => (L / 2) *
        ((t ^ (-3 : ℝ)) ^ s * Real.exp (-b * t ^ (-3 : ℝ)))) F (nhds 0) := by
      simpa using tendsto_const_nhds.mul hdecay
    have h := hlim.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h] with t ht
    exact ht
  unfold AndersonAC.S6.Planned.pivot_location
  filter_upwards [self_mem_nhdsWithin, hsmall_power, hsmall_exp] with t ht hpowSmall hexpSmall
  change 0 < t at ht
  intro m dist ell hell hdecay x hx
  by_contra hloc
  have hdist : ell / 2 ≤ dist x := le_of_not_gt hloc
  have htinv4pos : 0 < t ^ (-4 : ℤ) := by
    rw [show t ^ (-4 : ℤ) = (t ^ (4 : ℝ))⁻¹ by
      calc
        t ^ (-4 : ℤ) = t ^ ((-4 : ℤ) : ℝ) := (Real.rpow_intCast t (-4 : ℤ)).symm
        _ = t ^ (-(4 : ℝ)) := by norm_num
        _ = (t ^ (4 : ℝ))⁻¹ := Real.rpow_neg ht.le _]
    positivity
  have hdistlower : (1 / 1024 : ℝ) * t ^ (-4 : ℤ) ≤ dist x / 2 := by
    calc
      (1 / 1024 : ℝ) * t ^ (-4 : ℤ) ≤ ell / 4 := by nlinarith [hell]
      _ ≤ dist x / 2 := by nlinarith [hdist]
  have hpowInv : t ^ (-4 : ℤ) = (t ^ (4 : ℝ))⁻¹ := by
    calc
      t ^ (-4 : ℤ) = t ^ ((-4 : ℤ) : ℝ) := (Real.rpow_intCast t (-4 : ℤ)).symm
      _ = t ^ (-(4 : ℝ)) := by norm_num
      _ = (t ^ (4 : ℝ))⁻¹ := Real.rpow_neg ht.le _
  have herr : t ^ (-(103 / 100 : ℝ)) + 1 ≤ (1 / 2048 : ℝ) * t ^ (-4 : ℤ) := by
    have hprod :
        (t ^ (-(103 / 100 : ℝ)) + 1) * t ^ (4 : ℝ) < 1 / 2048 := by
      have heq :
          (t ^ (-(103 / 100 : ℝ)) + 1) * t ^ (4 : ℝ) =
            t ^ (297 / 100 : ℝ) + t ^ (4 : ℝ) := by
        calc
          (t ^ (-(103 / 100 : ℝ)) + 1) * t ^ (4 : ℝ) =
              t ^ (-(103 / 100 : ℝ)) * t ^ (4 : ℝ) + t ^ (4 : ℝ) := by ring
          _ = t ^ (297 / 100 : ℝ) + t ^ (4 : ℝ) := by
            rw [← Real.rpow_add ht]
            congr 1
            norm_num
      rw [heq]
      exact hpowSmall
    rw [hpowInv]
    have hdiv : t ^ (-(103 / 100 : ℝ)) + 1 <
        (1 / 2048 : ℝ) / t ^ (4 : ℝ) :=
      (lt_div_iff₀ (Real.rpow_pos_of_pos ht 4)).2 hprod
    have hmul : (1 / 2048 : ℝ) / t ^ (4 : ℝ) =
        (1 / 2048 : ℝ) * (t ^ (4 : ℝ))⁻¹ := by rw [div_eq_mul_inv]
    rw [← hmul]
    exact hdiv.le
  have hrad : (1 / 2048 : ℝ) * t ^ (-4 : ℤ) ≤
      max (dist x / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0 := by
    have hdif : (1 / 2048 : ℝ) * t ^ (-4 : ℤ) ≤
        dist x / 2 - t ^ (-(103 / 100 : ℝ)) - 1 := by
      nlinarith [hdistlower, hpowInv, htinv4pos, herr]
    exact le_trans hdif (le_max_left _ _)
  have hexp_order : -2 * a * t *
      max (dist x / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0 ≤
      -b * t ^ (-3 : ℝ) := by
    have hcoeff : -2 * a * t ≤ 0 := by nlinarith [mul_pos ha ht]
    have hmul := mul_le_mul_of_nonpos_left hrad hcoeff
    have hpow_mulZ : t * t ^ (-4 : ℤ) = t ^ (-3 : ℤ) := by
      have h : t ^ (1 : ℤ) * t ^ (-4 : ℤ) = t ^ (1 + (-4 : ℤ)) := by
        rw [← zpow_add₀ (ne_of_gt ht)]
      simpa using h
    have hpow_mul : t * t ^ (-4 : ℤ) = t ^ (-3 : ℝ) := by
      rw [hpow_mulZ]
      simpa using (Real.rpow_intCast t (-3 : ℤ)).symm
    dsimp [b]
    have hmulEq : -2 * a * t * ((1 / 2048 : ℝ) * t ^ (-4 : ℤ)) =
        -(a / 1024) * t ^ (-3 : ℝ) := by
      calc
        -2 * a * t * ((1 / 2048 : ℝ) * t ^ (-4 : ℤ)) =
            -(a / 1024) * (t * t ^ (-4 : ℤ)) := by ring
        _ = -(a / 1024) * t ^ (-3 : ℝ) := by rw [hpow_mul]
    rw [hmulEq] at hmul
    linarith
  have hexp_le : Real.exp (-2 * a * t *
      max (dist x / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) ≤
      Real.exp (-b * t ^ (-3 : ℝ)) := Real.exp_le_exp.mpr hexp_order
  have hratio_eq :
      (L / 2) * ((t ^ (-3 : ℝ)) ^ s * Real.exp (-b * t ^ (-3 : ℝ))) =
        (L * Real.exp (-b * t ^ (-3 : ℝ))) / (2 * t ^ p) := by
    have hpow : (t ^ (-3 : ℝ)) ^ s = t ^ (-p) := by
      calc
        (t ^ (-3 : ℝ)) ^ s = t ^ ((-3 : ℝ) * s) :=
          (Real.rpow_mul ht.le (-3 : ℝ) s).symm
        _ = t ^ (-p) := by congr 1 <;> dsimp [s, p] <;> ring
    rw [hpow, Real.rpow_neg ht.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos ht p)]
  have hexpSmall' : (L * Real.exp (-b * t ^ (-3 : ℝ))) / (2 * t ^ p) < 1 := by
    rw [← hratio_eq]
    exact hexpSmall
  have hupper : L * Real.exp (-2 * a * t *
      max (dist x / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) < 2 * t ^ p := by
    have hdiv := (div_lt_iff₀ (by positivity : 0 < 2 * t ^ p)).mp hexpSmall'
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hexp_le hL.le) (by simpa using hdiv)
  have hlow := hx
  unfold AndersonAC.S6.leverageScale at hlow
  exact (not_lt_of_ge hlow) (lt_of_le_of_lt (hdecay x) hupper)

theorem matrixRange_columnEquiv {R B B' : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (C : Matrix R B ℂ) (e : B' ≃ B) :
    AndersonAC.S6.matrixRange (C.submatrix id e) = AndersonAC.S6.matrixRange C := by
  classical
  have hvec1 (w : EuclideanSpace ℂ B') :
      Matrix.toEuclideanLin (C.submatrix id e) w =
        Matrix.toEuclideanLin C (WithLp.toLp 2 (fun i : B => w (e.symm i))) := by
    change WithLp.toLp 2 (Matrix.mulVec (C.submatrix id e) (WithLp.ofLp w)) =
      WithLp.toLp 2 (Matrix.mulVec C (WithLp.ofLp (WithLp.toLp 2 (fun i : B => w (e.symm i)))) )
    apply congrArg (WithLp.toLp 2)
    rw [Matrix.submatrix_mulVec_equiv]
    funext i
    rfl
  have hvec2 (w : EuclideanSpace ℂ B) :
      Matrix.toEuclideanLin (C.submatrix id e) (WithLp.toLp 2 (fun j : B' => w (e j))) =
        Matrix.toEuclideanLin C w := by
    change WithLp.toLp 2 (Matrix.mulVec (C.submatrix id e)
        (WithLp.ofLp (WithLp.toLp 2 (fun j : B' => w (e j))))) =
      WithLp.toLp 2 (Matrix.mulVec C (WithLp.ofLp w))
    apply congrArg (WithLp.toLp 2)
    rw [Matrix.submatrix_mulVec_equiv]
    funext i
    simp [Function.comp_def]
  apply Submodule.ext
  intro v
  change v ∈ LinearMap.range (Matrix.toEuclideanLin (C.submatrix id e)) ↔
    v ∈ LinearMap.range (Matrix.toEuclideanLin C)
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨WithLp.toLp 2 (fun i : B => w (e.symm i)), ?_⟩
    exact (hvec1 w).symm
  · rintro ⟨w, rfl⟩
    refine ⟨WithLp.toLp 2 (fun j : B' => w (e j)), ?_⟩
    exact hvec2 w

theorem exteriorGeometry_columnEquiv {n B B' : Type*} [Fintype n] [DecidableEq n]
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (d : ℕ)
    (ρ : n → ℝ) (H : Matrix n n ℂ) (C : Matrix n B ℂ) (t : ℝ) (r : n → ℂ)
    (e : B' ≃ B) (hgeo : ExteriorGeometry d ρ H C t r) :
    ExteriorGeometry d ρ H (C.submatrix id e) t r := by
  rcases hgeo with ⟨hradius, hdecomp, hsource⟩
  refine ⟨hradius, hdecomp, ?_⟩
  intro v hv i hi
  have hvC : v ∈ matrixRange C := by
    rw [matrixRange_columnEquiv C e] at hv
    exact hv
  exact hsource v hvC i hi

theorem projectionWeight_columnEquiv {R B B' : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (C : Matrix R B ℂ) (e : B' ≃ B) (i : R) :
    AndersonAC.S6.projectionWeight (C.submatrix id e) i =
      AndersonAC.S6.projectionWeight C i := by
  classical
  let U₁ := AndersonAC.S6.matrixRange (C.submatrix id e)
  let U₂ := AndersonAC.S6.matrixRange C
  have hrange : U₁ = U₂ := matrixRange_columnEquiv C e
  have hproj : U₁.starProjection = U₂.starProjection := by
    apply ContinuousLinearMap.ext
    intro v
    apply U₁.eq_starProjection_of_mem_orthogonal
    · simpa [U₁, U₂, hrange] using U₂.starProjection_apply_mem v
    · simpa [U₁, U₂, hrange] using U₂.sub_starProjection_mem_orthogonal v
  have hmap₁ : Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
      (AndersonAC.S6.rangeProjection (C.submatrix id e)) = U₁.starProjection := by
    rw [AndersonAC.S6.rangeProjection]
    exact (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).apply_symm_apply _
  have hmap₂ : Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
      (AndersonAC.S6.rangeProjection C) = U₂.starProjection := by
    rw [AndersonAC.S6.rangeProjection]
    exact (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).apply_symm_apply _
  have hR : AndersonAC.S6.rangeProjection (C.submatrix id e) =
      AndersonAC.S6.rangeProjection C := by
    apply (Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).injective
    change Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)
        (AndersonAC.S6.rangeProjection (C.submatrix id e)) =
      Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ) (AndersonAC.S6.rangeProjection C)
    rw [hmap₁, hmap₂, hproj]
  unfold AndersonAC.S6.projectionWeight
  rw [hR]

theorem leverage_decay_of_rangeLocalization {n : ℕ} {B : Type*} [Fintype B]
    [DecidableEq B] (d : ℕ) (c K : ℝ) (hc : 0 < c) (hck : c ≤ K)
    (hlocal : AndersonAC.S6.Planned.range_localization d c K hc hck)
    (t : ℝ) (r : Fin n → ℂ) (ρ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) B ℂ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hb : AndersonAC.S6.BroadBounds c K r)
    (hgeo : AndersonAC.S6.ExteriorGeometry d ρ H C t r) (τ : ℝ) (hτ : 0 < τ) :
    ∃ a L : ℝ, 0 < a ∧ 0 < L ∧ ∀ i,
      AndersonAC.S6.leverage C τ i ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i) := by
  classical
  obtain ⟨a, L, ha, hL, hbound⟩ := hlocal
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  have hgeo' := exteriorGeometry_columnEquiv d ρ H C t r e hgeo
  have hbound' := hbound (Fintype.card B) n t r ρ H (C.submatrix id e) ht ht1 hb hgeo'
  refine ⟨a, L, ha, hL, fun i => ?_⟩
  calc
    AndersonAC.S6.leverage C τ i = AndersonAC.S6.leverage (C.submatrix id e) τ i :=
      (AndersonAC.AgentS6.leverage_reindex C e τ i).symm
    _ ≤ AndersonAC.S6.projectionWeight (C.submatrix id e) i :=
      AndersonAC.AgentS6.leverage_le_projectionWeight (C.submatrix id e) hτ i
    _ ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i) := hbound'.2 i

abbrev RangeDecayBound (d : ℕ) (c K a L : ℝ) : Prop :=
  ∀ (b n : ℕ) (t : ℝ) (r : Fin n → ℂ) (ρ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin b) ℂ),
    0 < t → t ≤ 1 → BroadBounds c K r → ExteriorGeometry d ρ H C t r →
    (∀ v ∈ matrixRange C,
      ‖Matrix.toEuclideanLin (exponentialWeight a t ρ) v‖ ≤ L * ‖v‖) ∧
      (∀ i, projectionWeight C i ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i))

theorem leverage_decay_of_rangeBound {n : ℕ} {B : Type*} [Fintype B]
    [DecidableEq B] (d : ℕ) (c K a L : ℝ) (hRange : RangeDecayBound d c K a L)
    (t : ℝ) (r : Fin n → ℂ) (ρ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) B ℂ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hb : BroadBounds c K r) (hgeo : ExteriorGeometry d ρ H C t r)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ i, leverage C τ i ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i) := by
  classical
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  have hgeo' := exteriorGeometry_columnEquiv d ρ H C t r e hgeo
  have hbound := hRange (Fintype.card B) n t r ρ H (C.submatrix id e) ht ht1 hb hgeo'
  intro i
  calc
    leverage C τ i = leverage (C.submatrix id e) τ i :=
      (AndersonAC.AgentS6.leverage_reindex C e τ i).symm
    _ ≤ projectionWeight (C.submatrix id e) i :=
      AndersonAC.AgentS6.leverage_le_projectionWeight (C.submatrix id e) hτ i
    _ ≤ L ^ 2 * Real.exp (-2 * a * t * ρ i) := hbound.2 i

theorem collapsedDistanceToCore_lower {n : ℕ} (core : Finset (Fin n))
    (dist : Fin n → Fin n → ℝ) (collapsed : Fin n → Fin n → ℝ)
    (t : ℝ) (hcore : core.Nonempty)
    (hmetric : ∀ i j, dist i j / 2 - t ^ (-(103 / 100 : ℝ)) ≤ collapsed i j)
    (i : Fin n) :
    distanceToCore dist core i / 2 - t ^ (-(103 / 100 : ℝ)) ≤
      distanceToCore collapsed core i := by
  unfold AndersonAC.S6.distanceToCore
  simp only [dif_pos hcore]
  rw [Finset.le_inf'_iff]
  intro b hb
  have hmin := Finset.inf'_le (fun j => dist i j) hb
  have hm := hmetric i b
  nlinarith

theorem running_pivot_local_of_decay {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (μ : Measure Ω) (d : ℕ) (c K Cloc : ℝ) (dist : Fin n → Fin n → ℝ)
    (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell a L : ℝ)
    (ht : 0 < t) (ha : 0 < a) (hcorecard : 1 ≤ core.card)
    (hlocal : TrialLocalInput q μ d c K Cloc dist collapsed ell)
    (k : ℕ) (ω : Ω) (hk : k < q.stop ω)
    (hprev : ∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2)
    (hdecay : ∀ i, trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i ≤
      L ^ 2 * Real.exp (-2 * a * t *
        max (distanceToCore (collapsed k ω) core i - 1) 0))
    (hpivot : ∀ (m dist' : Fin n → ℝ) (ell' : ℝ),
      (1 / 256) * t ^ (-4 : ℤ) ≤ ell' →
      (∀ i, m i ≤ L ^ 2 * Real.exp (-2 * a * t *
        max (dist' i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0)) →
      ∀ x, 2 * leverageScale t ≤ m x → dist' x < ell' / 2) :
    distanceToCore dist core (q.pivot k ω) < ell / 2 := by
  have hcore : core.Nonempty := Finset.card_pos.mp (by omega)
  have hdecay' : ∀ i, trialWeights t (r ω) (q.state k ω) (q.ridge k ω) i ≤
      L ^ 2 * Real.exp (-2 * a * t *
        max (distanceToCore dist core i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) := by
    intro i
    have hbase := collapsedDistanceToCore_lower core dist (collapsed k ω) t hcore
      (hlocal.metric k ω hk.le hprev) i
    have hrho : max (distanceToCore dist core i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0 ≤
        max (distanceToCore (collapsed k ω) core i - 1) 0 :=
      max_le_max (sub_le_sub_right hbase 1) le_rfl
    have he : Real.exp (-2 * a * t * max (distanceToCore (collapsed k ω) core i - 1) 0) ≤
        Real.exp (-2 * a * t *
          max (distanceToCore dist core i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hrho (by nlinarith [mul_pos ha ht])
    exact (hdecay i).trans (mul_le_mul_of_nonneg_left he (sq_nonneg L))
  have hmlo : 2 * leverageScale t ≤
      trialWeights t (r ω) (q.state k ω) (q.ridge k ω) (q.pivot k ω) := by
    calc
      2 * leverageScale t ≤ maxWeight (trialWeights t (r ω) (q.state k ω) (q.ridge k ω)) :=
        (q.running_cap k ω hk).1
      _ = trialWeights t (r ω) (q.state k ω) (q.ridge k ω) (q.pivot k ω) :=
        (q.pivot_max k ω hk).symm
  exact hpivot (trialWeights t (r ω) (q.state k ω) (q.ridge k ω))
    (distanceToCore dist core) ell hlocal.ell_lower hdecay' (q.pivot k ω) hmlo

theorem all_running_pivots_local {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    [Nonempty Ω]
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (μ : Measure Ω)
    (d : ℕ) (c K Cloc : ℝ) (hc : 0 < c)
    (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ)
    (hlocal : TrialLocalInput q μ d c K Cloc dist collapsed ell)
    (hcorecard : 1 ≤ core.card) (hBroad : ∀ ω, BroadBounds c K (r ω))
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L) (hRange : RangeDecayBound d c K a L)
    (hPivotAt : ∀ (m dist' : Fin n → ℝ) (ell' : ℝ),
      (1 / 256) * t ^ (-4 : ℤ) ≤ ell' →
      (∀ i, m i ≤ L ^ 2 * Real.exp (-2 * a * t *
        max (dist' i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0)) →
      ∀ x, 2 * leverageScale t ≤ m x → dist' x < ell' / 2)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2 := by
  classical
  have hcore : core.Nonempty := Finset.card_pos.mp (by omega)
  have hck : c ≤ K := by
    let ω₀ := Classical.choice (inferInstance : Nonempty Ω)
    obtain ⟨-, hb⟩ := hBroad ω₀
    obtain ⟨i, hi⟩ := hcore
    obtain ⟨-, hci, hiK⟩ := hb i
    exact hci.trans hiK
  have hstep (k : ℕ) (ω : Ω) (hk : k < q.stop ω)
      (hprev : ∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2) :
      distanceToCore dist core (q.pivot k ω) < ell / 2 := by
    have hgeoData := hlocal.range_geometry k ω hk.le hprev
    obtain ⟨H, hgeo⟩ := hgeoData
    let ρ : Fin n → ℝ := fun i => max (distanceToCore (collapsed k ω) core i - 1) 0
    have hdecay := leverage_decay_of_rangeBound d c K a L hRange t (r ω) ρ H
      (trialCross t (r ω) (q.state k ω)) ht ht1 (hBroad ω) hgeo
      (q.ridge k ω) (q.running_ridge k ω hk)
    exact running_pivot_local_of_decay q μ d c K Cloc dist collapsed ell a L
      ht ha hcorecard hlocal k ω hk hprev hdecay hPivotAt
  have hall : ∀ k ω j, j ≤ k → j < q.stop ω →
      distanceToCore dist core (q.pivot j ω) < ell / 2 := by
    intro k
    induction k with
    | zero =>
        intro ω j hj hrun
        have hj0 : j = 0 := by omega
        subst j
        exact hstep 0 ω hrun (by intro j hj; omega)
    | succ k ih =>
        intro ω j hj hrun
        by_cases hlast : j = k + 1
        · subst j
          apply hstep (k + 1) ω hrun
          intro j' hj'
          exact ih ω j' (by omega) (lt_trans hj' hrun)
        · have hjk : j ≤ k := by omega
          exact ih ω j hjk hrun
  intro k ω hk
  exact hall k ω k le_rfl hk

theorem exists_tendsto_error_modulus {P : ℝ → ℝ → Prop}
    (hP : ∀ e > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → P t e) :
    ∃ ε : ℝ → ℝ, Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ t, 0 ≤ ε t) ∧ ∃ t0, 0 < t0 ∧ ∀ t, 0 < t → t < t0 → P t (ε t) := by
  classical
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos : ∀ n, 0 < e n := by intro n; dsimp [e]; positivity
  let d : ℕ → ℝ := fun n => Classical.choose (hP (e n) (hepos n))
  have hd : ∀ n, 0 < d n ∧ ∀ t, 0 < t → t < d n → P t (e n) := by
    intro n
    exact Classical.choose_spec (hP (e n) (hepos n))
  let s : ℕ → ℝ :=
    Nat.rec (min (d 0) 1)
      (fun n sn => min (sn / 2) (min (d (n + 1)) (1 / ((n : ℝ) + 2))))
  have hspos : ∀ n, 0 < s n := by
    intro n
    induction n with
    | zero => dsimp [s]; exact lt_min (hd 0).1 (by norm_num)
    | succ n ih =>
        dsimp [s]
        exact lt_min (by positivity) (lt_min (hd (n + 1)).1 (by positivity))
  have hsle_d : ∀ n, s n ≤ d n := by
    intro n
    cases n with
    | zero => dsimp [s]; exact min_le_left _ _
    | succ n =>
        dsimp [s]
        exact (min_le_right _ _).trans (min_le_left _ _)
  have hsle_inv : ∀ n, s n ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => dsimp [s]; norm_num
    | succ n ih =>
        calc
          s (n + 1) ≤ min (d (n + 1)) (1 / ((n : ℝ) + 2)) := min_le_right _ _
          _ ≤ 1 / ((n : ℝ) + 2) := min_le_right _ _
          _ = 1 / (((n + 1 : ℕ) : ℝ) + 1) := by push_cast; ring
  have hsstep : ∀ n, s (n + 1) ≤ s n := by
    intro n
    calc
      s (n + 1) ≤ s n / 2 := by change min (s n / 2) _ ≤ _; exact min_le_left _ _
      _ ≤ s n := by linarith [hspos n]
  have hsanti : Antitone s := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step j hij ih =>
        exact (hsstep j).trans ih
  have hex : ∀ t, 0 < t → ∃ n, s n ≤ t := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / t)
    have hn' : 1 / t < (n : ℝ) := hn
    have hprod : 1 < t * ((n : ℝ) + 1) := by
      have h := (div_lt_iff₀ ht).mp hn'
      nlinarith
    have hinv : 1 / ((n : ℝ) + 1) ≤ t := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    exact ⟨n, (hsle_inv n).trans hinv⟩
  let idx (t : ℝ) (ht : 0 < t) : ℕ :=
    @Nat.find (fun j : ℕ => s j ≤ t)
      (fun j => Classical.propDecidable (s j ≤ t)) (hex t ht)
  let N : ℝ → ℕ := fun t => if ht : 0 < t then idx t ht else 0
  have hNspec (t : ℝ) (ht : 0 < t) : s (N t) ≤ t := by
    simp only [N, dif_pos ht]
    change s (idx t ht) ≤ t
    exact @Nat.find_spec (fun j : ℕ => s j ≤ t)
      (fun j => Classical.propDecidable (s j ≤ t)) (hex t ht)
  have hNmin (t : ℝ) (ht : 0 < t) {n : ℕ} (hn : n < N t) : ¬ s n ≤ t := by
    simp only [N, dif_pos ht] at hn
    change n < idx t ht at hn
    exact @Nat.find_min (fun j : ℕ => s j ≤ t)
      (fun j => Classical.propDecidable (s j ≤ t)) (hex t ht) n hn
  let ε : ℝ → ℝ := fun t => if ht : 0 < t then e (N t - 1) else 0
  have hεnonneg : ∀ t, 0 ≤ ε t := by
    intro t
    by_cases ht : 0 < t
    · simp [ε, ht, (hepos (N t - 1)).le]
    · simp [ε, ht]
  have hN_tendsto : Tendsto N (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    rw [Filter.tendsto_atTop]
    intro m
    have hs := hspos (m + 1)
    have hev : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), t < s (m + 1) := by
      exact (nhdsGT_basis (0 : ℝ)).eventually_iff.mpr
        ⟨s (m + 1), hs, fun t ht => ht.2⟩
    filter_upwards [hev, self_mem_nhdsWithin] with t hts ht
    change 0 < t at ht
    by_contra hnot
    have hNm : N t < m := lt_of_not_ge hnot
    have hcomp := (hsstep m).trans (hsanti hNm.le)
    have hsN := hNspec t ht
    exact (not_le_of_gt hts) (hcomp.trans hsN)
  have hNsub_tendsto : Tendsto (fun t => N t - 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    rw [Filter.tendsto_atTop]
    intro m
    have hbound : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), m + 1 ≤ N t :=
      hN_tendsto (eventually_atTop.2 ⟨m + 1, fun _ h => h⟩)
    filter_upwards [hbound] with t ht
    omega
  have hetendsto : Tendsto e atTop (nhds 0) := by
    simpa [e] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hεeq : ε =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun t => e (N t - 1) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    simp [ε, ht]
  refine ⟨ε, ?_, hεnonneg, s 0, hspos 0, ?_⟩
  · exact (tendsto_congr' hεeq).2 (hetendsto.comp hNsub_tendsto)
  · intro t ht htt0
    have hNpos : 0 < N t := by
      by_contra h
      have hzero : N t = 0 := Nat.eq_zero_of_not_pos h
      have hspec := hNspec t ht
      apply (not_le_of_gt htt0)
      simpa [hzero] using hspec
    let n := N t - 1
    have hnst : n + 1 = N t := by dsimp [n]; omega
    have hnlt : n < N t := by omega
    have hsnot := hNmin t ht hnlt
    have hts : t < s n := lt_of_not_ge hsnot
    have htd : t < d n := lt_of_lt_of_le hts (hsle_d n)
    have hp := (hd n).2 t ht htd
    simpa [ε, ht, n] using hp

end AndersonAC.AgentS6

