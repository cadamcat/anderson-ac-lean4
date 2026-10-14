import AndersonAC.AgentS6Cap.Predictable
import AndersonAC.AgentS6.Stretched
import AndersonAC.AgentS6.Monitor

set_option maxHeartbeats 1000000

/-! One monitored row satisfies the varying-ridge maximal inequality. -/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

theorem row_crossing_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {core : Finset (Fin n)} {t c K L cConc : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (i : Fin n) (d : ℕ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hK : 1 ≤ K)
    (hL : 0 < L) (hcConc : 0 < cConc)
    (hbroad : ∀ ω, BroadBounds c K (r ω))
    (hstart : ∀ ω j, fourthRow (scaledInverse t (g0 ω)) j ≤ (4 / 5) * fourthCap t)
    (hconc : VectorConcentrationInput μ q.history cConc)
    (hrowBias : ∀ k, ∀ᵐ ω ∂μ, k < q.stop ω →
      |μ[(fun ω => recordedLeverageIncrement q k ω i) | q.history k] ω| ≤
        oneRowBias d t L ‖heatV q k ω i‖)
    (hrowJump : ∀ k ω, k < q.stop ω →
      |recordedLeverageIncrement q k ω i| ≤ oneRowJump t L ‖heatV q k ω i‖)
    (hmargin : (heatLimit t : ℝ) * (leverageScale t) ^ 2 / t ≤
      t ^ ((27 / 100) * delta))
    (hBiasSmall : ∀ (s : Finset ℕ) (v : ℕ → ℝ), (∀ k, 0 ≤ v k) →
      (s.card : ℝ) ≤ heatLimit t →
      ∑ k ∈ s, v k ^ 2 ≤ (4 * (K / c)) * t ^ ((27 / 100) * delta) →
      ∑ k ∈ s, oneRowBias d t L (v k) ≤ leverageScale t / 4) :
    ∀ᵐ ω ∂μ,
      conditionalProbability μ (q.history 0)
        {ω | ∃ s : ℕ, s ≤ heatLimit t ∧ leverageScale t / 2 <
          |∑ k ∈ Finset.range s, recordedLeverageIncrement q k ω i|} ω ≤
        (4 : ℝ) * Real.exp (-
          (cConc * min
            (1 / (128 * L ^ 2 * (2 * (2 * (K / c)) + 1)))
            (1 / (8 * L * (2 * Real.sqrt (K / c) + 1)))) *
          t ^ (-((27 / 100) * delta))) := by
  classical
  let l : ℝ := leverageScale t
  let a : ℝ := (27 / 100) * delta
  let C_H : ℝ := 2 * (K / c)
  let C_V : ℝ := 8 * L ^ 2 * (2 * C_H + 1)
  let C_J : ℝ := 2 * L * (2 * Real.sqrt (K / c) + 1)
  let J0 : ℝ := L * l * (2 * Real.sqrt (K / c) + 1) * t ^ (1 / 4 : ℝ)
  let J : ℝ := 2 * J0
  let V : ℝ := C_V * l ^ 2 * t ^ a
  let Z : ℕ → Ω → ℝ := fun k ω => recordedLeverageIncrement q k ω i
  let variance : ℕ → Ω → ℝ := fun k ω =>
    if ω ∈ rowActiveRun q i k then
      8 * L ^ 2 * l ^ 2 *
        (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) + l ^ 2 / t)
    else 0
  have hl : 0 < l := Real.rpow_pos_of_pos ht _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKc : 0 < K / c := div_pos hKpos hc
  have hCH : 0 < C_H := by dsimp [C_H]; positivity
  have hCV : 0 < C_V := by dsimp [C_V]; positivity
  have hJ0 : 0 < J0 := by positivity
  have hJ : 0 < J := by positivity
  have hV : 0 < V := by positivity
  have hscale : l / Real.sqrt t ≤ t ^ (1 / 4 : ℝ) := by
    have hpow : l ≤ t ^ (3 / 4 : ℝ) := by
      dsimp [l, leverageScale]
      exact rpow_anti ht ht1 (by norm_num [e0, delta])
    have hprod : t ^ (1 / 4 : ℝ) * Real.sqrt t = t ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, (Real.rpow_add ht (1 / 4 : ℝ) (1 / 2 : ℝ)).symm]
      congr 1
      norm_num
    exact (div_le_iff₀ (Real.sqrt_pos.mpr ht)).2 (by rw [hprod]; exact hpow)
  have hstartRow (ω : Ω) :
      fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t := hstart ω i
  have hheatSmall (k : ℕ) (ω : Ω) (hk : k < q.stop ω) :
      ‖heatV q k ω i‖ ≤ 2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) :=
    heatV_norm_small q ht ht1 hc hKpos ω i k hk (hbroad ω) (hstartRow ω)
  have hZbound : ∀ k ω, ‖Z k ω‖ ≤ J0 := by
    intro k ω
    by_cases hk : k < q.stop ω
    · have hj := hrowJump k ω hk
      have hv := hheatSmall k ω hk
      have hstep : |Z k ω| ≤
          L * l * (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) + l / Real.sqrt t) := by
        calc
          |Z k ω| ≤ oneRowJump t L ‖heatV q k ω i‖ := by simpa [Z] using hj
          _ = L * l * (‖heatV q k ω i‖ + l / Real.sqrt t) := by
            simp [oneRowJump, l]
          _ ≤ _ := by gcongr
      have hsum :
          2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) + l / Real.sqrt t ≤
            (2 * Real.sqrt (K / c) + 1) * t ^ (1 / 4 : ℝ) := by
        calc
          _ ≤ 2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) + t ^ (1 / 4 : ℝ) :=
            add_le_add le_rfl hscale
          _ = _ := by ring
      have hbound : |Z k ω| ≤ J0 := by
        calc
          |Z k ω| ≤ L * l *
              (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) + l / Real.sqrt t) := hstep
          _ ≤ L * l * ((2 * Real.sqrt (K / c) + 1) * t ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = J0 := by dsimp [J0]; ring
      simpa [Z, Real.norm_eq_abs] using hbound
    · have hzero : Z k ω = 0 := by
        simp [Z, recordedLeverageIncrement, hk]
      simp [hzero, Real.norm_eq_abs]
      exact hJ0.le
  have hZsm : ∀ k, StronglyMeasurable (Z k) := by
    intro k
    exact (recordedLeverageIncrement_stronglyMeasurable q k i).mono
      (q.history.le (k + 1))
  have hZint : ∀ k, Integrable (Z k) μ := by
    intro k
    exact Integrable.of_bound (hZsm k).aestronglyMeasurable J0
      (Filter.Eventually.of_forall fun ω => hZbound k ω)
  have hvSM : ∀ k, StronglyMeasurable[q.history k] (variance k) := by
    intro k
    have hentry := pivotEntrySq_stronglyMeasurable q i k
    have hset := rowActiveRun_measurable q i k
    have hraw : Measurable[q.history k] (fun ω =>
        8 * L ^ 2 * l ^ 2 *
          (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) + l ^ 2 / t)) := by
      fun_prop
    unfold variance
    exact (Measurable.ite hset hraw measurable_const).stronglyMeasurable
  have hvpos : ∀ k ω, 0 ≤ variance k ω := by
    intro k ω
    by_cases hω : ω ∈ rowActiveRun q i k
    · have hU : 0 ≤ pivotEntrySq q i k ω := by rw [pivotEntrySq_eq]; positivity
      simp [variance, hω]
      positivity
    · simp [variance, hω]
  have hZlePred : ∀ k ω, |Z k ω| ≤
      L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
        l / Real.sqrt t) := by
    intro k ω
    by_cases hω : ω ∈ rowActiveRun q i k
    · have hE := hω
      rcases hω with ⟨hk, hi, hcore⟩
      obtain ⟨hx, -, -, -, -⟩ := q.heat k ω hk
      have hv := heatV_sq_le_initial_entry q ω k i hk hi (hbroad ω)
      rw [← pivotEntrySq_eq] at hv
      have hp : 0 ≤ C_H *
          (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) := by
        have hU : 0 ≤ pivotEntrySq q i k ω := by rw [pivotEntrySq_eq]; positivity
        positivity
      have hroot := le_sqrt_of_sq (‖heatV q k ω i‖)
        (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2))
        (norm_nonneg _) (by
          dsimp [C_H]
          nlinarith [hv])
      have hjump := hrowJump k ω hk
      simpa [Z, oneRowJump, l] using
        (calc
          |Z k ω| ≤ oneRowJump t L ‖heatV q k ω i‖ := hjump
          _ ≤ L * l *
              (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
                l / Real.sqrt t) := by
            unfold oneRowJump
            gcongr)
    · have hzero : Z k ω = 0 := by
        have hmask := recordedIncrement_rowActiveRun q i k
        dsimp [Z]
        rw [congrFun hmask ω]
        simp [hω]
      simp [hzero]
      positivity
  have hJk_le_J0 : ∀ k ω,
      (if ω ∈ rowActiveRun q i k then
        L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
          l / Real.sqrt t) else 0) ≤ J0 := by
    intro k ω
    by_cases hω : ω ∈ rowActiveRun q i k
    · rcases hω with ⟨hk, hi, hcore⟩
      have hRun : ω ∈ rowActiveRun q i k := ⟨hk, hi, hcore⟩
      have hU : pivotEntrySq q i k ω ≤ t ^ (1 / 2 : ℝ) := by
        rw [pivotEntrySq_eq]
        have hsingle : ‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 4 ≤
            fourthRow (scaledInverse t (g0 ω)) i := by
          unfold fourthRow
          exact Finset.single_le_sum
            (f := fun j => ‖scaledInverse t (g0 ω) i j‖ ^ 4) (s := Finset.univ)
            (fun j _ => by positivity) (Finset.mem_univ _)
        have hsingle' : (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2) ^ 2 ≤
            fourthRow (scaledInverse t (g0 ω)) i := by
          convert hsingle using 1 <;> ring
        have hroot := le_sqrt_of_sq (‖scaledInverse t (g0 ω) i (q.pivot k ω)‖ ^ 2)
          (fourthRow (scaledInverse t (g0 ω)) i) (by positivity) hsingle'
        calc
          _ ≤ Real.sqrt (fourthRow (scaledInverse t (g0 ω)) i) := hroot
          _ ≤ t ^ (1 / 2 : ℝ) := by
            calc
              _ ≤ Real.sqrt (t ^ (1 + delta)) := Real.sqrt_le_sqrt (by
                calc
                  _ ≤ (4 / 5) * fourthCap t := hstartRow ω
                  _ ≤ t ^ (1 + delta) := by
                    unfold fourthCap
                    have hnonneg : 0 ≤ t ^ (1 + delta) := Real.rpow_nonneg ht.le _
                    nlinarith)
              _ = t ^ ((1 + delta) / 2) := by
                rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
                congr 1
                ring
              _ ≤ t ^ (1 / 2 : ℝ) :=
                rpow_anti ht ht1 (by unfold delta; norm_num)
      have herr : (Real.sqrt t * entryBudget t) ^ 2 ≤ t ^ (1 / 2 : ℝ) := by
        rw [heatError_sq ht]
        exact rpow_anti ht ht1 (by norm_num [delta])
      have hsum : pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2 ≤
          2 * t ^ (1 / 2 : ℝ) := by
        calc
          _ ≤ t ^ (1 / 2 : ℝ) + t ^ (1 / 2 : ℝ) := add_le_add hU herr
          _ = _ := by ring
      have hroot :
          Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) ≤
            2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) := by
        have htargetSq :
            (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ)) ^ 2 =
              C_H * (2 * t ^ (1 / 2 : ℝ)) := by
          have hrpow : (t ^ (1 / 4 : ℝ)) ^ 2 = t ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
            congr 1
            norm_num
          calc
            (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ)) ^ 2 =
                4 * (Real.sqrt (K / c)) ^ 2 * (t ^ (1 / 4 : ℝ)) ^ 2 := by ring
            _ = 4 * (K / c) * t ^ (1 / 2 : ℝ) := by
              rw [Real.sq_sqrt (div_nonneg hKpos.le hc.le), hrpow]
            _ = C_H * (2 * t ^ (1 / 2 : ℝ)) := by dsimp [C_H]; ring
        have hsq :
            (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2))) ^ 2 ≤
              (2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ)) ^ 2 := by
          have hA0 : 0 ≤ C_H *
              (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) := by
            have hU0 : 0 ≤ pivotEntrySq q i k ω := by rw [pivotEntrySq_eq]; positivity
            positivity
          rw [Real.sq_sqrt hA0, htargetSq]
          exact mul_le_mul_of_nonneg_left hsum hCH.le
        have hroot' := le_sqrt_of_sq
          (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)))
          _ (Real.sqrt_nonneg _) hsq
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hroot'
        exact hroot'
      have hstep :
          Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
              l / Real.sqrt t ≤ (2 * Real.sqrt (K / c) + 1) * t ^ (1 / 4 : ℝ) := by
        calc
          _ ≤ 2 * Real.sqrt (K / c) * t ^ (1 / 4 : ℝ) + t ^ (1 / 4 : ℝ) :=
            add_le_add hroot hscale
          _ = _ := by ring
      calc
        _ = L * l *
            (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
              l / Real.sqrt t) := by simp [hRun]
        _ ≤ J0 := by
          calc
            _ ≤ L * l * ((2 * Real.sqrt (K / c) + 1) * t ^ (1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
            _ = J0 := by dsimp [J0]; ring
    · simp [hω]
      exact hJ0.le
  have hJkSM : ∀ k, StronglyMeasurable[q.history k] (fun ω =>
      if ω ∈ rowActiveRun q i k then
        L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
          l / Real.sqrt t) else 0) := by
    intro k
    have hU := pivotEntrySq_stronglyMeasurable q i k
    have hE := rowActiveRun_measurable q i k
    have hraw : Measurable[q.history k] (fun ω =>
        L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
          l / Real.sqrt t)) := by fun_prop
    exact (Measurable.ite hE hraw measurable_const).stronglyMeasurable
  have hJkInt : ∀ k, Integrable (fun ω =>
      if ω ∈ rowActiveRun q i k then
        L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
          l / Real.sqrt t) else 0) μ := by
    intro k
    have hSM := (hJkSM k).mono (q.history.le k)
    have hbound : ∀ ω, ‖(if ω ∈ rowActiveRun q i k then
        L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
          l / Real.sqrt t) else 0)‖ ≤ J0 := by
      intro ω
      by_cases hE : ω ∈ rowActiveRun q i k
      · have hnonneg : 0 ≤ L * l *
            (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
              l / Real.sqrt t) := by positivity
        rw [if_pos hE, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        simpa [hE] using hJk_le_J0 k ω
      · simp [hE]
        exact hJ0.le
    exact Integrable.of_bound hSM.aestronglyMeasurable J0
      (Filter.Eventually.of_forall hbound)
  have hZabsJk : ∀ k, ∀ ω,
      |Z k ω| ≤ if ω ∈ rowActiveRun q i k then
        L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
          l / Real.sqrt t) else 0 := by
    intro k ω
    by_cases hω : ω ∈ rowActiveRun q i k
    · simpa [hω] using hZlePred k ω
    · have hzero : Z k ω = 0 := by
        have hmask := recordedIncrement_rowActiveRun q i k
        dsimp [Z]
        rw [congrFun hmask ω]
        simp [hω]
      simp [hω, hzero]
  have hcondAbs : ∀ k, ∀ᵐ ω ∂μ,
      |μ[Z k | q.history k] ω| ≤
        if ω ∈ rowActiveRun q i k then
          L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
            l / Real.sqrt t) else 0 := by
    intro k
    let Jk : Ω → ℝ := fun ω => if ω ∈ rowActiveRun q i k then
      L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
        l / Real.sqrt t) else 0
    have hJkSM : StronglyMeasurable[q.history k] Jk := by simpa [Jk] using hJkSM k
    have hJkI := hJkInt k
    have hZint' := hZint k
    have hupper := condExp_mono (m := q.history k) hZint' hJkI (Eventually.of_forall fun ω => by
      have h := hZabsJk k ω
      exact le_trans (le_abs_self (Z k ω)) h)
    have hJnegInt : Integrable (-(fun ω => Jk ω)) μ := hJkI.neg
    have hlower := condExp_mono (m := q.history k) hJnegInt hZint' (Eventually.of_forall fun ω => by
      have h := hZabsJk k ω
      exact neg_le_of_abs_le h)
    have hJce_eq := condExp_of_stronglyMeasurable (q.history.le k) hJkSM hJkI
    have hJce : μ[(fun ω => Jk ω) | q.history k] =ᵐ[μ] Jk :=
      Filter.Eventually.of_forall (fun ω => congrFun hJce_eq ω)
    have hnegce : μ[-(fun ω => Jk ω) | q.history k] =ᵐ[μ] -μ[(fun ω => Jk ω) | q.history k] :=
      condExp_neg _ _
    filter_upwards [hupper, hlower, hJce, hnegce] with ω hu hl hJ hn
    have hu' : μ[Z k | q.history k] ω ≤ Jk ω := by simpa [Jk, hJ] using hu
    have hl' : -Jk ω ≤ μ[Z k | q.history k] ω := by simpa [Jk, hJ, hn] using hl
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hcenterBound : ∀ k, ∀ᵐ ω ∂μ,
      |Z k ω - μ[Z k | q.history k] ω| ≤ J := by
    intro k
    filter_upwards [hcondAbs k] with ω hc
    have hz := hZbound k ω
    have hz' : |Z k ω| ≤ J0 := by simpa [Z, Real.norm_eq_abs] using hz
    have hjk : (if ω ∈ rowActiveRun q i k then
        L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
          l / Real.sqrt t) else 0) ≤ J0 := hJk_le_J0 k ω
    have hsum := abs_sub (Z k ω) (μ[Z k | q.history k] ω)
    dsimp [J]
    dsimp [J0]
    linarith
  have hXSM : ∀ k, StronglyMeasurable (fun ω =>
      (Z k ω - μ[Z k | q.history k] ω) ^ 2) := by
    intro k
    have hcond : StronglyMeasurable[q.history k] (fun ω => μ[Z k | q.history k] ω) :=
      stronglyMeasurable_condExp
    exact ((hZsm k).sub (hcond.mono (q.history.le k))).pow 2
  have hvar : ∀ k, ∀ᵐ ω ∂μ,
      μ[(fun ω => (Z k ω - μ[Z k | q.history k] ω) ^ 2) | q.history k] ω ≤ variance k ω := by
    intro k
    let Jk : Ω → ℝ := fun ω => if ω ∈ rowActiveRun q i k then
      L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
        l / Real.sqrt t) else 0
    let X : Ω → ℝ := fun ω => Z k ω - μ[Z k | q.history k] ω
    let W : Ω → ℝ := fun ω => 4 * (Jk ω) ^ 2
    have hJkSM' : StronglyMeasurable[q.history k] Jk := by simpa [Jk] using hJkSM k
    have hJkSM0 : StronglyMeasurable Jk := hJkSM'.mono (q.history.le k)
    have hJkBound : ∀ ω, ‖Jk ω‖ ≤ J0 := by
      intro ω
      have hnonneg : 0 ≤ Jk ω := by
        by_cases hE : ω ∈ rowActiveRun q i k
        · simp [Jk, hE]; positivity
        · simp [Jk, hE]
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hJk_le_J0 k ω
    have hJk2I : Integrable (fun ω => Jk ω ^ 2) μ := by
      exact Integrable.of_bound (hJkSM0.pow 2).aestronglyMeasurable (J0 ^ 2)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hnonneg : 0 ≤ Jk ω := by
            by_cases hE : ω ∈ rowActiveRun q i k
            · simp [Jk, hE]; positivity
            · simp [Jk, hE]
          have hbound' : Jk ω ≤ J0 := by
            have h := hJkBound ω
            rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at h
            exact h
          have hsquare : (Jk ω) ^ 2 ≤ J0 ^ 2 := by
            have hprod := mul_nonneg (sub_nonneg.mpr hbound') (add_nonneg hJ0.le hnonneg)
            nlinarith [hprod]
          exact hsquare)
    have hWsm : StronglyMeasurable[q.history k] W := by
      dsimp [W]
      exact (hJkSM'.pow 2).const_mul 4
    have hWint : Integrable W μ := by
      dsimp [W]
      exact hJk2I.const_mul 4
    have hXint : Integrable (X ^ 2) μ := by
      apply Integrable.of_bound (hXSM k).aestronglyMeasurable (4 * J0 ^ 2)
      filter_upwards [hcenterBound k] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))]
      dsimp [X, J] at hω ⊢
      rcases abs_le.mp hω with ⟨hlo, hhi⟩
      nlinarith
    have hXleW : X ^ 2 ≤ᵐ[μ] W := by
      filter_upwards [Filter.Eventually.of_forall (hZabsJk k), hcondAbs k] with ω hZ hCE
      dsimp [X, W]
      have hnonneg : 0 ≤ Jk ω := by
        by_cases hE : ω ∈ rowActiveRun q i k
        · simp [Jk, hE]; positivity
        · simp [Jk, hE]
      have hZ' : |Z k ω| ≤ Jk ω := by simpa [Jk] using hZ
      have hCE' : |μ[Z k | q.history k] ω| ≤ Jk ω := by simpa [Jk] using hCE
      have hsub := abs_sub (Z k ω) (μ[Z k | q.history k] ω)
      have hpred : |Z k ω - μ[Z k | q.history k] ω| ≤ 2 * Jk ω := by
        calc
          _ ≤ |Z k ω| + |μ[Z k | q.history k] ω| := hsub
          _ ≤ Jk ω + Jk ω := add_le_add hZ' hCE'
          _ = 2 * Jk ω := by ring
      rcases abs_le.mp hpred with ⟨hlo, hhi⟩
      nlinarith [hlo, hhi, hnonneg]
    have hmono := condExp_mono (m := q.history k) hXint hWint hXleW
    have hWce_eq := condExp_of_stronglyMeasurable (q.history.le k) hWsm hWint
    have hWce : μ[W | q.history k] =ᵐ[μ] W :=
      Filter.Eventually.of_forall (fun ω => congrFun hWce_eq ω)
    have h4leVar : ∀ ω, W ω ≤ variance k ω := by
      intro ω
      by_cases hE : ω ∈ rowActiveRun q i k
      · have hA0 : 0 ≤ C_H *
            (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) := by
          have hU0 : 0 ≤ pivotEntrySq q i k ω := by rw [pivotEntrySq_eq]; positivity
          positivity
        have hB0 : 0 ≤ l / Real.sqrt t := by positivity
        have hsumSq :
            (Real.sqrt (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
              l / Real.sqrt t) ^ 2 ≤
              2 * (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) +
                (l / Real.sqrt t) ^ 2) := by
          have hsq : 0 ≤ (Real.sqrt (C_H *
              (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) -
              l / Real.sqrt t) ^ 2 := sq_nonneg _
          have hsqrt : (Real.sqrt (C_H *
              (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2))) ^ 2 =
              C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) :=
            Real.sq_sqrt hA0
          have heq : (Real.sqrt (C_H *
              (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
              l / Real.sqrt t) ^ 2 +
              (Real.sqrt (C_H *
                (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) -
                l / Real.sqrt t) ^ 2 =
              2 * (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) +
                (l / Real.sqrt t) ^ 2) := by
            calc (Real.sqrt (C_H *
                (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
                l / Real.sqrt t) ^ 2 +
                (Real.sqrt (C_H *
                  (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) -
                  l / Real.sqrt t) ^ 2
                  = 2 * ((Real.sqrt (C_H *
                    (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2))) ^ 2 +
                    (l / Real.sqrt t) ^ 2) := by ring
              _ = 2 * (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) +
                  (l / Real.sqrt t) ^ 2) := by rw [hsqrt]
          linarith
        have hdiv : (l / Real.sqrt t) ^ 2 = l ^ 2 / t := by
          rw [div_pow, Real.sq_sqrt ht.le]
        have hcoef : 0 ≤ 4 * (L * l) ^ 2 := by positivity
        have hJk_pos : Jk ω = L * l * (Real.sqrt (C_H *
            (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2)) +
            l / Real.sqrt t) := if_pos hE
        have hvar_pos : variance k ω = 8 * L ^ 2 * l ^ 2 *
            (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) + l ^ 2 / t) :=
          if_pos hE
        have hW_eq : W ω = 4 * (Jk ω) ^ 2 := rfl
        rw [hW_eq, hJk_pos, hvar_pos]
        calc
          4 * (L * l * (Real.sqrt (C_H * (pivotEntrySq q i k ω +
              (Real.sqrt t * entryBudget t) ^ 2)) + l / Real.sqrt t)) ^ 2 =
              4 * (L * l) ^ 2 *
                (Real.sqrt (C_H * (pivotEntrySq q i k ω +
                  (Real.sqrt t * entryBudget t) ^ 2)) + l / Real.sqrt t) ^ 2 := by ring
          _ ≤ 4 * (L * l) ^ 2 *
                (2 * (C_H * (pivotEntrySq q i k ω +
                  (Real.sqrt t * entryBudget t) ^ 2) + (l / Real.sqrt t) ^ 2)) :=
                mul_le_mul_of_nonneg_left hsumSq hcoef
          _ = 8 * L ^ 2 * l ^ 2 *
                (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) + l ^ 2 / t) := by
            rw [hdiv]; ring
      · simp [W, Jk, variance, hE]
    filter_upwards [hmono, hWce] with ω hm hW
    have hle := h4leVar ω
    rw [hW] at hm
    exact hm.trans hle
  have hbias : ∀ᵐ ω ∂μ,
      ∑ k ∈ Finset.range (heatLimit t), |μ[Z k | q.history k] ω| ≤ l / 4 := by
    have hsingle : ∀ k, ∀ᵐ ω ∂μ,
        |μ[Z k | q.history k] ω| ≤
          if ω ∈ rowActiveRun q i k then oneRowBias d t L ‖heatV q k ω i‖ else 0 := by
      intro k
      let E := rowActiveRun q i k
      have hmask := recordedIncrement_rowActiveRun q i k
      have hEmeas := rowActiveRun_measurable q i k
      have hCEmask : μ[Z k | q.history k] =ᵐ[μ]
          E.indicator (fun ω => μ[Z k | q.history k] ω) := by
        have hce := condExp_indicator (hZint k) hEmeas
        have hmaskZ : Z k =ᵐ[μ] E.indicator (Z k) := by
          have hEq : Z k = E.indicator (Z k) := by simpa [Z, E] using hmask
          exact Filter.Eventually.of_forall fun ω => congrFun hEq ω
        have hce' := condExp_congr_ae (m := q.history k) hmaskZ
        exact hce'.trans hce
      filter_upwards [hrowBias k, hCEmask] with ω hbiasω hmaskω
      by_cases hE : ω ∈ E
      · have hrun := hE.1
        simpa [E, hE] using hbiasω hrun
      · have hzero : μ[Z k | q.history k] ω = 0 := by simpa [E, hE] using hmaskω
        simp [E, hE, hzero]
    have hsingleAll : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range (heatLimit t),
        |μ[Z k | q.history k] ω| ≤
          if ω ∈ rowActiveRun q i k then oneRowBias d t L ‖heatV q k ω i‖ else 0 := by
      rw [eventually_all_finset]
      intro k hk
      exact hsingle k
    filter_upwards [hsingleAll] with ω hall
    let S : Finset ℕ := (Finset.range (heatLimit t)).filter
      (fun k => ω ∈ rowActiveRun q i k)
    have hsumBound : ∑ k ∈ Finset.range (heatLimit t),
        |μ[Z k | q.history k] ω| ≤
        ∑ k ∈ Finset.range (heatLimit t),
          if ω ∈ rowActiveRun q i k then oneRowBias d t L ‖heatV q k ω i‖ else 0 :=
      Finset.sum_le_sum fun k hk => hall k hk
    have hsumEq :
        (∑ k ∈ Finset.range (heatLimit t),
          (if ω ∈ rowActiveRun q i k then oneRowBias d t L ‖heatV q k ω i‖ else 0)) =
          (∑ k ∈ S, oneRowBias d t L ‖heatV q k ω i‖) := by
      dsimp [S]
      rw [Finset.sum_filter]
    have hSsubset : S ⊆ (Finset.range (q.stop ω)).filter
        (fun k => i ∈ (q.state k ω).active) := by
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkN, hkE⟩
      rcases hkE with ⟨hkstop, hi, -⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkstop, hi⟩
    have hSenergy : ∑ k ∈ S, ‖heatV q k ω i‖ ^ 2 ≤
        (4 * (K / c)) * t ^ ((27 / 100) * delta) := by
      calc
        _ ≤ ∑ k ∈ (Finset.range (q.stop ω)).filter
            (fun k => i ∈ (q.state k ω).active), ‖heatV q k ω i‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsubset (by
            intro k hk hkn
            positivity)
        _ ≤ _ := running_heatV_energy_small q ht ht1 hc hK ω i (hbroad ω) (hstart ω i)
    have hScard : (S.card : ℝ) ≤ heatLimit t := by
      have hcard := Finset.card_le_card (show S ⊆ Finset.range (heatLimit t) by
        intro k hk
        exact (Finset.mem_filter.mp hk).1)
      simpa using hcard
    have hBias := hBiasSmall S (fun k => ‖heatV q k ω i‖)
      (fun k => norm_nonneg _) hScard hSenergy
    rw [hsumEq] at hsumBound
    exact hsumBound.trans (by dsimp [l]; exact hBias)
  let Avar : ℝ := 8 * L ^ 2 * (2 * C_H + 1)
  have hbudget : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range (heatLimit t), variance k ω ≤ V := by
    filter_upwards [] with ω
    let S : Finset ℕ := (Finset.range (heatLimit t)).filter
      (fun k => ω ∈ rowActiveRun q i k)
    have hsumRewrite : ∑ k ∈ Finset.range (heatLimit t), variance k ω =
        ∑ k ∈ S, 8 * L ^ 2 * l ^ 2 *
          (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) + l ^ 2 / t) := by
      dsimp [variance, S]
      rw [Finset.sum_filter]
    have hSsubset : S ⊆ Finset.range (q.stop ω) := by
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkN, hkE⟩
      exact Finset.mem_range.mpr hkE.1
    have hEntry : ∑ k ∈ S,
        (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) ≤
          2 * t ^ ((27 / 100) * delta) := by
      calc
        _ ≤ ∑ k ∈ Finset.range (q.stop ω),
            (pivotEntrySq q i k ω +
              (Real.sqrt t * entryBudget t) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsubset
          intro k hk hkn
          have hpivot : 0 ≤ pivotEntrySq q i k ω := by rw [pivotEntrySq_eq]; positivity
          exact add_nonneg hpivot (sq_nonneg _)
        _ ≤ _ := by
          simpa [pivotEntrySq_eq] using
            (running_entry_energy_small q ht ht1 ω i (hstart ω i))
    have hScard : (S.card : ℝ) ≤ heatLimit t := by
      have hcard : S.card ≤ heatLimit t := by
        simpa using Finset.card_le_card (show S ⊆ Finset.range (heatLimit t) by
          intro k hk
          exact (Finset.mem_filter.mp hk).1)
      exact_mod_cast hcard
    have hconst : (S.card : ℝ) * (l ^ 2 / t) ≤
        t ^ ((27 / 100) * delta) := by
      calc
        (S.card : ℝ) * (l ^ 2 / t) ≤ (heatLimit t : ℝ) * (l ^ 2 / t) :=
          mul_le_mul_of_nonneg_right hScard (div_nonneg (sq_nonneg _) ht.le)
        _ = ((heatLimit t : ℝ) * l ^ 2) / t := by ring
        _ ≤ t ^ ((27 / 100) * delta) := by simpa [l] using hmargin
    rw [hsumRewrite]
    calc
      ∑ k ∈ S, 8 * L ^ 2 * l ^ 2 *
          (C_H * (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) + l ^ 2 / t)
          = 8 * L ^ 2 * l ^ 2 *
            (C_H * ∑ k ∈ S,
                (pivotEntrySq q i k ω + (Real.sqrt t * entryBudget t) ^ 2) +
              (S.card : ℝ) * (l ^ 2 / t)) := by
                rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
                simp [Finset.sum_const, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ 8 * L ^ 2 * l ^ 2 *
          (C_H * (2 * t ^ ((27 / 100) * delta)) + t ^ ((27 / 100) * delta)) := by
            gcongr
      _ = V := by dsimp [V, Avar, C_V, C_H, a]; ring
  have hJle : J ≤ 2 * J0 := by rfl
  have htail := AndersonAC.S6.two_sided_stream_tail μ q.history cConc l J V
    (heatLimit t) Z variance hl hJ hV hconc
    (fun k => recordedLeverageIncrement_stronglyMeasurable q k i)
    hZint hbias hvSM (fun k ω => hvpos k ω)
    (by
      intro k
      filter_upwards [hcenterBound k] with ω hω
      dsimp [J]
      exact hω)
    hvar hbudget
  -- The variance and jump scales give a stretched exponential with exponent 0.27δ.
  have hC1 : 0 < 1 / (16 * C_V) := by positivity
  have hC2 : 0 < 1 / (4 * C_J) := by positivity
  have hmin :
      min (l ^ 2 / (16 * V)) (l / (4 * J)) ≥
        min (1 / (16 * C_V)) (1 / (4 * C_J)) * t ^ (-a) := by
    have hvarRatio : l ^ 2 / (16 * V) = (1 / (16 * C_V)) * t ^ (-a) := by
      dsimp [V]
      have hta : 0 < t ^ a := Real.rpow_pos_of_pos ht _
      calc
        l ^ 2 / (16 * (C_V * l ^ 2 * t ^ a)) = 1 / (16 * C_V * t ^ a) := by
          field_simp [hCV.ne', hl.ne', hta.ne']
        _ = (1 / (16 * C_V)) * t ^ (-a) := by
          rw [Real.rpow_neg ht.le]
          field_simp [hCV.ne', hta.ne']
    have hjumpRatio : l / (4 * J) = (1 / (4 * C_J)) * t ^ (-(1 / 4 : ℝ)) := by
      dsimp [J, J0, C_J]
      calc
        l / (4 * (2 * (L * l * (2 * Real.sqrt (K / c) + 1) * t ^ (1 / 4 : ℝ)))) =
            1 / (4 * (2 * L * (2 * Real.sqrt (K / c) + 1) * t ^ (1 / 4 : ℝ))) := by
              field_simp [hL.ne', hl.ne']
        _ = (1 / (4 * (2 * L * (2 * Real.sqrt (K / c) + 1)))) *
            t ^ (-(1 / 4 : ℝ)) := by
              rw [Real.rpow_neg ht.le]
              field_simp [hL.ne', (Real.rpow_pos_of_pos ht (1 / 4 : ℝ)).ne'] <;> ring
    have hexp : -(1 / 4 : ℝ) ≤ -a := by norm_num [a, delta]
    have hpow : t ^ (-a) ≤ t ^ (-(1 / 4 : ℝ)) :=
      rpow_anti ht ht1 hexp
    rw [hvarRatio, hjumpRatio]
    apply le_min
    · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg ht.le _)
    · calc
        min (1 / (16 * C_V)) (1 / (4 * C_J)) * t ^ (-a) ≤
            (1 / (4 * C_J)) * t ^ (-a) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg ht.le _)
        _ ≤ (1 / (4 * C_J)) * t ^ (-(1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
  have htail' : ∀ᵐ ω ∂μ,
      conditionalProbability μ (q.history 0)
        {ω | ∃ s ≤ heatLimit t, l / 2 < |∑ k ∈ Finset.range s, Z k ω|} ω ≤
        (4 : ℝ) * Real.exp (-(cConc * min (1 / (16 * C_V)) (1 / (4 * C_J))) * t ^ (-a)) := by
    filter_upwards [htail] with ω hω
    have hexp := mul_le_mul_of_nonneg_left hmin hcConc.le
    have hexp' : (cConc * min (1 / (16 * C_V)) (1 / (4 * C_J))) * t ^ (-a) ≤
        cConc * min (l ^ 2 / (16 * V)) (l / (4 * J)) := by
      rw [mul_assoc]
      exact hexp
    apply hω.trans
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp.mpr
      simpa [neg_mul] using neg_le_neg hexp'
    · positivity
  have hconst1 : 1 / (16 * C_V) =
      1 / (128 * L ^ 2 * (2 * (2 * (K / c)) + 1)) := by
    dsimp [C_V, C_H]
    congr 1
    ring
  have hconst2 : 1 / (4 * C_J) =
      1 / (8 * L * (2 * Real.sqrt (K / c) + 1)) := by
    dsimp [C_J]
    congr 1
    ring
  rw [hconst1, hconst2] at htail'
  simpa [Z, l, a] using htail'

end AndersonAC.AgentS6
