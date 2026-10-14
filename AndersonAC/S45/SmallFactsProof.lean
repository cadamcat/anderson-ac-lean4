import AndersonAC.S45.Definitions

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace AndersonAC.AgentS45

theorem final_suffix_diagonal_proof (η : ℝ) (ξ r : ℂ) :
    -((2 * η : ℝ) : ℂ) * r + (ξ + (η : ℂ) * r) = ξ - (η : ℂ) * r := by
  push_cast
  ring

theorem failed_tile_freshness_proof {I : Type*} (q : AndersonAC.S45.QueryHistory I)
    (T : Set I) (newQueries : Set (I × ℕ)) (hq : q.fresh)
    (hnew : ∀ i k, (i, k) ∈ newQueries → i ∈ T) :
    (q.failedTile T newQueries).fresh := by
  intro i hi k hk hmem
  rcases hi with ⟨hi, hiT⟩
  rcases Set.mem_or_mem_of_mem_union hmem with hold | hnewmem
  · exact hq i hi k hk hold
  · exact hiT (hnew i k hnewmem)

theorem successful_digit_freshness_proof {I : Type*} (q : AndersonAC.S45.QueryHistory I)
    (newQueries : Set (I × ℕ)) (hq : q.fresh)
    (hnew : ∀ i k, (i, k) ∈ newQueries → k = q.depth + 1) :
    ({ q with trueQueries := q.trueQueries ∪ newQueries, depth := q.depth + 1 }).fresh := by
  intro i hi k hk hmem
  change q.depth + 1 < k at hk
  rcases Set.mem_or_mem_of_mem_union hmem with hold | hnewmem
  · have hqk : q.depth < k := by omega
    exact hq i hi k hqk hold
  · have heq := hnew i k hnewmem
    omega

theorem finite_tiles_terminate_proof {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (μ : Measure Ω) (endless : T → Set Ω) (h : ∀ T, μ (endless T) = 0) :
    μ (⋃ T, endless T) = 0 := by
  exact measure_iUnion_null h

theorem continueIndicator_predictable_proof {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℕ mΩ) (ok : ℕ → Ω → Prop)
    (hok : ∀ k, MeasurableSet[ℱ k] {ω | ok k ω}) :
    ∀ k, StronglyMeasurable[ℱ k] (AndersonAC.S45.continueIndicator ok k) := by
  classical
  intro k
  have hset : MeasurableSet[ℱ k] {ω | ∀ j ≤ k, ok j ω} := by
    have hInter : MeasurableSet[ℱ k] (⋂ j : {j : ℕ // j ≤ k}, {ω | ok j.1 ω}) :=
      MeasurableSet.iInter fun j => (ℱ.mono j.2) {ω | ok j.1 ω} (hok j.1)
    convert hInter using 1 <;> ext ω <;> simp
  have hm : Measurable[ℱ k] (AndersonAC.S45.continueIndicator ok k) := by
    exact Measurable.ite hset measurable_const measurable_const
  exact hm.stronglyMeasurable

theorem normalized_digit_law_proof {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t w C : ℝ) (ξ : Ω → ℝ)
    (ht : 0 < t) (hw : 0 < w)
    (hξ : AndersonAC.S45.MomentLaw μ (w * t) C ξ) :
    AndersonAC.S45.MomentLaw μ t C (fun ω => ξ ω / Real.sqrt w) := by
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hswne : Real.sqrt w ≠ 0 := ne_of_gt hsw
  refine ⟨hξ.measurable.div_const _, ?_, ?_, ?_⟩
  · calc
      (∫ ω, ξ ω / Real.sqrt w ∂μ) = (∫ ω, ξ ω ∂μ) / Real.sqrt w := integral_div _ _
      _ = 0 := by rw [hξ.mean]; simp
  · have hpoint : ∀ ω, (ξ ω / Real.sqrt w) ^ 2 = (1 / w) * (ξ ω) ^ 2 := by
      intro ω
      calc
        (ξ ω / Real.sqrt w) ^ 2 = (ξ ω) ^ 2 / (Real.sqrt w) ^ 2 := by rw [div_pow]
        _ = (ξ ω) ^ 2 / w := by rw [Real.sq_sqrt (le_of_lt hw)]
        _ = (1 / w) * (ξ ω) ^ 2 := by ring
    calc
      (∫ ω, (ξ ω / Real.sqrt w) ^ 2 ∂μ) = ∫ ω, (1 / w) * (ξ ω) ^ 2 ∂μ := by
        congr 1
        funext ω
        exact hpoint ω
      _ = (1 / w) * ∫ ω, (ξ ω) ^ 2 ∂μ := integral_const_mul _ _
      _ = t := by rw [hξ.variance]; field_simp
  · filter_upwards [hξ.bounded] with ω hω
    calc
      |ξ ω / Real.sqrt w| = |ξ ω| / Real.sqrt w := by rw [abs_div, abs_of_pos hsw]
      _ ≤ (C * Real.sqrt (w * t)) / Real.sqrt w :=
        div_le_div_of_nonneg_right hω (le_of_lt hsw)
      _ = C * Real.sqrt t := by
        rw [Real.sqrt_mul (le_of_lt hw) t]
        field_simp [hswne]

theorem harmonic_slots_proof (M : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.range M, (1 : ℝ) / (M - k : ℕ)) ≤ 1 + Real.log M := by
  let f : ℕ → ℝ := fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ)
  have hsum : (∑ k ∈ Finset.range M, (1 : ℝ) / (M - k : ℕ)) = (harmonic M : ℝ) := by
    calc
      (∑ k ∈ Finset.range M, (1 : ℝ) / (M - k : ℕ)) =
          ∑ k ∈ Finset.range M, f (M - 1 - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [f]
        have hk' : k < M := Finset.mem_range.mp hk
        congr 1
        congr 1
        omega
      _ = ∑ k ∈ Finset.range M, f k := Finset.sum_range_reflect f M
      _ = (harmonic M : ℝ) := by
        simp [f, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hsum]
  exact harmonic_le_one_add_log M

theorem endpoint_margin_proof : ∀ (C : ℝ), 0 < C → ∃ t0 > 0, ∀ t θ : ℝ,
    0 < t → t < t0 → 1 / 4 ≤ θ → θ ≤ 5 / 8 →
    (θ^2 + C * AndersonAC.S45.power t (AndersonAC.S45.delta / 2000)) *
        AndersonAC.S45.rowCap t <
      (7 / 10 : ℝ) * AndersonAC.S45.rowCap (θ * t) ∧
    θ * AndersonAC.S45.power t AndersonAC.S45.kappa <
      AndersonAC.S45.power (θ * t) AndersonAC.S45.kappa := by
  intro C hC
  let ε : ℝ := AndersonAC.S45.delta / 2000
  let e : ℝ := 1 + AndersonAC.S45.delta
  let q : ℝ := 1 - AndersonAC.S45.delta
  let b : ℝ := 1 / (3200 * (C + 1))
  let t0 : ℝ := AndersonAC.S45.power b ε⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have ht0 : 0 < t0 := by
    dsimp [t0, AndersonAC.S45.power]
    exact Real.rpow_pos_of_pos hb _
  have heps : 0 < ε := by dsimp [ε, AndersonAC.S45.delta]; norm_num
  have ht0pow : AndersonAC.S45.power t0 ε = b := by
    change Real.rpow (Real.rpow b ε⁻¹) ε = b
    exact Real.rpow_inv_rpow hb.le heps.ne'
  have hden : 0 < 3200 * (C + 1) := by positivity
  have hCb : C * b < 1 / 3200 := by
    calc
      C * b = C / (3200 * (C + 1)) := by dsimp [b]; ring
      _ < 1 / 3200 := by
        apply (div_lt_iff₀ hden).2
        nlinarith [hC]
  have hCgap : C * b < 1 / 1600 := by linarith
  have hδ : AndersonAC.S45.delta = (1 : ℝ) / 100 := by norm_num [AndersonAC.S45.delta]
  have hq : q = 99 / 100 := by dsimp [q]; rw [hδ]; norm_num
  have he : e = 101 / 100 := by dsimp [e]; rw [hδ]; norm_num
  have hκ : AndersonAC.S45.kappa = (1 : ℝ) / 20000 := by
    norm_num [AndersonAC.S45.kappa, AndersonAC.S45.delta]
  refine ⟨t0, ht0, ?_⟩
  intro t θ ht htt hθlo hθhi
  have hθpos : 0 < θ := by linarith
  have hθlt1 : θ < 1 := by linarith
  have htErr : C * AndersonAC.S45.power t ε < 1 / 1600 := by
    have hpow : AndersonAC.S45.power t ε < b := by
      calc
        AndersonAC.S45.power t ε < AndersonAC.S45.power t0 ε :=
          Real.rpow_lt_rpow ht.le htt heps
        _ = b := ht0pow
    calc
      C * AndersonAC.S45.power t ε < C * b := mul_lt_mul_of_pos_left hpow hC
      _ < 1 / 1600 := hCgap
  have hqexp : θ ^ q ≤ θ ^ (4 / 5 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_ge hθpos (by linarith)
    rw [hq]
    norm_num
  have hqbase : θ ^ (4 / 5 : ℝ) ≤ (5 / 8 : ℝ) ^ (4 / 5 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hθhi (by norm_num)
  have hroot5 : (5 / 8 : ℝ) ^ (4 / 5 : ℝ) < 69 / 100 := by
    apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by norm_num : 0 < (5 : ℝ))).1
    calc
      ((5 / 8 : ℝ) ^ (4 / 5 : ℝ)) ^ (5 : ℝ) = (5 / 8 : ℝ) ^ 4 := by
        rw [← Real.rpow_mul (by norm_num) (4 / 5 : ℝ) (5 : ℝ)]
        norm_num
      _ < (69 / 100 : ℝ) ^ (5 : ℝ) := by norm_num
  have hqbound : θ ^ q < 69 / 100 := lt_of_le_of_lt (le_trans hqexp hqbase) hroot5
  have heq : e + q = 2 := by rw [he, hq]; norm_num
  have hθpowidentity : θ ^ e * θ ^ q = θ ^ 2 := by
    rw [← Real.rpow_add hθpos, heq]
    norm_num [Real.rpow_natCast]
  have hθpowlower : (1 / 16 : ℝ) ≤ θ ^ e := by
    have hθsq : (1 / 4 : ℝ) ^ 2 ≤ θ ^ 2 := by nlinarith
    have hexp : θ ^ 2 ≤ θ ^ e := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (x := θ) (y := (2 : ℝ)) (z := e)
        hθpos (by linarith) (by rw [he]; norm_num)
    nlinarith [hθsq, hexp]
  have hfactor : (1 / 100 : ℝ) < (7 / 10 : ℝ) - θ ^ q := by linarith
  have hgap : (1 / 1600 : ℝ) < θ ^ e * ((7 / 10 : ℝ) - θ ^ q) := by
    calc
      (1 / 1600 : ℝ) = (1 / 16 : ℝ) * (1 / 100 : ℝ) := by norm_num
      _ ≤ θ ^ e * (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hθpowlower (by norm_num)
      _ < θ ^ e * ((7 / 10 : ℝ) - θ ^ q) :=
        mul_lt_mul_of_pos_left hfactor (Real.rpow_pos_of_pos hθpos e)
  have hbasegap : θ ^ 2 + 1 / 1600 < (7 / 10 : ℝ) * θ ^ e := by
    have hdiff : (7 / 10 : ℝ) * θ ^ e - θ ^ 2 =
        θ ^ e * ((7 / 10 : ℝ) - θ ^ q) := by
      rw [← hθpowidentity]
      ring
    linarith
  have hcoef : θ ^ 2 + C * AndersonAC.S45.power t ε < (7 / 10 : ℝ) * θ ^ e := by
    linarith
  have hmain := mul_lt_mul_of_pos_right hcoef (Real.rpow_pos_of_pos ht e)
  have hsmall :
      (θ ^ 2 + C * AndersonAC.S45.power t ε) * AndersonAC.S45.rowCap t <
        (7 / 10 : ℝ) * AndersonAC.S45.rowCap (θ * t) := by
    simpa [AndersonAC.S45.rowCap, AndersonAC.S45.power,
      Real.mul_rpow (le_of_lt hθpos) (le_of_lt ht), mul_assoc] using hmain
  have htheta : θ < θ ^ AndersonAC.S45.kappa :=
    Real.self_lt_rpow_of_lt_one hθpos hθlt1 (by rw [hκ]; norm_num)
  have htκ : 0 < AndersonAC.S45.power t AndersonAC.S45.kappa :=
    Real.rpow_pos_of_pos ht AndersonAC.S45.kappa
  have hsmallθ := mul_lt_mul_of_pos_right htheta htκ
  have hθt : AndersonAC.S45.power (θ * t) AndersonAC.S45.kappa =
      AndersonAC.S45.power θ AndersonAC.S45.kappa * AndersonAC.S45.power t AndersonAC.S45.kappa :=
    by
      change Real.rpow (θ * t) AndersonAC.S45.kappa =
        Real.rpow θ AndersonAC.S45.kappa * Real.rpow t AndersonAC.S45.kappa
      exact Real.mul_rpow (le_of_lt hθpos) (le_of_lt ht)
  refine ⟨hsmall, ?_⟩
  rw [hθt]
  simpa [AndersonAC.S45.power] using hsmallθ

end AndersonAC.AgentS45
