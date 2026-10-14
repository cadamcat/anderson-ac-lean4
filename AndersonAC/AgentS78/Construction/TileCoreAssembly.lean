import AndersonAC.AgentS78.Construction.TileCore
import AndersonAC.AgentS78.Construction.TileTrialFirst
import AndersonAC.S45.RawBoundsProof
import AndersonAC.S45.TrialInputsFinal

/-!
# WP10 construction, C4a core: assembly of the pieces A0–A3

`tileCrossing_of_pieces`: A0 (slot description), A1 (uniform slot law), A2 (monitor bounds)
and A3 (failure crosses a budget) give `TileCrossingStatement`, through
`AgentS45.ordered_raw_bounds_proof` and `AgentS45.ordered_trial_inputs_proof`
(05:766–870).
-/

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

/-- `UniformSlotLaw` is monotone in its constant. -/
theorem uniformSlotLaw_mono {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    {μ : Measure Ω} {ℱ : Filtration ℕ mΩ} {M : ℕ} {t C C' : ℝ} {run : ℕ → Ω → Bool}
    {remaining : ℕ → Ω → Finset I} {slot : ℕ → Ω → I} {ξ : ℕ → Ω → ℝ}
    (h : S45.UniformSlotLaw μ ℱ M t C run remaining slot ξ) (hC : C ≤ C') :
    S45.UniformSlotLaw μ ℱ M t C' run remaining slot ξ where
  run_predictable := h.run_predictable
  remaining_measurable := h.remaining_measurable
  slot_adapted := h.slot_adapted
  scalar_adapted := h.scalar_adapted
  nonempty := h.nonempty
  bounded k hk := by
    filter_upwards [h.bounded k hk] with ω hω hr
    exact (hω hr).trans (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
  uniform := h.uniform
  mean := h.mean
  variance := h.variance

theorem logFactor_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 0 ≤ S45.logFactor t := by
  unfold S45.logFactor
  have : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  linarith

theorem power_nonneg_asm (t e : ℝ) (ht : 0 ≤ t) : 0 ≤ S45.power t e := by
  unfold S45.power; exact Real.rpow_nonneg ht e

theorem monitorJump_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k : S45.MonitorKind) :
    0 ≤ S45.monitorJump t k := by
  have hl := logFactor_nonneg ht ht1
  cases k <;> simp only [S45.monitorJump] <;>
    first
    | exact mul_nonneg hl (power_nonneg_asm _ _ ht.le)
    | exact power_nonneg_asm _ _ ht.le

theorem monitorVariance_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k : S45.MonitorKind) :
    0 ≤ S45.monitorVariance t k := by
  have hl := logFactor_nonneg ht ht1
  cases k <;> simp only [S45.monitorVariance] <;>
    first
    | exact mul_nonneg (pow_nonneg hl _) (power_nonneg_asm _ _ ht.le)
    | exact mul_nonneg hl (power_nonneg_asm _ _ ht.le)

theorem monitorBias_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k : S45.MonitorKind) :
    0 ≤ S45.monitorBias t k := by
  have hl := logFactor_nonneg ht ht1
  have hp := fun e => power_nonneg_asm t e ht.le
  cases k <;> simp only [S45.monitorBias]
  · exact add_nonneg (mul_nonneg (pow_nonneg hl _) (add_nonneg (hp _) (Real.sqrt_nonneg _)))
      (mul_nonneg (pow_nonneg hl _) (hp _))
  · exact mul_nonneg hl (hp _)
  · exact mul_nonneg hl (hp _)

/-- `TrialInputs` is monotone in its constant (for `0 < t ≤ 1`). -/
def trialInputs_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {s d : ℕ} {t C C' : ℝ}
    (a : S45.TrialInputs μ ℱ s d t C) (hC : C ≤ C') (ht : 0 < t) (ht1 : t ≤ 1) :
    S45.TrialInputs μ ℱ s d t C' where
  kind := a.kind
  dimension := a.dimension
  raw := a.raw
  envelope := a.envelope
  differences i :=
    { (a.differences i) with
      jump := fun k => by
        filter_upwards [(a.differences i).jump k] with ω hω
        exact hω.trans (mul_le_mul_of_nonneg_right hC (monitorJump_nonneg ht ht1 _))
      total_variance := fun n => by
        filter_upwards [(a.differences i).total_variance n] with ω hω
        exact hω.trans (mul_le_mul_of_nonneg_right hC (monitorVariance_nonneg ht ht1 _)) }
  drift i N := by
    filter_upwards [a.drift i N] with ω hω
    exact hω.trans (mul_le_mul_of_nonneg_right hC (monitorBias_nonneg ht ht1 _))
  dimensions := a.dimensions.trans
    (mul_le_mul_of_nonneg_right hC (power_nonneg_asm _ _ ht.le))

/-- The empty `TrialInputs` (no monitor). -/
def trialInputs_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (d : ℕ) (t C : ℝ) (hC : 0 ≤ C) (ht : 0 ≤ t) :
    S45.TrialInputs μ ℱ 0 d t C where
  kind i := i.elim0
  dimension i := i.elim0
  raw i := i.elim0
  envelope i := i.elim0
  differences i := i.elim0
  drift i := i.elim0
  dimensions := by simpa using mul_nonneg hC (power_nonneg_asm t _ ht)

/-- Transfer of a crossing through `HEq` raw increments of a common dimension. -/
theorem crossing_of_heq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {s d D : ℕ} {t C : ℝ}
    (b : S45.TrialInputs μ ℱ s d t C) (kind : Fin s → S45.MonitorKind)
    (R : Fin s → ℕ → Ω → S45.CMat (Fin D)) (hk : b.kind = kind)
    (hd : b.dimension = fun _ => D) (hR : ∀ i k ω, HEq (b.raw i (k + 1) ω) (R i (k + 1) ω))
    (ω : Ω) (i : Fin s) (n : ℕ)
    (hcross : S45.monitorBudget t (kind i) < ‖S45.partialSum (R i) n ω‖) :
    ω ∈ b.crossing := by
  obtain ⟨bkind, bdim, braw, benv, bdiff, bdrift, bdims⟩ := b
  simp only at hk hd hR
  subst hk hd
  refine ⟨i, n, ?_⟩
  have : S45.partialSum (braw i) n ω = S45.partialSum (R i) n ω := by
    unfold S45.partialSum
    exact Finset.sum_congr rfl fun k _ => eq_of_heq (hR i k ω)
  simpa [S45.TrialInputs.crossing, this] using hcross

/-- The dimension count `s · D ≤ 30 C² t^{−12d}` of the padded monitors. -/
theorem monitor_dims_le {d m : ℕ} (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (hx : TileGoodCore C P j T x)
    (ht : 0 < sweepScale P.u m j) (ht1 : sweepScale P.u m j ≤ 1) :
    ((monitorCount P j T : ℝ) * (monitorDim P j T : ℝ)) ≤
      30 * C ^ 2 * (S45.power (sweepScale P.u m j) (-6 * (d : ℝ))) ^ 2 := by
  set X := S45.power (sweepScale P.u m j) (-6 * (d : ℝ)) with hX
  have hX1 : 1 ≤ X := by
    rw [hX]; unfold S45.power
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by nlinarith [(d.cast_nonneg : (0:ℝ) ≤ d)])
  have hC := hx.one_le
  have ha := hx.inner_card
  have hb : ((P.cover j).cover.dim T : ℝ) ≤ C * X :=
    ((P.cover j).cover.dimension T).trans (mul_le_mul_of_nonneg_right hx.cover_C (by linarith))
  have hs : (monitorCount P j T : ℝ) ≤ 5 * C * X := by
    unfold monitorCount; push_cast; nlinarith
  have hD : (monitorDim P j T : ℝ) ≤ 6 * C * X := by
    unfold monitorDim localDim; push_cast; nlinarith
  calc (monitorCount P j T : ℝ) * (monitorDim P j T : ℝ) ≤ (5 * C * X) * (6 * C * X) :=
        mul_le_mul hs hD (by positivity) (by positivity)
    _ = 30 * C ^ 2 * X ^ 2 := by ring

/-- `t^{−6(2d+1)} = (t^{−6d})² · t^{−6}`. -/
theorem power_split (t : ℝ) (ht : 0 < t) (d : ℕ) :
    S45.power t (-6 * ((2 * d + 1 : ℕ) : ℝ)) =
      (S45.power t (-6 * (d : ℝ))) ^ 2 * S45.power t (-6) := by
  unfold S45.power
  simp only [Real.rpow_eq_pow]
  rw [sq, ← Real.rpow_add ht, ← Real.rpow_add ht]
  congr 1; push_cast; ring

/-- **Assembly of the C4a core.** -/
theorem tileCrossing_of_pieces (d : ℕ) (C : ℝ) (hA0 : TileSlotDescriptionStatement)
    (hA1 : TileSlotLawStatement) (hA2 : TileMonitorBoundsStatement d C)
    (hA3 : TileFailCrossingStatement d C) : TileCrossingStatement d C := by
  obtain ⟨C₂, hC₂, t2, ht2, hA2⟩ := hA2
  obtain ⟨t3, ht3, hA3⟩ := hA3
  obtain ⟨C', hC', t1, ht1, hinp⟩ :=
    AgentS45.ordered_trial_inputs_proof (2 * d + 1) C₂ (by linarith)
  -- smallness for the dimension count: `t^6 ≤ C₂ / (30 C²)` (and `C ≤ C₂ t^{-6}`)
  set K : ℝ := C₂ / (30 * (max C 1) ^ 2) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨max C' 1, le_max_right _ _, min (min t1 t2) (min t3 (min (1 / 2) K)), ?_, ?_⟩
  · exact lt_min (lt_min ht1 ht2) (lt_min ht3 (lt_min (by norm_num) hKpos))
  intro m P j T M x hu hj hjm hM hab hx htsmall
  set t := sweepScale P.u m j with ht_def
  have htpos : 0 < t := sweepScale_pos_first (lt_trans (by norm_num) hu.1) m j
  have ht1' : t < t1 := lt_of_lt_of_le htsmall (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht2' : t < t2 := lt_of_lt_of_le htsmall (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht3' : t < t3 := lt_of_lt_of_le htsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hthalf : t < 1 / 2 := lt_of_lt_of_le htsmall
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htK : t < K := lt_of_lt_of_le htsmall
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have htle1 : t ≤ 1 := by linarith
  set ℱ := tileFiltration P j T M x
  -- the empty tile: no slot, no failure
  by_cases hN : slotCount P j T = 0
  · refine ⟨ℱ, 0, trialInputs_empty _ ℱ (2 * d + 1) t (max C' 1) (by positivity) htpos.le, ?_⟩
    intro ω hω
    rw [(hA0 d m P j T M x hM hab).1] at hω
    simp only [Set.mem_setOf_eq, hN] at hω
    simp [slotSeq] at hω
  have hNpos : 0 < slotCount P j T := Nat.pos_of_ne_zero hN
  obtain ⟨hrun, hmeas, hherm, hmean, hstack, hjump⟩ :=
    hA2 m P j T M x hu hj hjm hM hab hx ht2'
  have hlaw := uniformSlotLaw_mono (hA1 d m C P j T M x hu hj hjm hM hab hx
    (tileRun P j T M x) hrun) hC₂
  have hcount : ∀ k < slotCount P j T, ∀ ω, tileRun P j T M x k ω = true →
      (tileRemaining P j T M k ω).card = slotCount P j T - k :=
    fun k hk ω _ => (hA0 d m P j T M x hM hab).2 k hk.le ω
  obtain ⟨a, hak, had, haraw⟩ := AgentS45.ordered_raw_bounds_proof
    (sourcesLaw (Torus d m) M) ℱ (siteCount d m) (monitorCount P j T) (slotCount P j T) t C₂
    (monitorKind P j T) (fun _ => monitorDim P j T) (tileRun P j T M x) (tileRemaining P j T M)
    (tileSlotF P j T M) (tileXi P j T M x) (tileEval P j T M x) ⟨htpos, by linarith⟩
    (by linarith) hlaw hcount hmeas hherm hmean hstack hjump
  -- dimension and slot counts
  have hC1 : 1 ≤ C := hx.one_le
  have hX := power_split t htpos d
  set X := S45.power t (-6 * (d : ℝ)) with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]; unfold S45.power
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos htpos htle1
      (by nlinarith [(d.cast_nonneg : (0:ℝ) ≤ d)])
  have h6 : 30 * C ^ 2 ≤ C₂ * S45.power t (-6) := by
    have hmax : C ≤ max C 1 := le_max_left _ _
    have ht6 : t ^ 6 ≤ K := by
      have : t ^ 6 ≤ t := pow_le_of_le_one htpos.le htle1 (by norm_num)
      linarith
    have hp6 : S45.power t (-6) = (t ^ 6)⁻¹ := by
      unfold S45.power
      rw [Real.rpow_eq_pow, show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg htpos.le,
        Real.rpow_natCast]
    rw [hp6, hK] at *
    have ht6pos : 0 < t ^ 6 := by positivity
    rw [le_div_iff₀ (by positivity)] at ht6
    rw [← div_eq_mul_inv, le_div_iff₀ ht6pos]
    have : C ^ 2 ≤ (max C 1) ^ 2 := pow_le_pow_left₀ (by linarith) hmax 2
    nlinarith
  have hdims : (∑ i : Fin (monitorCount P j T), (a.dimension i : ℝ)) ≤
      C₂ * S45.power t (-6 * ((2 * d + 1 : ℕ) : ℝ)) := by
    rw [had]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have := monitor_dims_le C P j T x hx htpos htle1
    rw [hX]
    calc (monitorCount P j T : ℝ) * (monitorDim P j T : ℝ) ≤ 30 * C ^ 2 * X ^ 2 := this
      _ ≤ C₂ * S45.power t (-6) * X ^ 2 :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = C₂ * (X ^ 2 * S45.power t (-6)) := by ring
  have hMle : ((slotCount P j T : ℕ) : ℝ) ≤ C₂ * S45.power t (-6 * ((2 * d + 1 : ℕ) : ℝ)) := by
    rw [hX]
    have hcard := hx.tile_card
    have hCX : 1 ≤ C * X := one_le_mul_of_one_le_of_one_le hC1 hX1
    calc ((slotCount P j T : ℕ) : ℝ) ≤ C * X := hcard
      _ ≤ 30 * C ^ 2 * X ^ 2 := by nlinarith
      _ ≤ C₂ * S45.power t (-6) * X ^ 2 := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = C₂ * (X ^ 2 * S45.power t (-6)) := by ring
  obtain ⟨b, hbk, hbd, hbraw⟩ := hinp (RandomSources (Torus d m) M) (sourcesLaw (Torus d m) M) ℱ
    (monitorCount P j T) (slotCount P j T) t a htpos ht1' hNpos hMle hdims
  refine ⟨ℱ, monitorCount P j T, trialInputs_mono b (le_max_left _ _) htpos htle1, ?_⟩
  intro ω hω
  rw [(hA0 d m P j T M x hM hab).1] at hω
  obtain ⟨i, n, hcross⟩ := hA3 m P j T M x hu hj hjm hM hab hx ht3' ω hω
  refine crossing_of_heq (trialInputs_mono b (le_max_left _ _) htpos htle1) (monitorKind P j T)
    (tileRaw P j T M x) (hbk.trans hak) (hbd.trans had) ?_ ω i n hcross
  intro i k ω
  exact (hbraw i (k + 1) ω).trans (haraw i k ω)

end AndersonAC.AgentS78
