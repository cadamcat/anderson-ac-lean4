import AndersonAC.AgentS78.Construction.TilePhaseEnd
import AndersonAC.AgentS78.Construction.SweepSchur
import AndersonAC.AgentS78.SweepFromS45
import AndersonAC.AgentS78.SweepPrestate
import AndersonAC.AgentS78.Construction.SweepEndPositive
import AndersonAC.S45.DuplicationProof
import AndersonAC.AgentS78.Construction.SweepEndCompare

/-!
# Analytic sweep end

This proves the sweep-end statement in `TilePhaseEnd.lean:41`, which connects the
tile phase to the clearing phase. The argument uses the duplicated-port identity
(04-sweep.tex:190–228), local transfer (05-local-sweeps.tex:536–600), and
Proposition 4.9 (`S45.ordinary_sweep_endpoint`).

The hypotheses include stage bounds for the old endpoint, a pivot at every committed
step, and the physical identity of the post-sweep record. The first two support the
S45 endpoint estimate; the physical identity is needed for Combes–Thomas decay.

`sweepEndMapTheta_isDamped` gives the post-sweep damping. `SweepReserveRowStatement`
provides the final reserve-row bound. `SweepS45Facts` and `SweepTransportStatement`
give the sequence hypotheses and prefix validity. The cumulative Schur identity gives
per-step positivity. These facts yield `SweepFacts`, the initial comparison, and the
resolvent decay used by `sweepEnd_proof`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open scoped Matrix.Norms.L2Operator

variable {d m : ℕ}

/-! ## Scales of a digit sweep -/

section Scales

theorem stageScale_pred_eq {u : ℝ} {j m : ℕ} (hj : 1 ≤ j) :
    stageScale u (j - 1) m = 4 * (u / (4 : ℝ) ^ j) + u / (4 : ℝ) ^ m := by
  unfold stageScale
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

theorem sweepScale_digit {u : ℝ} {m j : ℕ} (hj : j ≤ m) :
    sweepScale u m j = stageScale u (j - 1) m := by
  unfold sweepScale; rw [if_neg (show ¬ IsFinalSweep m j by unfold IsFinalSweep; omega)]

theorem sweepTheta_digit {u : ℝ} {m j : ℕ} (hj : j ≤ m) :
    sweepTheta u m j = stageScale u j m / stageScale u (j - 1) m := by
  unfold sweepTheta; rw [if_neg (show ¬ IsFinalSweep m j by unfold IsFinalSweep; omega)]

/-- The digit-sweep facts used by the S45 join: `t = t_{j−1}`, `θ t = t_j`, `1/4 ≤ θ ≤ 5/8`. -/
theorem digitSweep_scales {u : ℝ} (hu : 0 < u) {m j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ m) :
    0 < stageScale u (j - 1) m ∧
    sweepTheta u m j * stageScale u (j - 1) m = stageScale u j m ∧
    1 / 4 ≤ sweepTheta u m j ∧ sweepTheta u m j ≤ 5 / 8 := by
  rw [sweepTheta_digit hj, stageScale_pred_eq hj1]
  have ha : 0 < u / (4 : ℝ) ^ j := by positivity
  have hb : 0 < u / (4 : ℝ) ^ m := by positivity
  have hba : u / (4 : ℝ) ^ m ≤ u / (4 : ℝ) ^ j :=
    div_le_div_of_nonneg_left hu.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hj)
  have hs : stageScale u j m = u / (4 : ℝ) ^ j + u / (4 : ℝ) ^ m := rfl
  rw [hs]
  set a := u / (4 : ℝ) ^ j
  set b := u / (4 : ℝ) ^ m
  have hden : 0 < 4 * a + b := by linarith
  refine ⟨hden, by field_simp, ?_, ?_⟩
  · rw [le_div_iff₀ hden]; linarith
  · rw [div_le_iff₀ hden]; linarith

theorem digitSweep_theta_pos {u : ℝ} (hu : 0 < u) {m j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ m) :
    0 < sweepTheta u m j ∧ sweepTheta u m j < 1 := by
  obtain ⟨-, -, h1, h2⟩ := digitSweep_scales hu hj1 hj
  constructor <;> linarith

end Scales

/-! ## The stage history gives the damped identity of the old endpoint

`BoundaryHist.damped` (identical statement) is now declared in TilePhaseRun.lean
; the duplicate was removed here at the merge. -/

/-! ## The active set after the sweep -/

section Damped

theorem sweepEndActive_eq {x : RunRecord d m}
    (hlive : ∀ p : Port d m, p ∈ (x.sweep.state x.sweep.length).live ↔
      p.1 ∈ x.endpoint.active ∧ p.2 = true) :
    sweepEndActive x = x.endpoint.active := by
  classical
  ext i
  simp only [sweepEndActive, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hlive ((i, true) : Port d m)).trans ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

end Damped

/-! ## The S45 join -/

section Join

open AndersonAC.S45 (splitPorts initialPorts reserves)

/-- **The transported sweep** (output of the transport package): the committed sweep of `x`,
restricted to the ports of the active sites and reindexed along `e : Fin n ≃ active`, satisfies
the sequence hypotheses of `S45.ordinary_sweep_endpoint` for `old = toS45 x.endpoint x.r e`, at
scale `t`, ratio `θ`, with reserve-row constant `C`. The final reserve block is that of
`x.sweep`. -/
def SweepS45Facts (C t θ : ℝ) (x : RunRecord d m) : Prop :=
  ∃ (n : ℕ) (e : Fin n ≃ x.endpoint.active) (q : S45.Sequence (initialPorts (Fin n))),
    q.wellFormed t ((splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e)).r ∧
    (q.state 0).live = Finset.univ ∧
    (q.state 0).g = ((splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e)).g ∧
    (q.state q.length).live = reserves ∧
    (∀ i k : Fin n, (q.state q.length).g (i, true) (k, true) =
      (x.sweep.state x.sweep.length).g (((e i).val, true) : Port d m)
        (((e k).val, true) : Port d m)) ∧
    (∀ k ≤ q.length,
      ((q.state k).state ((splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e)).r).g.IsSymm ∧
      ((q.state k).state ((splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e)).r).ward t) ∧
    (∀ k ≤ q.length, q.valid t ((splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e)).r
      (((splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e)).D t) k) ∧
    (∀ i, ((q.state q.length).ambient ((splitPorts (Fin n) θ).liftState
        (toS45 x.endpoint x.r e)).r).fourthRow t reserves (i, true) ≤
      (θ ^ 2 + C * S45.power t (S45.delta / 2000)) * S45.rowCap t)

/-- **The final reserve rows (contract, hard: 05:536–600, `local_transfer`).** At the end of a
digit sweep the reserve-port fourth rows of the committed state are at most
`(θ² + Crow t^{δ/2000}) rowCap t` (the last conclusion of `AgentS45.local_transfer_proof` on the
whole sweep record, blocks = the accepted tiles, `TraceTails` built as in
sweep transfer). Stated on the record itself (ambient ports), so that the transport is mechanical. -/
def SweepReserveRowStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
  ∃ Crow ≥ (1 : ℝ), ∃ t0 > (0 : ℝ), ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ)
    (Cb : ℝ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    ∀ i ∈ x.endpoint.active,
      ((x.sweep.state x.sweep.length).ambient (portR (sweepTheta u m j) x.r)).fourthRow
        (sweepScale u m j) reserves ((i, true) : Port d m) ≤
      (sweepTheta u m j ^ 2 + Crow * S45.power (sweepScale u m j) (S45.delta / 2000)) *
        S45.rowCap (sweepScale u m j)

/-- **The transport (contract, mechanical).** At the end of a digit sweep, the committed sweep
restricted to the ports of the active sites (`Sequence.restrictLive`) and
reindexed along some `e : Fin n ≃ active` satisfies `SweepS45Facts`: reindex of `wellFormed`,
start (`start_lift`, `start_live`), end (`live_end`), per-step symmetry/Ward (from the start by
`wellFormed_symm_ward`), validity at every prefix (`TileSweepCore.valid`; `stageD0` restricted to
the active ports is the D of the lifted old state, the endpoint being damped by `hist`), and the
reserve rows (fourth rows over reserves, masked entries vanish). The per-step positivity is
derived here (`AgentS78send.seq_step_positive`). -/
def SweepTransportStatement (d : ℕ) : Prop :=
  ∀ (C Cb Crow : ℝ) (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    (∀ i ∈ x.endpoint.active,
      ((x.sweep.state x.sweep.length).ambient (portR (sweepTheta u m j) x.r)).fourthRow
        (sweepScale u m j) reserves ((i, true) : Port d m) ≤
      (sweepTheta u m j ^ 2 + Crow * S45.power (sweepScale u m j) (S45.delta / 2000)) *
        S45.rowCap (sweepScale u m j)) →
    SweepS45Facts Crow (sweepScale u m j) (sweepTheta u m j) x

/-- The lifted old state at the sweep start: `‖K‖ ≤ 1/2` and broad port damping bounds. -/
theorem liftOld_facts {n : ℕ} (old : S45.State (Fin n)) (t θ Cs : ℝ) (hθ1 : 1 / 4 ≤ θ)
    (hθ2 : θ ≤ 5 / 8) (hCs : 0 < Cs)
    (hb : ∀ i, ‖old.r i‖ ≤ Cs ∧ 1 / Cs ≤ old.p i ∧ old.p i ≤ Cs)
    (hfix : ∀ i, old.g i i = old.r i) (hK : ‖old.K t‖ ≤ 1 / 3) :
    ‖((splitPorts (Fin n) θ).liftState old).K t‖ ≤ 1 / 2 ∧
    ∀ y, ‖((splitPorts (Fin n) θ).liftState old).r y‖ ≤ 2 * Cs ∧
      1 / (2 * Cs) ≤ (((splitPorts (Fin n) θ).liftState old).r y).im ∧
      (((splitPorts (Fin n) θ).liftState old).r y).im ≤ 2 * Cs := by
  have hdup := AgentS45.duplication_algebraic (splitPorts (Fin n) θ) old t
    (fun i => AgentS45.splitPorts_mass (by linarith) (by linarith) i) hfix
  refine ⟨by rw [hdup.2.2.1]; linarith, fun y => ?_⟩
  -- the squared weight is `√θ` or `√(1 − θ)`, in `[1/2, 1]`
  have hw : 1 / 2 ≤ (splitPorts (Fin n) θ).weight y ^ 2 ∧
      (splitPorts (Fin n) θ).weight y ^ 2 ≤ 1 := by
    have key : ∀ a : ℝ, 1 / 4 ≤ a → a ≤ 1 → 1 / 2 ≤ S45.power a (1 / 4) ^ 2 ∧
        S45.power a (1 / 4) ^ 2 ≤ 1 := by
      intro a ha1 ha2
      rw [AgentS45.quarter_sq (by linarith)]
      refine ⟨?_, Real.sqrt_le_one.mpr ha2⟩
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt ha1
    simp only [splitPorts]
    split_ifs
    · exact key θ hθ1 (by linarith)
    · exact key (1 - θ) (by linarith) (by linarith)
  obtain ⟨b1, b2, b3⟩ := hb y.1
  have hp : (((splitPorts (Fin n) θ).liftState old).r y).im =
      (splitPorts (Fin n) θ).weight y ^ 2 * old.p y.1 :=
    AgentS45.lift_p_entry (splitPorts (Fin n) θ) old y
  have hr : ‖((splitPorts (Fin n) θ).liftState old).r y‖ =
      (splitPorts (Fin n) θ).weight y ^ 2 * ‖old.r y.1‖ := by
    simp only [S45.PortMap.liftState, splitPorts, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hp0 : 0 < old.p y.1 := lt_of_lt_of_le (by positivity) b2
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]; nlinarith [norm_nonneg (old.r y.1)]
  · rw [hp]
    have : 1 / (2 * Cs) = 1 / 2 * (1 / Cs) := by ring
    rw [this]
    exact mul_le_mul hw.1 b2 (by positivity) (by nlinarith)
  · rw [hp]; nlinarith

theorem pivot_bit_of_ne_none {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ}
    {Cb : ℝ} {done : Finset (Fin (P.cover j).cover.count)} {x : RunRecord d m}
    (h : TileSweepCore C P j n₀ u E ρ Cb done x)
    (hpiv : ∀ k < x.sweep.length, x.sweep.pivot k ≠ none) :
    ∀ k < x.sweep.length, ∃ i, x.sweep.pivot k = some ((i, false) : Port d m) := by
  intro k hk
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hpiv k hk)
  refine ⟨y.1, ?_⟩
  rw [hy]
  exact congrArg some (Prod.ext rfl (h.bit_pivots k hk y hy))

/-- **The analytic sweep end, core part**: SweepFacts, the damped identity of the post-sweep
endpoint, its initial rows and lag (the fields `sweep`, `physical`, `initialRows`,
`initialLag` of `ClearPhaseData.ofSweep'`). Monotone in `Cb` and `CA`. -/
theorem sweepEnd_core (hT : SweepTransportStatement d) (hR : SweepReserveRowStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∃ Cb₀ > (0 : ℝ), ∃ CA₀ > (0 : ℝ), ∃ t0 > (0 : ℝ), ∀ Cb ≥ Cb₀, ∀ CA ≥ CA₀,
    ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    SweepFacts Cb (stageScale u (j - 1) m) (stageScale u j m) x.endpoint
      (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r ∧
    IsDampedEndpoint (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r (stageScale u j m) ∧
    (∀ i, rowFour (normalizedInverse (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint
      (stageScale u j m)) i ≤ 0.7 * stageScale u j m ^ (1 + delta)) ∧
    (∀ i ∈ (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint.active,
      ‖(sweepEndMapTheta (sweepTheta P.u m j) x).endpoint.g i i - x.r i‖ ≤
        CA * stageScale u j m ^ (0.42 * delta)) := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨Crow, hCrow, tT, htT, hR'⟩ := hR cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  set Cs : ℝ := max (max CP (1 / cP)) Crow with hCs_def
  have hCs1 : 1 ≤ Cs := le_trans hCrow (le_max_right _ _)
  obtain ⟨C', hC', ts, hts, hsw⟩ := sweep_from_S45 Cs hCs1
  obtain ⟨tP, htP, hscale⟩ := AgentS78send.exists_positiveScale (2 * Cs) (by linarith)
  refine ⟨max C' 1, lt_of_lt_of_le one_pos (le_max_right _ _), 4 * C', by linarith,
    min tT (min ts tP),
    lt_min htT (lt_min hts htP),
    fun Cb hCb CA hCA m n₀ u E ρ P j x hn hu' hu hnj hjm hsmall hSB hcore => ?_⟩
  have hpiv := hcore.pivots_some
  subst hn hu'
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  have hj1 : 1 ≤ j := by omega
  obtain ⟨ht, hθt, hθ1, hθ2⟩ := digitSweep_scales hu0 hj1 hjm
  obtain ⟨hθpos, hθlt⟩ := digitSweep_theta_pos hu0 hj1 hjm
  have hts_eq := sweepScale_digit (u := P.u) hjm
  set t := stageScale P.u (j - 1) m with ht_def
  set θ := sweepTheta P.u m j with hθ_def
  have hsmall' : t < ts := by
    rw [← hts_eq]; exact lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallP : t < tP := by
    rw [← hts_eq]; exact lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_right _ _))
  -- old endpoint: damped at `t_{j−1}`
  have hDo : IsDampedEndpoint x.endpoint x.r t := hcore.hist.damped (by omega)
  -- live set at the end and the active set of the post-sweep endpoint
  have hlive := hcore.live_end
  have hact : (sweepEndMapTheta θ x).endpoint.active = x.endpoint.active :=
    sweepEndActive_eq hlive
  -- post-sweep endpoint damped at `θ t`
  have hwf : x.sweep.wellFormed t (portR θ x.r) := by
    have := hcore.wellFormed; rwa [hts_eq] at this
  have hDs : IsDampedEndpoint (sweepEndMapTheta θ x).endpoint x.r (θ * t) :=
    sweepEndMapTheta_isDamped x x ht hθpos hθlt hDo rfl hwf hcore.start_lift
      (pivot_bit_of_ne_none hcore hpiv) hlive
  -- the transported sweep
  obtain ⟨n, e, q, h1, h2, h3, h4, h5, h6, h7, h9⟩ :=
    hT C Cb Crow m P.n₀ P.u E ρ P j x rfl rfl hu hnj hjm hcore
      (hR' m P.n₀ P.u E ρ P j Cb x rfl rfl hu hnj hjm (lt_of_lt_of_le hsmall (min_le_left _ _))
        hSB hcore)
  rw [hts_eq] at h1 h6 h7 h9
  -- old-state facts from the stage bounds
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := sweep_prestate (n₀ := P.n₀) x.endpoint x.r hcP hDo hu e hSB
  have hCmax : max CP (1 / cP) ≤ Cs := le_max_left _ _
  have hpos_max : 0 < max CP (1 / cP) := lt_of_lt_of_le hcP (le_trans hCP (le_max_left _ _))
  have hoS : ∀ i, (toS45 (sweepEndMapTheta θ x).endpoint x.r
        (e.trans (Equiv.subtypeEquivRight (fun y => by rw [hact])))).r i =
        (toS45 x.endpoint x.r e).r i ∧
      ‖(toS45 x.endpoint x.r e).r i‖ ≤ Cs ∧ 1 / Cs ≤ (toS45 x.endpoint x.r e).p i ∧
      (toS45 x.endpoint x.r e).p i ≤ Cs := by
    intro i
    obtain ⟨a1, a2, a3⟩ := p1 i
    refine ⟨rfl, a1.trans hCmax, le_trans ?_ a2, a3.trans hCmax⟩
    exact one_div_le_one_div_of_le hpos_max hCmax
  -- the final reserve block is `√θ` times the post-sweep matrix
  have hsq : (Real.sqrt θ : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθpos
    exact_mod_cast this.ne'
  have hend : ∀ i k : Fin n, (q.state q.length).g (i, true) (k, true) =
      Real.sqrt θ * (toS45 (sweepEndMapTheta θ x).endpoint x.r
        (e.trans (Equiv.subtypeEquivRight (fun y => by rw [hact])))).g i k := by
    intro i k
    rw [h5]
    have hi : (e i).val ∈ sweepEndActive x := by rw [sweepEndActive_eq hlive]; exact (e i).2
    have hk : (e k).val ∈ sweepEndActive x := by rw [sweepEndActive_eq hlive]; exact (e k).2
    simp only [toS45, Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe, sweepEndMapTheta,
      sweepEndMatrixTheta]
    rw [if_pos ⟨hi, hk⟩]
    field_simp
    rfl
  -- the reserve-row cap with the larger constant
  have hrow : ∀ i, ((q.state q.length).ambient ((splitPorts (Fin n) θ).liftState
        (toS45 x.endpoint x.r e)).r).fourthRow t reserves (i, true) ≤
      (θ ^ 2 + Cs * S45.power t (S45.delta / 2000)) * S45.rowCap t := by
    intro i
    refine (h9 i).trans ?_
    have hp : 0 ≤ S45.power t (S45.delta / 2000) := Real.rpow_nonneg ht.le _
    have hr : 0 ≤ S45.rowCap t := Real.rpow_nonneg ht.le _
    have : Crow ≤ Cs := le_max_right _ _
    exact mul_le_mul_of_nonneg_right (by nlinarith) hr
  -- per-step positivity from validity at every prefix
  have hCs0 : 0 < Cs := lt_of_lt_of_le one_pos hCs1
  obtain ⟨hK0, hbroad⟩ := liftOld_facts (toS45 x.endpoint x.r e) t θ Cs hθ1 hθ2 hCs0
    (fun i => (hoS i).2) p2 p6
  have hamb : (q.state 0).ambient ((splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e)).r =
      (splitPorts (Fin n) θ).liftState (toS45 x.endpoint x.r e) := by
    unfold S45.LiveState.ambient
    rw [h2, AgentS45.mask_univ, h3]
  have h8 := AgentS78send.seq_step_positive q t _ _ (2 * Cs) (by linarith)
    (hscale t ht hsmallP) h1 h2 (by rw [hamb]; exact hK0) hbroad h6 h7
  have H := hsw n t θ x.endpoint (sweepEndMapTheta θ x).endpoint x.r hact e _ _ rfl rfl q
    hDo hDs ht hsmall' hθ1 hθ2 hoS p2 p3 p4 p5 p6 h1 h2 h3 h4 hend h6 h8 (h7 _ le_rfl) hrow
  obtain ⟨⟨haff, hK⟩, hrows, hlag⟩ := H
  rw [hθt] at haff hK hrows hlag hDs
  have ha : 0 < t ^ (0.10 * delta) := Real.rpow_pos_of_pos ht _
  have hC'Cb : C' ≤ Cb := le_trans (le_max_left _ _) hCb
  have h1Cb : 1 ≤ Cb := le_trans (le_max_right _ _) hCb
  refine ⟨⟨hact, fun y hy => ?_, ?_⟩, hDs, hrows, fun i hi => ?_⟩
  · obtain ⟨l, r⟩ := haff y hy
    have hT0 : 0 ≤ stageTarget x.endpoint x.r t (stageScale P.u j m) x.endpoint.active y := by
      by_contra hneg
      push_neg at hneg
      have : 0 < C' * t ^ (0.10 * delta) := mul_pos hC' ha
      nlinarith
    constructor
    · refine le_trans ?_ l
      have : C' * t ^ (0.10 * delta) ≤ Cb * t ^ (0.10 * delta) :=
        mul_le_mul_of_nonneg_right hC'Cb ha.le
      nlinarith
    · refine le_trans r ?_
      have : C' * t ^ (0.10 * delta) ≤ Cb * t ^ (0.10 * delta) :=
        mul_le_mul_of_nonneg_right hC'Cb ha.le
      nlinarith
  · refine le_trans hK ?_
    have : 1 * t ^ (0.10 * delta) ≤ Cb * t ^ (0.10 * delta) :=
      mul_le_mul_of_nonneg_right h1Cb ha.le
    linarith
  · refine le_trans (hlag i hi) ?_
    exact mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg (stageScale_pos' hu j m).le _)

end Join

/-! ## Decay of the post-sweep endpoint (split off) -/

section Decay

/-- **Combes–Thomas decay of the post-sweep endpoint (contract, new analysis).** The field
`resolventDecay` of `ClearPhaseData.ofSweep'`: at `t_j`, for `(M + diag ζ − t_j r)⁻¹` on the
active set, with the terminal metric (05 Combes–Thomas, `AgentS78Geo.combes_thomas_entry`); it
needs the physical identity of the post-sweep record (otherwise `M` is an arbitrary real
symmetric matrix). All the conclusions of `sweepEnd_core` are available as hypotheses. -/
def SweepEndResolventStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
  ∀ C Cb : ℝ, 1 ≤ C → 1 ≤ Cb →
  ∃ CA₀ > (0 : ℝ), ∃ cA₀ > (0 : ℝ), ∃ t0 > (0 : ℝ), ∀ CA ≥ CA₀, ∀ cA : ℝ, 0 < cA → cA ≤ cA₀ →
  ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    PhysicalIdentity E (sweepEndMapTheta (sweepTheta P.u m j) x) →
    SweepFacts Cb (stageScale u (j - 1) m) (stageScale u j m) x.endpoint
      (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r →
    IsDampedEndpoint (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r (stageScale u j m) →
    (∀ i, rowFour (normalizedInverse (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint
      (stageScale u j m)) i ≤ 0.7 * stageScale u j m ^ (1 + delta)) →
    ∀ i i', ‖normalizedInverse (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint
        (stageScale u j m) i i'‖ ≤
      CA / Real.sqrt (stageScale u j m) * Real.exp (-cA * stageScale u j m *
        max (physicalDistance d m i i' / 2 - stageScale u j m ^ (-1.03 : ℝ)) 0)

end Decay

/-! ## The sweep-end contract (TilePhaseEnd.lean, amended form) -/

/-- **The sweep end** (`SweepEndStatement`, amended form) from the transport package, the reserve-row package and
the Combes–Thomas package (the duplicated-port identity is proved: `sweepSchur_proof`; the
per-step positivity and the initial comparison are proved here). -/
theorem sweepEnd_proof (hT : SweepTransportStatement d) (hR : SweepReserveRowStatement d)
    (hDec : SweepEndResolventStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∃ Cb₀ > (0 : ℝ), ∀ Cb ≥ Cb₀, ∃ CA₀ > (0 : ℝ), ∃ cA₀ > (0 : ℝ), ∀ CA ≥ CA₀, ∀ cA : ℝ,
      0 < cA → cA ≤ cA₀ → SweepEndStatement d C Cb CA cA cP CP cL CL C₀ := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨Cb₀, hCb₀, CA₁, hCA₁, t1, ht1, hcore⟩ :=
    sweepEnd_core hT hR cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  refine ⟨max Cb₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun Cb hCb => ?_⟩
  have hCb1 : 1 ≤ Cb := le_trans (le_max_right _ _) hCb
  obtain ⟨CA₂, hCA₂, cA₂, hcA₂, t2, ht2, hdec⟩ :=
    hDec cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C Cb hC hCb1
  -- the comparison constants
  set cc := min cL (3 / (8 * CP ^ 2)) / 2 with hcc
  set CC := 3 / 2 * max (C₀ + 1 / cP ^ 2) CL with hCC
  have hCPpos : 0 < CP := lt_of_lt_of_le hcP hCP
  have hcc0 : 0 < cc := by
    have : 0 < min cL (3 / (8 * CP ^ 2)) := lt_min hcL (by positivity)
    rw [hcc]; linarith
  have hCC0 : 0 < CC := by
    have : 0 < max (C₀ + 1 / cP ^ 2) CL := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    rw [hCC]; positivity
  obtain ⟨t3, ht3, hε⟩ := AgentS45.power_small (e := 0.10 * delta) (by norm_num [delta])
    (a := 1 / (2 * Cb)) (by positivity)
  refine ⟨max (max CA₁ CA₂) cc⁻¹, lt_of_lt_of_le hCA₁ ((le_max_left _ _).trans (le_max_left _ _)),
    min cA₂ CC⁻¹, lt_min hcA₂ (inv_pos.mpr hCC0),
    fun CA hCA cA hcA hcA' => ⟨min t1 (min t2 t3), lt_min ht1 (lt_min ht2 ht3), ?_⟩⟩
  intro m n₀ u E ρ P j x hn hu' hu hnj hjm hsmall hSB hphys hcore'
  have hCA1 : CA₁ ≤ CA := (le_max_left _ _).trans ((le_max_left _ _).trans hCA)
  have hCA2 : CA₂ ≤ CA := (le_max_right _ _).trans ((le_max_left _ _).trans hCA)
  have hCA3 : cc⁻¹ ≤ CA := (le_max_right _ _).trans hCA
  obtain ⟨hsw, hDs, hrows, hlag⟩ := hcore Cb (le_trans (le_max_left _ _) hCb) CA hCA1
    m n₀ u E ρ P j x hn hu' hu hnj hjm
    (lt_of_lt_of_le hsmall (min_le_left _ _)) hSB hcore'
  have hdecay := hdec CA hCA2 cA hcA (hcA'.trans (min_le_left _ _)) m n₀ u E ρ P j x
    hn hu' hu hnj hjm (lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_left _ _)))
    hSB hcore' hphys hsw hDs hrows
  -- the initial comparison
  subst hn hu'
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  obtain ⟨ht, hθt, hθ1, hθ2⟩ := digitSweep_scales hu0 (by omega : 1 ≤ j) hjm
  have hθeq : sweepTheta P.u m j = stageScale P.u j m / stageScale P.u (j - 1) m :=
    sweepTheta_digit hjm
  have htsmall : stageScale P.u (j - 1) m < t3 := by
    rw [← sweepScale_digit hjm]
    exact lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_right _ _))
  have hpow := hε _ ht htsmall
  have hpow0 : 0 ≤ stageScale P.u (j - 1) m ^ (0.10 * delta) := Real.rpow_nonneg ht.le _
  have hε' : Cb * stageScale P.u (j - 1) m ^ (0.10 * delta) ≤ 1 / 2 := by
    have h1 : Cb * S45.power (stageScale P.u (j - 1) m) (0.10 * delta) ≤ Cb * (1 / (2 * Cb)) :=
      mul_le_mul_of_nonneg_left hpow.le (by linarith)
    have h2 : Cb * (1 / (2 * Cb)) = 1 / 2 := by field_simp
    exact (h1.trans h2.le)
  have hcmp := sweep_initialComparison (by omega) hu hcP hcL hCL.le hC₀.le x.endpoint
    (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r hSB hsw hDs
    (by rw [← hθeq]; exact hθ1) (by rw [← hθeq]; exact hθ2)
    (mul_nonneg (by linarith) hpow0) hε'
  have hS0 : ∀ f, 0 ≤ spatialEnergy (nnGraph d m)
      (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint.active
      (stageScale P.u P.n₀ m * stageScale P.u j m) f := fun f =>
    spatialEnergy_nonneg' _ _ _ (mul_pos (stageScale_pos' hu _ m) (stageScale_pos' hu _ m)) f
  refine ⟨hsw, hDs, hdecay, fun f => ⟨?_, ?_⟩, hrows, hlag⟩
  · refine le_trans ?_ (hcmp f).1
    exact mul_le_mul_of_nonneg_right (hcA'.trans (min_le_right _ _)) (hS0 f)
  · refine (hcmp f).2.trans ?_
    exact mul_le_mul_of_nonneg_right hCA3 (hS0 f)

end AndersonAC.AgentS78
