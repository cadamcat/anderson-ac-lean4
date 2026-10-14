import AndersonAC.AgentS78.Construction.SweepEndReserve

/-!
# Analytic end of the final residual sweep

This proves `FinalSweepStatement` in `TilePhaseEnd.lean`; `finalSweep_good` gives
`hfinal_of_finalGood`. The manuscript describes this sweep in 04-sweep.tex:36–41
(`t = t_m = 2η`, `w = θ = 1/2`) and 08-history.tex:340–368 (consuming the residual
with reserve normalization `√(θt) = √η`), with the final record bounds in
08-history.tex:375–386.

The final sweep applies `sweepEnd_core` at `j = m + 1`, where
`sweepScale u m (m+1) = t_m` and `sweepTheta u m (m+1) = 1/2`. The statement
`FinalSweepStatementSB` also assumes stage bounds for the old endpoint at `m`.
`finalSweep_good_SB` adds that hypothesis to `finalSweep_good`. The full transport
and row-tail statements cover `j ≤ m + 1` and imply the digit-sweep cases `j ≤ m`.
They yield a damped endpoint at `η` and lag at most `CA η^{0.42δ}`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S45 (splitPorts initialPorts reserves)
open scoped Matrix.Norms.L2Operator

variable {d m : ℕ}

/-! ## Scales of the final sweep (–41) -/

theorem sweepScale_final (u : ℝ) (m : ℕ) : sweepScale u m (m + 1) = stageScale u m m := by
  unfold sweepScale; rw [if_pos (show IsFinalSweep m (m + 1) by unfold IsFinalSweep; omega)]

theorem sweepTheta_final (u : ℝ) (m : ℕ) : sweepTheta u m (m + 1) = 1 / 2 := by
  unfold sweepTheta; rw [if_pos (show IsFinalSweep m (m + 1) by unfold IsFinalSweep; omega)]

/-- `θ t_m = s_m = η` (–41, 08:351). -/
theorem finalSweep_height (u : ℝ) (m : ℕ) :
    sweepTheta u m (m + 1) * sweepScale u m (m + 1) = OAI.Anderson.scaleHeight m u := by
  rw [sweepTheta_final, sweepScale_final]
  unfold stageScale OAI.Anderson.scaleHeight
  ring

theorem sweepScale_pos {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (m j : ℕ) :
    0 < sweepScale u m j := by
  unfold sweepScale; split_ifs <;> exact stageScale_pos' hu _ _

/-! ## The open contracts of the sweep end, for every sweep `j ≤ m + 1` -/

/-- `SweepTransportStatement` (SweepEnd.lean) for every sweep including the
final residual one (`j ≤ m + 1` instead of `j ≤ m`). -/
def SweepTransportFullStatement (d : ℕ) : Prop :=
  ∀ (C Cb Crow : ℝ) (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m + 1 →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    (∀ i ∈ x.endpoint.active,
      ((x.sweep.state x.sweep.length).ambient (portR (sweepTheta u m j) x.r)).fourthRow
        (sweepScale u m j) reserves ((i, true) : Port d m) ≤
      (sweepTheta u m j ^ 2 + Crow * S45.power (sweepScale u m j) (S45.delta / 2000)) *
        S45.rowCap (sweepScale u m j)) →
    SweepS45Facts Crow (sweepScale u m j) (sweepTheta u m j) x

theorem SweepTransportFullStatement.digit (h : SweepTransportFullStatement d) :
    SweepTransportStatement d :=
  fun C Cb Crow m n₀ u E ρ P j x hn hu' hu hnj hjm =>
    h C Cb Crow m n₀ u E ρ P j x hn hu' hu hnj (by omega)

/-- `SweepRowTailStatement` (SweepEndReserve.lean) for every sweep including
the final residual one (`j ≤ m + 1` instead of `j ≤ m`). -/
def SweepRowTailFullStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
  ∃ Ct ≥ (1 : ℝ), ∃ ct > (0 : ℝ), ∃ t0 > (0 : ℝ), ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ)
    (P : TilePlan d m) (j : ℕ) (Cb : ℝ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m + 1 →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    ∀ k < x.sweep.length, ∀ y, x.sweep.pivot k = some y → ∀ i,
      |x.sweep.stepRow (sweepScale u m j) (portR (sweepTheta u m j) x.r) S45.reserves k i| ≤
        S45.power (sweepScale u m j) (-Ct) *
          Real.exp (-ct * sweepScale u m j ^ 3 * (P.cover j).dist i y)

theorem SweepRowTailFullStatement.digit (h : SweepRowTailFullStatement d) :
    SweepRowTailStatement d := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨Ct, hCt, ct, hct, t0, ht0, H⟩ := h cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  exact ⟨Ct, hCt, ct, hct, t0, ht0, fun m n₀ u E ρ P j Cb x hn hu' hu hnj hjm =>
    H m n₀ u E ρ P j Cb x hn hu' hu hnj (by omega)⟩

/-- `SweepReserveRowStatement` for every sweep `j ≤ m + 1`. -/
def SweepReserveRowFullStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
  ∃ Crow ≥ (1 : ℝ), ∃ t0 > (0 : ℝ), ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ)
    (Cb : ℝ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m + 1 →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    ∀ i ∈ x.endpoint.active,
      ((x.sweep.state x.sweep.length).ambient (portR (sweepTheta u m j) x.r)).fourthRow
        (sweepScale u m j) reserves ((i, true) : Port d m) ≤
      (sweepTheta u m j ^ 2 + Crow * S45.power (sweepScale u m j) (S45.delta / 2000)) *
        S45.rowCap (sweepScale u m j)

/-- **The final reserve rows from the row tails** (`sweepReserveRow_of_tails` for `j ≤ m + 1`). -/
theorem sweepReserveRowFull_of_tails (hTail : SweepRowTailFullStatement d) :
    SweepReserveRowFullStatement d := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨Ct, hCt, ct, hct, tT, htT, htail⟩ := hTail cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  set Cm := max C Ct with hCm
  have hCm1 : 1 ≤ Cm := le_trans hC (le_max_left _ _)
  obtain ⟨C', hC', tR, htR, htr⟩ := AgentS78send.reserveRow_transfer d Cm ct hCm1 hct
  refine ⟨max C' 1, le_max_right _ _, min (min tT tR) 1, lt_min (lt_min htT htR) one_pos, ?_⟩
  intro m n₀ u E ρ P j Cb x hn hu' hu hnj hjm hsmall hSB hcore i hi
  subst hn hu'
  have ht : 0 < sweepScale P.u m j := sweepScale_pos hu m j
  have ht1 : sweepScale P.u m j ≤ 1 := (lt_of_lt_of_le hsmall (min_le_right _ _)).le
  obtain ⟨blocks, hb1, hb2, hb3, -, hb5⟩ := hcore.blocks
  have hrowtail := htail m P.n₀ P.u E ρ P j Cb x rfl rfl hu hnj hjm
    (lt_of_lt_of_le hsmall ((min_le_left _ _).trans (min_le_left _ _))) hSB hcore
  have H := htr (Port d m) (Torus d m) (sweepScale P.u m j) (P.cover j).b (sweepTheta P.u m j)
    (P.cover j).C C (P.cover j).dist (portR (sweepTheta P.u m j) x.r) S45.reserves
    (P.cover j).cover x.sweep blocks ht
    (lt_of_lt_of_le hsmall ((min_le_left _ _).trans (min_le_right _ _)))
    (hcore.plan.cover_C.trans (le_max_left _ _)) hcore.plan.shell (le_max_left _ _)
    hcore.wellFormed
    (fun k l hk hl y hy hy' => pivot_injective hcore.wellFormed hk hl hy hy')
    hb1 hb2 hb3
    (fun k hk y hy i => (hrowtail k hk y hy i).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith [le_max_right C Ct]))
      (Real.exp_pos _).le))
    hcore.start_ambientLag (hcore.start_ambient_reserve_rows ht)
    (fun T i hi => ((hb5 T).2.1 i hi).2)
  have hmem : ((i, true) : Port d m) ∈ (S45.reserves : Finset (Port d m)) ∩
      (x.sweep.state x.sweep.length).live := by
    refine Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩,
      (hcore.live_end _).2 ⟨hi, rfl⟩⟩
  refine (H _ hmem).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht.le _)
  have : 0 ≤ S45.power (sweepScale P.u m j) (S45.delta / 2000) := Real.rpow_nonneg ht.le _
  nlinarith [le_max_left C' 1]

/-! ## The final sweep core: damped endpoint at `η` and the endpoint lag -/

/-- **The end of the final residual sweep** (θ = 1/2, `t = t_m`): the post-sweep endpoint is a
damped endpoint at `η = s_m` (`sweepEndMapTheta_isDamped`), and its active
diagonal lag is `≤ CA η^{0.42δ}` (Proposition 4.9 through `sweep_from_S45`, as in
`sweepEnd_core`). -/
theorem finalSweep_core (hT : SweepTransportFullStatement d)
    (hTail : SweepRowTailFullStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∃ CA > (0 : ℝ), ∃ t0 > (0 : ℝ),
    ∀ (Cb : ℝ) (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ ≤ m →
    sweepScale u m (m + 1) < t0 →
    StageBounds d m n₀ m u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P (m + 1) n₀ u E ρ Cb Finset.univ x →
    IsDampedEndpoint (sweepEndMapTheta (sweepTheta P.u m (m + 1)) x).endpoint x.r
      (OAI.Anderson.scaleHeight m u) ∧
    (sweepEndMapTheta (sweepTheta P.u m (m + 1)) x).endpoint.active = x.endpoint.active ∧
    (∀ i ∈ (sweepEndMapTheta (sweepTheta P.u m (m + 1)) x).endpoint.active,
      ‖(sweepEndMapTheta (sweepTheta P.u m (m + 1)) x).endpoint.g i i - x.r i‖ ≤
        CA * OAI.Anderson.scaleHeight m u ^ (0.42 * delta)) := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨Crow, hCrow, tT, htT, hR'⟩ :=
    sweepReserveRowFull_of_tails hTail cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  set Cs : ℝ := max (max CP (1 / cP)) Crow with hCs_def
  have hCs1 : 1 ≤ Cs := le_trans hCrow (le_max_right _ _)
  obtain ⟨C', hC', ts, hts, hsw⟩ := sweep_from_S45 Cs hCs1
  obtain ⟨tP, htP, hscale⟩ := AgentS78send.exists_positiveScale (2 * Cs) (by linarith)
  refine ⟨4 * C', by linarith, min tT (min ts tP), lt_min htT (lt_min hts htP),
    fun Cb m n₀ u E ρ P x hn hu' hu hnm hsmall hSB hcore => ?_⟩
  have hpiv := hcore.pivots_some
  subst hn hu'
  have hSB' : StageBounds d m P.n₀ (m + 1 - 1) P.u cP CP cL CL C₀ x.endpoint x.r := by
    rwa [Nat.add_sub_cancel]
  have hts_eq := sweepScale_final P.u m
  have hθ_eq := sweepTheta_final P.u m
  have ht : 0 < stageScale P.u m m := stageScale_pos' hu m m
  have hη : sweepTheta P.u m (m + 1) * stageScale P.u m m = OAI.Anderson.scaleHeight m P.u := by
    rw [← hts_eq]; exact finalSweep_height P.u m
  set t := stageScale P.u m m with ht_def
  set θ := sweepTheta P.u m (m + 1) with hθ_def
  have hθ1 : 1 / 4 ≤ θ := by rw [hθ_eq]; norm_num
  have hθ2 : θ ≤ 5 / 8 := by rw [hθ_eq]; norm_num
  have hθpos : 0 < θ := by rw [hθ_eq]; norm_num
  have hθlt : θ < 1 := by rw [hθ_eq]; norm_num
  have hsmall' : t < ts := by
    rw [← hts_eq]; exact lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallP : t < tP := by
    rw [← hts_eq]; exact lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_right _ _))
  -- old endpoint: damped at `t_m`
  have hDo : IsDampedEndpoint x.endpoint x.r t := by
    have := hcore.hist.damped (by omega : P.n₀ ≤ m + 1 - 1)
    rwa [Nat.add_sub_cancel] at this
  -- live set at the end and the active set of the post-sweep endpoint
  have hlive := hcore.live_end
  have hact : (sweepEndMapTheta θ x).endpoint.active = x.endpoint.active :=
    sweepEndActive_eq hlive
  -- post-sweep endpoint damped at `θ t = η`
  have hwf : x.sweep.wellFormed t (portR θ x.r) := by
    have := hcore.wellFormed; rwa [hts_eq] at this
  have hDs : IsDampedEndpoint (sweepEndMapTheta θ x).endpoint x.r (θ * t) :=
    sweepEndMapTheta_isDamped x x ht hθpos hθlt hDo rfl hwf hcore.start_lift
      (pivot_bit_of_ne_none hcore hpiv) hlive
  -- the transported sweep
  obtain ⟨n, e, q, h1, h2, h3, h4, h5, h6, h7, h9⟩ :=
    hT C Cb Crow m P.n₀ P.u E ρ P (m + 1) x rfl rfl hu (by omega) le_rfl hcore
      (hR' m P.n₀ P.u E ρ P (m + 1) Cb x rfl rfl hu (by omega) le_rfl
        (lt_of_lt_of_le hsmall (min_le_left _ _)) hSB' hcore)
  rw [hts_eq] at h1 h6 h7 h9
  -- old-state facts from the stage bounds at `m`
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
  have hend : ∀ i k : Fin n, (q.state q.length).g (i, true) (k, true) =
      Real.sqrt θ * (toS45 (sweepEndMapTheta θ x).endpoint x.r
        (e.trans (Equiv.subtypeEquivRight (fun y => by rw [hact])))).g i k := by
    intro i k
    rw [h5]
    have hsq : (Real.sqrt θ : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθpos
      exact_mod_cast this.ne'
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
  obtain ⟨-, -, hlag⟩ := H
  rw [hη] at hDs hlag
  exact ⟨hDs, hact, hlag⟩

/-! ## The final sweep record with stage bounds -/

/-- `FinalSweepStatementSB` adds stage bounds for the old endpoint at `m`, analogous
to the StageBounds hypothesis at `j − 1` in `SweepEndStatement`. The run invariant
provides them through `stageBounds_of_hist` with `k = m`. -/
def FinalSweepStatementSB (d : ℕ) (C Cb Cr cp cg cP CP cL CL C₀ : ℝ) : Prop :=
  ∃ t0 > 0, ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ ≤ m →
    sweepScale u m (m + 1) < t0 →
    StageBounds d m n₀ m u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P (m + 1) n₀ u E ρ Cb Finset.univ x →
    let y := sweepEndMapTheta (sweepTheta P.u m (m + 1)) x
    IsDampedEndpoint y.endpoint y.r (OAI.Anderson.scaleHeight m u) ∧
    Fintype.card (Torus d m) ≤ 2 * y.endpoint.active.card ∧
    (∀ i ∈ y.endpoint.active, ‖y.r i‖ ≤ Cr ∧ cp ≤ (y.r i).im) ∧
    (∀ i ∈ y.endpoint.active, ‖y.endpoint.g i i - y.r i‖ ≤ cp - cg)

/-- The statement with stage bounds implies the base statement for records whose old endpoint satisfies the
stage bounds at `m` (as a hypothesis on every record, which is how the run supplies it). -/
theorem finalSweepStatement_of_SB {C Cb Cr cp cg cP CP cL CL C₀ : ℝ}
    (h : FinalSweepStatementSB d C Cb Cr cp cg cP CP cL CL C₀)
    (hSB : ∀ (m n₀ : ℕ) (u : ℝ) (x : RunRecord d m),
      StageBounds d m n₀ m u cP CP cL CL C₀ x.endpoint x.r) :
    FinalSweepStatement d C Cb Cr cp cg := by
  obtain ⟨t0, ht0, H⟩ := h
  exact ⟨t0, ht0, fun m n₀ u E ρ P x hn hu' hu hnm hsmall hcore =>
    H m n₀ u E ρ P x hn hu' hu hnm hsmall (hSB m n₀ u x) hcore⟩

/-- **The final residual sweep record** (`FinalSweepStatementSB`) from the transport and
row-tail contracts for `j ≤ m + 1`, with `Cr = CP`, `cp = cP`, `cg = cP/2` (08:375–386). -/
theorem finalSweep_proof (hT : SweepTransportFullStatement d)
    (hTail : SweepRowTailFullStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∀ Cb : ℝ, FinalSweepStatementSB d C Cb CP cP (cP / 2) cP CP cL CL C₀ := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC Cb
  obtain ⟨CA, hCA, t1, ht1, hcore⟩ := finalSweep_core hT hTail cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨t3, ht3, hε⟩ := AgentS45.power_small (e := 0.42 * delta) (by norm_num [delta])
    (a := cP / (2 * CA)) (by positivity)
  refine ⟨min t1 t3, lt_min ht1 ht3, ?_⟩
  intro m n₀ u E ρ P x hn hu' hu hnm hsmall hSB hcoreX y
  obtain ⟨hDs, hact, hlag⟩ := hcore Cb m n₀ u E ρ P x hn hu' hu hnm
    (lt_of_lt_of_le hsmall (min_le_left _ _)) hSB hcoreX
  have hSB0 := hSB
  unfold StageBounds at hSB0
  dsimp only at hSB0
  obtain ⟨hdiag, -, -, -, hcard, -, -⟩ := hSB0
  -- `η < t_m < t3`
  have hη : OAI.Anderson.scaleHeight m u < t3 := by
    have h1 : OAI.Anderson.scaleHeight m u < sweepScale u m (m + 1) := by
      rw [sweepScale_final]; unfold stageScale OAI.Anderson.scaleHeight
      have hu0 : 0 < u := lt_trans (by norm_num) hu.1
      have : 0 < u / (4 : ℝ) ^ m := by positivity
      linarith
    exact lt_trans h1 (lt_of_lt_of_le hsmall (min_le_right _ _))
  have hη0 : 0 < OAI.Anderson.scaleHeight m u := by
    have hu0 : 0 < u := lt_trans (by norm_num) hu.1
    unfold OAI.Anderson.scaleHeight; positivity
  have hpow := hε _ hη0 hη
  have hlag' : CA * OAI.Anderson.scaleHeight m u ^ (0.42 * delta) ≤ cP - cP / 2 := by
    have h1 : CA * S45.power (OAI.Anderson.scaleHeight m u) (0.42 * delta) ≤
        CA * (cP / (2 * CA)) := mul_le_mul_of_nonneg_left hpow.le hCA.le
    have h2 : CA * (cP / (2 * CA)) = cP - cP / 2 := by
      rw [mul_div_assoc', mul_comm CA cP, mul_div_mul_right _ _ hCA.ne']; ring
    exact h1.trans h2.le
  subst hu'
  refine ⟨hDs, ?_, fun i hi => ?_, fun i hi => (hlag i hi).trans hlag'⟩
  · show Fintype.card (Torus d m) ≤ 2 * (sweepEndMapTheta (sweepTheta P.u m (m + 1)) x).endpoint.active.card
    rw [hact]; exact hcard
  · have hi' : i ∈ x.endpoint.active := by rw [← hact]; exact hi
    obtain ⟨-, h1, -, h3⟩ := hdiag i hi'
    exact ⟨h3, h1⟩

/-- **The constants of the final record** as the consumer (`UniformCertificateInput`:
`0 < cp`, `0 < cg`) needs them; they depend only on the stage-bound constants. -/
theorem finalSweep_exists (hT : SweepTransportFullStatement d)
    (hTail : SweepRowTailFullStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
    ∃ Cr cp cg : ℝ, 0 < cp ∧ 0 < cg ∧ ∀ C : ℝ, 1 ≤ C → ∀ Cb : ℝ,
      FinalSweepStatementSB d C Cb Cr cp cg cP CP cL CL C₀ :=
  fun cP CP cL CL C₀ hcP hCP hcL hCL hC₀ =>
    ⟨CP, cP, cP / 2, hcP, by linarith, fun C hC Cb =>
      finalSweep_proof hT hTail cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC Cb⟩

/-- **The final record from the tile-phase invariant of the final sweep** (`finalSweep_good`
with the stage bounds at `m` as a hypothesis on the record). -/
theorem finalSweep_good_SB {C Cb Cr cp cg cP CP cL CL C₀ : ℝ}
    (hfin : FinalSweepStatementSB d C Cb Cr cp cg cP CP cL CL C₀) :
    ∃ t0 > 0, ∀ {m : ℕ} {P : TilePlan d m} {n₀ : ℕ} {u E : ℝ} {ρ : ℂ},
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ ≤ m →
    sweepScale u m (m + 1) < t0 →
    ∀ x : RunRecord d m, x ∈ TileSweepInv C P (m + 1) n₀ u E ρ Cb Finset.univ →
    (x.aborted = false → StageBounds d m n₀ m u cP CP cL CL C₀ x.endpoint x.r) →
    (guardMap (endMap P (m + 1)) x).aborted = false →
    guardMap (endMap P (m + 1)) x ∈ FinalGood (d := d) (m := m) u E Cr cp cg := by
  obtain ⟨t0, ht0, hfin⟩ := hfin
  refine ⟨t0, ht0, ?_⟩
  intro m P n₀ u E ρ hn hu' hu hnm hsmall x hx hSB hab
  have hab' : x.aborted = false := by
    unfold guardMap at hab; split_ifs at hab with h
    · exact absurd hab (by simp [h])
    · simpa [Bool.not_eq_true] using h
  have hg : guardMap (endMap P (m + 1)) x = endMap P (m + 1) x := by simp [guardMap, hab']
  rw [hg, endMap_final]
  obtain ⟨h1, h2, h3, h4⟩ := hfin m n₀ u E ρ P x hn hu' hu hnm hsmall (hSB hab') (hx hab')
  exact ⟨(hx hab').physical_end, h1, h2, h3, h4⟩

end AndersonAC.AgentS78
