import AndersonAC.AgentS78.Construction.SweepEndDecay
import AndersonAC.AgentS78.Construction.SweepEndRows

/-!
# The final reserve rows of a digit sweep

agent-s78send (2026-10-14). `SweepReserveRowStatement` (SweepEnd.lean) reduces, through the
generic reserve-row transfer `AgentS78send.reserveRow_transfer` applied to the committed sweep
on `Port d m` (live start = the ports of the active sites), to the **row tails of every
committed step** (`SweepRowTailStatement`, the `rows` field of S45 `TraceTails` for the
reserve columns; 05:155–239 Lemma `local-prospective`, as argon-s78transfer's A3b for a tile
candidate). The start facts (zero start lag, start reserve rows `≤ θ² rowCap`) are proved here
from the v3 stage-start clauses on `startV3` by reindexing the duplicated start along the
equivalence between the live start ports and the ports of the active sites.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78send

open AndersonAC.S45
open scoped Matrix.Norms.L2Operator

/-- The lag is invariant under reindexing. -/
theorem reindex_lag {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : State ι) (t : ℝ) (i : κ) :
    (AgentS45.State.reindex e s).lag t i = s.lag t (e i) := by
  have hK : 1 - (AgentS45.State.reindex e s).K t = (1 - s.K t).submatrix e e := by
    rw [AgentS45.State.reindex_K]
    ext a b
    simp [Matrix.one_apply, e.injective.eq_iff]
  have hraw : (AgentS45.State.reindex e s).rawLag = s.rawLag ∘ e := rfl
  simp only [State.lag, State.P]
  rw [hK, Matrix.inv_submatrix_equiv, hraw, Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

end AndersonAC.AgentS78send

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem mem_sweepStartLive (θ : ℝ) (x : RunRecord d m) (p : Port d m) :
    p ∈ (sweepStartLiveState θ x).live ↔ p.1 ∈ x.endpoint.active := by
  simp [sweepStartLiveState]

/-- The live start ports are the ports of the active sites. -/
def startLiveEquiv (θ : ℝ) (x : RunRecord d m) :
    {p // p ∈ (sweepStartLiveState θ x).live} ≃ S45.initialPorts {i // i ∈ x.endpoint.active} where
  toFun p := (⟨p.1.1, (mem_sweepStartLive θ x p.1).1 p.2⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2), (mem_sweepStartLive θ x _).2 q.1.2⟩
  left_inv p := rfl
  right_inv q := rfl

/-- The duplicated start, read on its live ports, is the v3 start `startV3` reindexed. -/
theorem sweepStart_state_eq (P : TilePlan d m) (j : ℕ) (x : RunRecord d m) :
    (sweepStartLiveState (sweepTheta P.u m j) x).state (portR (sweepTheta P.u m j) x.r) =
      AgentS45.State.reindex (startLiveEquiv (sweepTheta P.u m j) x) (startV3 P j x.endpoint x.r) :=
  rfl

variable {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}
  {done : Finset (Fin (P.cover j).cover.count)} {x : RunRecord d m}

/-- **Zero lag at the sweep start** on the live ports. -/
theorem TileSweepCore.start_ambientLag (h : TileSweepCore C P j n₀ u E ρ Cb done x) :
    ∀ i ∈ (x.sweep.state 0).live,
      (x.sweep.state 0).ambientLag (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) i = 0 := by
  rw [h.start_lift]
  intro i hi
  unfold S45.LiveState.ambientLag
  rw [dif_pos hi, sweepStart_state_eq, AgentS78send.reindex_lag]
  exact h.start.start_lag _

/-- **Start reserve rows** on the ambient start state. -/
theorem TileSweepCore.start_ambient_reserve_rows (h : TileSweepCore C P j n₀ u E ρ Cb done x)
    (ht : 0 < sweepScale P.u m j) :
    ∀ i ∈ (S45.reserves : Finset (Port d m)),
      ((x.sweep.state 0).ambient (portR (sweepTheta P.u m j) x.r)).fourthRow (sweepScale P.u m j)
        S45.reserves i ≤ sweepTheta P.u m j ^ 2 * S45.rowCap (sweepScale P.u m j) := by
  classical
  rw [h.start_lift]
  intro i hires
  set t := sweepScale P.u m j
  set θ := sweepTheta P.u m j
  set a := sweepStartLiveState θ x
  set r := portR θ x.r
  have hrc : 0 ≤ θ ^ 2 * S45.rowCap t :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.le _)
  by_cases hi : i ∈ a.live
  · -- the live reserve port: the sum is the v3 start reserve row
    have hdead : ∀ j ∈ (S45.reserves : Finset (Port d m)).filter (fun j => j ∉ a.live),
        ‖(a.ambient r).h t i j‖ ^ 4 = 0 := by
      intro j hj
      rw [AgentS45.ambient_h_dead _ r t i (Finset.mem_filter.1 hj).2]; simp
    have hsplit : (a.ambient r).fourthRow t S45.reserves i =
        ∑ j ∈ (S45.reserves : Finset (Port d m)).filter (fun j => j ∈ a.live),
          ‖(a.ambient r).h t i j‖ ^ 4 := by
      simp only [S45.State.fourthRow]
      rw [← Finset.sum_filter_add_sum_filter_not (S45.reserves : Finset (Port d m))
        (fun j => j ∈ a.live), Finset.sum_eq_zero hdead, add_zero]
    have hres : ∀ q : Port d m, q ∈ (S45.reserves : Finset (Port d m)) ↔ q.2 = true := by
      intro q; simp [S45.reserves]
    have hres' : ∀ q : S45.initialPorts {i // i ∈ x.endpoint.active},
        q ∈ (S45.reserves : Finset (S45.initialPorts {i // i ∈ x.endpoint.active})) ↔
          q.2 = true := by
      intro q; simp [S45.reserves]
    have hsum : ∑ j ∈ (S45.reserves : Finset (Port d m)).filter (fun j => j ∈ a.live),
          ‖(a.ambient r).h t i j‖ ^ 4 =
        (startV3 P j x.endpoint x.r).fourthRow t S45.reserves
          (startLiveEquiv θ x ⟨i, hi⟩) := by
      simp only [S45.State.fourthRow]
      refine Finset.sum_bij'
        (fun q hq => startLiveEquiv θ x ⟨q, (Finset.mem_filter.1 hq).2⟩)
        (fun q _ => ((q.1.1, q.2) : Port d m)) ?_ ?_ ?_ ?_ ?_
      · intro q hq
        exact (hres' _).2 ((hres q).1 (Finset.mem_filter.1 hq).1)
      · intro q hq
        refine Finset.mem_filter.2 ⟨(hres _).2 ((hres' q).1 hq), ?_⟩
        exact (mem_sweepStartLive θ x _).2 q.1.2
      · intro q hq; rfl
      · intro q hq; rfl
      · intro q hq
        rw [AgentS45.ambient_h_live a r t hi (Finset.mem_filter.1 hq).2, sweepStart_state_eq,
          AgentS45.State.reindex_h]
        rfl
    rw [hsplit, hsum]
    exact h.start.start_reserve_rows _ ((hres' _).2 ((hres i).1 hires))
  · -- a dead start port: every entry vanishes
    have hz : (a.ambient r).fourthRow t S45.reserves i = 0 := by
      simp only [S45.State.fourthRow]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (a.ambient r).h t i j = 0 := by
        show (Real.sqrt t : ℂ) * S45.mask a.live a.g i j = 0
        simp [S45.mask, S45.pad, hi]
      rw [this]; simp
    rw [hz]; exact hrc

/-! ## The reduction of the reserve rows to the row tails -/

/-- **Row tails of the committed sweep (contract, hard; 05:155–239).** Every committed step of a
finished digit sweep changes the reserve fourth rows only near its pivot:
`|stepRow reserves k i| ≤ t^{-Ct} exp(−ct t³ dist(i, x_k))` (the reserve part of the `rows`
field of S45 `TraceTails`). Route: argon-s78transfer's A3b (`traceTails_of_slotSeq`:
`step_delete_inverse_decay`, poly tail helpers) at every committed prefix, with the prefix
bounds (‖K‖ ≤ 3/4, rawLag) from the cumulative Schur identity of the sweep restricted to the
active ports (luna-s78live) and the prefix decay `TileSweepCore.start.prefix_decay`. -/
def SweepRowTailStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
  ∃ Ct ≥ (1 : ℝ), ∃ ct > (0 : ℝ), ∃ t0 > (0 : ℝ), ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ)
    (P : TilePlan d m) (j : ℕ) (Cb : ℝ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    ∀ k < x.sweep.length, ∀ y, x.sweep.pivot k = some y → ∀ i,
      |x.sweep.stepRow (sweepScale u m j) (portR (sweepTheta u m j) x.r) S45.reserves k i| ≤
        S45.power (sweepScale u m j) (-Ct) *
          Real.exp (-ct * sweepScale u m j ^ 3 * (P.cover j).dist i y)

/-- **The final reserve rows from the row tails.** -/
theorem sweepReserveRow_of_tails (hTail : SweepRowTailStatement d) :
    SweepReserveRowStatement d := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨Ct, hCt, ct, hct, tT, htT, htail⟩ := hTail cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  set Cm := max C Ct with hCm
  have hCm1 : 1 ≤ Cm := le_trans hC (le_max_left _ _)
  obtain ⟨C', hC', tR, htR, htr⟩ := AgentS78send.reserveRow_transfer d Cm ct hCm1 hct
  refine ⟨max C' 1, le_max_right _ _, min (min tT tR) 1, lt_min (lt_min htT htR) one_pos, ?_⟩
  intro m n₀ u E ρ P j Cb x hn hu' hu hnj hjm hsmall hSB hcore i hi
  subst hn hu'
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  have ht : 0 < sweepScale P.u m j := by
    rw [sweepScale_digit hjm]; exact stageScale_pos' hu _ m
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

/-- **The sweep end from the transport, row-tail and terminal Combes–Thomas contracts.** -/
theorem sweepEnd_proof'' (hT : SweepTransportStatement d) (hTail : SweepRowTailStatement d)
    (hCT : TerminalCTStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∃ Cb₀ > (0 : ℝ), ∀ Cb ≥ Cb₀, ∃ CA₀ > (0 : ℝ), ∃ cA₀ > (0 : ℝ), ∀ CA ≥ CA₀, ∀ cA : ℝ,
      0 < cA → cA ≤ cA₀ → SweepEndStatement d C Cb CA cA cP CP cL CL C₀ :=
  sweepEnd_proof' hT (sweepReserveRow_of_tails hTail) hCT

end AndersonAC.AgentS78
