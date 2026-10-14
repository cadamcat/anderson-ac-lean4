import AndersonAC.AgentS78.Construction.StagePhasePkgOps

/-!
# Clearing-phase package: clearing operations and the sweep-end hand-over

agent-s78phase2 (DISPATCH 04:08:18).

* `runOp_clear_exit`: a clearing operation of a clearing stage exits by the clearing block;
* `clrOp_keeps` (`ClearingBoxFacts.hClr`): `boxCL … j (rank y) → boxCL … j (rank y + 1)`,
  from `clearingBlockR_keeps` (analytic DONE statement), the frozen damping, and the physical
  identity (FAIL/empty: unchanged; DONE: `ClearingDonePhysHyp`);
* `sweepEnd_clear` (`ClearingBoxFacts.hXcE`): the sweep end of a clearing stage enters
  `ClearPhaseR … j 0`: the sweep-end facts (`SweepEndStatement`) with the scale radius
  `Ds = 2^9 t_j^{-8-ν}` (`ofSweepDs`), the record clauses after the snapshot
  (`clearRecPos_snapshot`; coupled prefixes from `RunBasics`, cover and pending from `Xg`, the
  hop structure from the physical identity), the broad damping from the history.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf)
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-- A clearing operation of a clearing stage exits by the clearing block. -/
theorem runOp_clear_exit (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (n₀ : ℕ) (u : ℝ) (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m / 2)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hrun : ∀ k' < k, (runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y) x k' ω) = false) :
    ∃ s0, BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s0 ∧
      (runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y).exit
        (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y) x k ω) =
        clearingExit (d := d) (m := m) j y s0 := by
  have hreach := localState_reach (tileOrderSize P) _ x ω k hrun
  revert hreach
  generalize localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y) x k ω = s
  intro hreach
  have hop : runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y =
      (clrOf n₀ u j y).embed (clearEmbed ts₀) clearProj := by
    rw [runOp_two, if_pos ⟨hj, by omega, hjm⟩]
  rw [hop] at hreach ⊢
  obtain ⟨s0, hs0, rfl⟩ := blockReach_embed (clrOf n₀ u j y) (clearEmbed ts₀) clearProj
    (fun _ => rfl) x s hreach
  exact ⟨s0, hs0, rfl⟩

theorem runOp_clear_id (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (n₀ : ℕ) (u : ℝ) (j : ℕ) (y : Torus d m) (hjm : ¬ j ≤ m / 2) :
    runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y = simpleBlock (ts₀, cl₀) id := by
  rw [runOp_two, if_neg (fun h => hjm h.2.2)]

/-- **Clearing operations keep the record part** (`hXcC`). -/
theorem clrOp_Xc {cB CB Ctr CA cA PA : ℝ} {N : ℕ} {t₀ : ℝ}
    (hdone : ClearingDoneInst d cB CB Ctr CA cA PA N t₀)
    (hCtr : 2 ≤ Ctr) (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (E : ℝ) (ρ : ℂ) (Cb dlo dhi : ℝ) (RB : ℕ → Set (RunRecord d m)) (j : ℕ) (y : Torus d m)
    (hN : N ≤ P.n₀) (hj : P.n₀ < j) (hjc : j ≤ m / 2) (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (ht : stageScale P.u j m < t₀) (ht4 : stageScale P.u j m ≤ 1 / 4) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u RB j 2 y
      (boxCL P.n₀ P.u E ρ Cb CA cA PA dlo dhi (pkgXc cB CB Ctr P E ρ Cb CA cA PA) j
        (siteRank d m y))
      (pkgXc cB CB Ctr P E ρ Cb CA cA PA j (siteRank d m y + 1)) := by
  intro x k ω _ hx hrun _ _ _
  obtain ⟨s0, hs0, he⟩ := runOp_clear_exit P ts₀ cl₀ P.n₀ P.u j y hj hjc x k ω hrun
  rw [he]
  exact clearingBlockR_keeps hdone (clearingDoneHops_proof d) hCtr j y hN hj hu ht ht4
    x (hx.2 hjc) s0 hs0

/-- The DONE exit is in the clearing phase. -/
theorem clrOp_donePhase {cB CB Ctr CA cA PA : ℝ} {N : ℕ} {t₀ : ℝ}
    (hdone : ClearingDoneInst d cB CB Ctr CA cA PA N t₀)
    (hCtr : 2 ≤ Ctr) (P : TilePlan d m) (E : ℝ) (ρ : ℂ) (Cb dlo dhi : ℝ) (j : ℕ) (y : Torus d m)
    (hN : N ≤ P.n₀) (hj : P.n₀ < j) (hjc : j ≤ m / 2) (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (ht : stageScale P.u j m < t₀) (ht4 : stageScale P.u j m ≤ 1 / 4)
    (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (hx : x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA dlo dhi (pkgXc cB CB Ctr P E ρ Cb CA cA PA) j
      (siteRank d m y)) (hab : x.aborted = false)
    (hs : BlockReach (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x s)
    (hne : s.2.core ≠ ∅) (hf : s.2.failed = false) (hdn : s.2.done = true) :
    ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (clearingDoneExit x s.2) := by
  have hR' := clearingBlockR_keeps hdone (clearingDoneHops_proof d) hCtr j y hN hj hu ht ht4
    x (hx.2 hjc) s hs
  have he : clearingExit (d := d) (m := m) j y s = clearingDoneExit x s.2 := by
    have hx1 := (clr_reach P.n₀ j P.u y x s hs).1
    obtain ⟨r0, sc0⟩ := s
    simp only at hx1 hne hf hdn ⊢
    subst hx1
    have hne' : sc0.core ≠ ∅ := hne
    simp [clearingExit, hab, clearingScheduled, hjc, hne', hf, hdn]
  rw [he] at hR'
  exact hR'.toPhase

/-- **The DONE step of the box** (`hDone`): the DONE exit is in the clearing phase, and has the
physical identity by `hP`. -/
theorem clrOp_done {cB CB Ctr CA cA PA : ℝ} {N : ℕ} {t₀ : ℝ}
    (hdone : ClearingDoneInst d cB CB Ctr CA cA PA N t₀) (hP : ClearingDonePhysHyp d)
    (hCtr : 2 ≤ Ctr) (P : TilePlan d m) (E : ℝ) (ρ : ℂ) (Cb dlo dhi : ℝ) (j : ℕ) (y : Torus d m)
    (hN : N ≤ P.n₀) (hj : P.n₀ < j) (hjc : j ≤ m / 2) (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (ht : stageScale P.u j m < t₀) (ht4 : stageScale P.u j m ≤ 1 / 4)
    (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (hx : x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA dlo dhi (pkgXc cB CB Ctr P E ρ Cb CA cA PA) j
      (siteRank d m y)) (hab : x.aborted = false)
    (hs : BlockReach (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x s)
    (hne : s.2.core ≠ ∅) (hf : s.2.failed = false) (hdn : s.2.done = true) :
    ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (clearingDoneExit x s.2) ∧
      PhysicalIdentity E (clearingDoneExit x s.2) := by
  have hR' := clearingBlockR_keeps hdone (clearingDoneHops_proof d) hCtr j y hN hj hu ht ht4
    x (hx.2 hjc) s hs
  have he : clearingExit (d := d) (m := m) j y s = clearingDoneExit x s.2 := by
    have hx1 := (clr_reach P.n₀ j P.u y x s hs).1
    obtain ⟨r0, sc0⟩ := s
    simp only at hx1 hne hf hdn ⊢
    subst hx1
    have hne' : sc0.core ≠ ∅ := hne
    simp [clearingExit, hab, clearingScheduled, hjc, hne', hf, hdn]
  rw [he] at hR'
  exact ⟨hR'.toPhase, hP P.n₀ j P.u E y x s hs hab hjc hne hf hdn (hx.1.2 hab)⟩

/-- The schedule index of the sweep end of stage `j`. -/
theorem sweepEnd_decode (j : ℕ) :
    decodeJ d m (opIndex d m j 1 (site₀ d m)) = j ∧ decodeK d m (opIndex d m j 1 (site₀ d m)) = 1 ∧
      opIndex d m j 1 (site₀ d m) % siteCount d m = 0 := by
  obtain ⟨e1, e2, e3⟩ := decode_opIndex (d := d) (m := m) j 1 (site₀ d m) (by norm_num)
  refine ⟨e1, e2, ?_⟩
  rw [← rank_decodeY, e3, rank_site₀]

/-- **The sweep end of a clearing stage enters the clearing-phase set** (`hXcE`). -/
theorem sweepEnd_clear {Cg Cb CA cA PA cP CP cL CL C₀ : ℝ} {t0 : ℝ}
    (hend : ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ) (x : RunRecord d m),
      P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
      sweepScale u m j < t0 →
      StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
      PhysicalIdentity E (sweepEndMapTheta (sweepTheta P.u m j) x) →
      TileSweepCore Cg P j n₀ u E ρ Cb Finset.univ x →
      let sw := (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint
      SweepFacts Cb (stageScale u (j - 1) m) (stageScale u j m) x.endpoint sw x.r ∧
      IsDampedEndpoint sw x.r (stageScale u j m) ∧
      (∀ i i', ‖normalizedInverse sw (stageScale u j m) i i'‖ ≤
        CA / Real.sqrt (stageScale u j m) * Real.exp (-cA * stageScale u j m *
          max (physicalDistance d m i i' / 2 - stageScale u j m ^ (-1.03 : ℝ)) 0)) ∧
      (∀ f, cA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f ≤
          endpointEnergy sw x.r (stageScale u j m) f ∧
        endpointEnergy sw x.r (stageScale u j m) f ≤
          CA * spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f) ∧
      (∀ i, rowFour (normalizedInverse sw (stageScale u j m)) i ≤
        0.7 * stageScale u j m ^ (1 + delta)) ∧
      (∀ i ∈ sw.active, ‖sw.g i i - x.r i‖ ≤ CA * stageScale u j m ^ (0.42 * delta)))
    (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (E : ℝ) (ρ : ℂ)
    (j : ℕ) (y : Torus d m) (hy : y = site₀ d m)
    (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hn₀ : 1 ≤ P.n₀) (hj : P.n₀ < j) (hjm : j ≤ m)
    (hm : 2 ≤ m) (hCA : 512 ≤ CA) (hcA : 0 < cA) (hPA : 0 ≤ PA) (hcP : 0 < cP)
    (hsmall : sweepScale P.u m j < t0)
    (hSBh : ∀ k s rk, P.n₀ ≤ k → k ≤ m → BoundaryHist P.n₀ P.u E ρ Cb k s rk →
      StageBounds d m P.n₀ k P.u cP CP cL CL C₀ s rk)
    (hcAP : cA ≤ cP) (hCAP : CP ≤ CA) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n ∩ pkgXg (2 ^ 25) P n) j 1 y
      (boxTS Cg P P.n₀ P.u E ρ Cb cP CP j (siteCount d m))
      (pkgXc cP CP (2 ^ 25) P E ρ Cb CA cA PA j 0) := by
  intro x k ω hxRB hx hrun _ hexRB hjc hab'
  subst hy
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 1 (site₀ d m) =
      simpleBlock (ts₀, cl₀) (guardMap (endMap P j)) := by
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩), if_neg (show (1 : ℕ) ≠ 0 by norm_num),
      if_pos (show (1 : ℕ) = 1 from rfl), if_pos (show site₀ d m = site₀ d m from rfl)]
  have hex := runOp_simple_exit P ts₀ cl₀ P.n₀ P.u j 1 (site₀ d m) _ hop x k ω hrun
  rw [hex] at hab' hexRB ⊢
  have hab : x.aborted = false := by
    cases h : x.aborted
    · rfl
    · rw [guardMap_aborted _ x h, h] at hab'; cases hab'
  rw [guardMap_live _ x hab] at hab' hexRB ⊢
  have hT : TileSweepCore Cg P j P.n₀ P.u E ρ Cb Finset.univ x := by
    have := hx.1; rw [doneUpTo_all] at this; exact this hab
  set θ := sweepTheta P.u m j with hθ
  set z := sweepEndMapTheta θ x with hz
  have hEnd : endMap P j x = snapshotMap j z := by
    unfold endMap; simp only [Function.comp, if_pos hjc]; rfl
  have hSB := hSBh (j - 1) x.endpoint x.r (by omega) (by omega) hT.hist
  obtain ⟨hsw, hdmp, hdec, hcmp, hrow, hlag⟩ :=
    hend m P.n₀ P.u E ρ P j x rfl rfl hu hj hjm hsmall hSB hT.physical_end hT
  have hzE : z.endpoint = (endMap P j x).endpoint := (endMap_endpoint P j x).1.symm
  have hzr : (endMap P j x).r = x.r := (endMap_endpoint P j x).2.1
  -- the clearing-phase datum with the large scale radius
  set t := stageScale P.u j m with ht
  have hw := ds_window (d := d) hu hjm
  have hCA1 : 1 ≤ CA := by linarith
  have htp := Real.rpow_pos_of_pos (stageScale_pos' hu j m) (-8 - nu d)
  let D : ClearPhaseData P.n₀ P.u E ρ Cb CA cA PA j (endMap P j x) :=
    ClearPhaseData.ofSweepDs hu hn₀ hj hjm hm hCA1 hcA hPA (512 * t ^ (-8 - nu d))
      (by linarith) (by nlinarith) (ds_embedded hu hjm hm) x.endpoint z.endpoint x.r hT.hist hsw
      (fun i => ⟨hcAP.trans (hx.2 i).1, (hx.2 i).2.1.trans hCAP, (hx.2 i).2.2.trans hCAP⟩) hdmp
      (by rw [hsw.active]; exact (hT.hist.count_metric (by omega)).1)
      (fun a b => by
        rw [hsw.active]
        refine le_trans ?_ ((hT.hist.count_metric (by omega)).2 a b)
        have h1 : stageScale P.u j m ≤ stageScale P.u (j - 1) m := stageScale_anti hu m (by omega)
        have h2 : stageScale P.u (j - 1) m ^ (-1.03 : ℝ) ≤ stageScale P.u j m ^ (-1.03 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (stageScale_pos' hu j m) h1 (by norm_num)
        linarith)
      hdec hcmp hrow hlag (endMap P j x) hzE.symm hzr
  -- the record facts of `x` and of the exit
  have hdecn := sweepEnd_decode (d := d) (m := m) j
  set n := opIndex d m j 1 (site₀ d m) with hn
  obtain ⟨hbas1, -, hbas3⟩ := hxRB.1 hab
  have hph := phaseOf_end P n hdecn.2.1 hdecn.2.2 (by rw [hdecn.1]; exact hj)
    (by rw [hdecn.1]; omega)
  rw [hph.1, hdecn.1] at hbas3
  have hreserve : sweepEndActive x = x.endpoint.active := sweepEndActive_eq_rb x hbas3.reserve
  have hgi : gIdx P n = some (j - 1) := by
    unfold gIdx; rw [hdecn.1, hdecn.2.1, if_neg (by omega), if_pos hjm, if_pos (Or.inr ⟨rfl, hdecn.2.2⟩)]
  obtain ⟨hcover, hpend, l, T, hT1, hT2⟩ := hxRB.2 hab (j - 1) hgi
  have hdisj : ∀ i ∈ x.endpoint.active, i ∉ x.terminal := by
    refine hbas1 ?_
    have := (lt_finalStart_iff (d := d) (m := m) n).mpr (by rw [hdecn.1]; exact hjm)
    exact this.le
  have hzact : z.endpoint.active = x.endpoint.active := hreserve
  have hzterm : z.terminal = x.terminal := rfl
  have hcompl : z.endpoint.active = Finset.univ \ z.terminal := by
    rw [hzact, hzterm]; ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨hdisj i, fun hi => (hcover i).resolve_right hi⟩
  -- coupled prefixes from `RunBasics` after the sweep end
  obtain ⟨-, -, hpost⟩ := hexRB.1 hab'
  rw [hph.2, hdecn.1] at hpost
  have hcoupled : ∀ i ∈ z.endpoint.active, i ∉ z.pending → z.prefixLength i + P.n₀ = j := by
    intro i hi hip
    have := hpost i (by rw [hEnd]; exact hi) (by rw [hEnd]; exact hip)
    rw [hEnd] at this
    have hdl : doneLength m P.n₀ j = j - P.n₀ := by unfold doneLength; rw [if_pos hjm]
    show z.prefixLength i + P.n₀ = j
    have : (snapshotMap j z).prefixLength i = j - P.n₀ := this.trans hdl
    change z.prefixLength i = j - P.n₀ at this
    omega
  -- the trace
  have htrace : ∃ l, ∃ T : ClearingGeometry d m P.n₀ j l P.u (2 ^ 25),
      (∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
        (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
        ∀ a ∈ z.endpoint.active, ∀ b ∈ z.endpoint.active, z.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
          terminalDistance (nnGraph d m) (geometryTerminals T) a b = 0) ∧
      geometryTerminals T = z.terminal ∧ ∀ a, T.index a ≠ j := by
    refine ⟨l, clearingGeometryLift T (show j - 1 ≤ j by omega), ?_, hT1, fun a => ?_⟩
    · refine AndersonAC.AgentS78Geo.hops_of_physicalIdentity (by omega) E z hT.physical_end _
        (fun w hw => ?_)
      show w ∈ geometryTerminals T
      rw [hT1]
      rcases hcover w with h | h
      · exact absurd (hzact ▸ h) hw
      · exact h
    · have := hT2 a
      show T.index a ≠ j
      omega
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · have h := clearRecPos_snapshot (2 ^ 25) P.n₀ P.u j z hcoupled hcompl
      (by show x.pending ⊆ z.endpoint.active; rw [hzact]; exact hpend) htrace
    rw [← hEnd] at h
    exact h
  · exact hw.1
  · exact hw.2
  · intro i
    rw [hzr]
    exact ⟨(hx.2 i).1, (hx.2 i).2.2⟩

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-- **The DONE step of the box off the exceptional set** (route R2 form of `hDone`). -/
theorem clrOp_doneZ {cB CB Ctr CA cA PA : ℝ} {N : ℕ} {t₀ : ℝ}
    (hdone : ClearingDoneInst d cB CB Ctr CA cA PA N t₀) (hPZ : ClearingDonePhysZ d)
    (hCtr : 2 ≤ Ctr) (P : TilePlan d m) (E : ℝ) (ρ : ℂ) (Cb dlo dhi : ℝ) (j : ℕ) (y : Torus d m)
    (hN : N ≤ P.n₀) (hj : P.n₀ < j) (hjc : j ≤ m / 2) (hu : P.u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (ht : stageScale P.u j m < t₀) (ht4 : stageScale P.u j m ≤ 1 / 4)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hω : ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P))
    (hTV : x ∈ TrueValues P.n₀ P.u ω)
    (hx : x ∈ boxCL P.n₀ P.u E ρ Cb CA cA PA dlo dhi (pkgXc cB CB Ctr P E ρ Cb CA cA PA) j
      (siteRank d m y)) (hab : x.aborted = false)
    (hrun : ∀ k' < k, (clearingBlock (d := d) (m := m) P.n₀ j P.u y).halted
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k' ω) = false)
    (hne : (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.core
      ≠ ∅)
    (hf : (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.failed
      = false)
    (hdn : (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2.done
      = true) :
    ClearPhase P.n₀ P.u E ρ Cb CA cA PA j (clearingDoneExit x
        (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2) ∧
      PhysicalIdentity E (clearingDoneExit x
        (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω).2) := by
  have hs := localState_reach (tileOrderSize P) _ x ω k hrun
  obtain ⟨D, hpos, -⟩ := hx.2 hjc hab
  have hcover : ∀ i, i ∈ x.endpoint.active ∨ i ∈ x.terminal := (runG_of_clearRec hpos.base).1
  exact ⟨clrOp_donePhase hdone hCtr P E ρ Cb dlo dhi j y hN hj hjc hu ht ht4 x _ hx hab hs hne hf
      hdn,
    hPZ P.n₀ j P.u E y (tileOrderSize P) ω x k (by linarith [hu.1]) hω hTV hab hjc hcover (hx.1.2 hab) hrun hne hf hdn⟩

end AndersonAC.AgentS78
