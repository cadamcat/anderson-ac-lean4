import AndersonAC.AgentS78.Construction.RunOpsInputs
import AndersonAC.AgentS78.Construction.ClearingSnap
import AndersonAC.AgentS78.Construction.ClearingHalt
import AndersonAC.AgentS78.Construction.TileCoverFinal

/-!
# Per-box assembly with the clearing block

`RunOpsInputs` uses `clr j y := clearingBlock n₀ j u y` and the plan from
`tilePlan_exists`. `ClearingFacts`, `ClearingHalt`, and `ClearingSnap` provide the
clearing-block facts. The assembly combines the tile disciplines, clearing-block
measurability and geometry, and the per-box `BoxInvariant` for the run, trial bounds,
halting, and final record.

`uniformCertificateInput_of_boxInvariants` assembles these hypotheses into a uniform
certificate input.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources sourcesLaw querySigns)

variable {d m : ℕ}

/-- The clearing blocks of a box. -/
abbrev clrOf (n₀ : ℕ) (u : ℝ) : ℕ → Torus d m → Block (Torus d m) (RunRecord d m)
    (RunRecord d m × ClearScratch d m) :=
  fun j y => clearingBlock (d := d) (m := m) n₀ j u y

/-- : a failure candidate is marked only if it passes the pivot guard. -/
def ClearingFailGuarded (d m : ℕ) : Prop :=
  ∀ (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc : ClearScratch d m) (p : Torus d m),
    actionOf (d := d) (m := m) j u rc sc = .fail (some p) →
      guardHolds (d := d) (m := m) j sc.core (coupledActive rc) rc.terminal p

/-- : the core lies within `t_j^{-ν} R_j` of its anchor. -/
def ClearingCoreRadius (d m : ℕ) : Prop :=
  ∀ (j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m), ∀ v ∈ theCore (d := d) (m := m) j u y x,
    physicalDistance d m v y ≤ stageScale u j m ^ (-nu d) * separationRadius j

/-- , converse: an anchored component with at most `t_j^{-ν}` sites inside
that radius is an eligible candidate. -/
def ClearingEligibleIntro (d m : ℕ) : Prop :=
  ∀ (j : ℕ) (u : ℝ) (y : Torus d m) (B : Finset (Torus d m)), y ∈ B →
    (∀ v ∈ B, (siteRank d m y).val ≤ (siteRank d m v).val) →
    (B.card : ℝ) ≤ stageScale u j m ^ (-nu d) →
    (∀ v ∈ B, physicalDistance d m v y ≤ stageScale u j m ^ (-nu d) * separationRadius j) →
    eligibleCand (d := d) (m := m) j u y B

/-- **The run invariant package of one box** (for the schedule with the clearing block). -/
structure BoxInvariant (d m n₀ : ℕ) (u E Cr cp cg c : ℝ) (P : TilePlan d m) where
  ts₀ : TileScratch d m
  cl₀ : ClearScratch d m
  rec₀ : RunRecord d m
  hpend₀ : rec₀.pending = ∅
  hrec₀ : rec₀.aborted = false
  Inv : ℕ → Set (RunRecord d m)
  hInv0 : rec₀ ∈ Inv 0
  /-- route R2: kept only off the null `exceptionalSet`, on records with the true values of `ω` -/
  hInv : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
    ω ∉ exceptionalSet (d := d) (m := m) n₀ u E (tileOrderSize P) → x ∈ TrueValues n₀ u ω →
    x ∈ Inv n →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) = false) →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) = true →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈ Inv (n + 1)
  hTV0 : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), rec₀ ∈ TrueValues n₀ u ω
  /-- the true installed values are kept jointly with `Inv` -/
  hTV : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
    ω ∉ exceptionalSet (d := d) (m := m) n₀ u E (tileOrderSize P) → x ∈ TrueValues n₀ u ω →
    x ∈ Inv n →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) = false) →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) = true →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
        TrueValues n₀ u ω
  hbound : ∀ n, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P) (localFirstFail (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x) ≤ ENNReal.ofReal (birthBound c (slotScaleOf d m n))
  hfinal : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), ω ∉ exceptionalSet (d := d) (m := m) n₀ u E (tileOrderSize P) → blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))) rec₀ (stageStartIdx d m (m + 2)) ω ≠ ⊤ → (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))) rec₀ (stageStartIdx d m (m + 2)) ω).aborted = false → ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ), IsDampedEndpoint s r (OAI.Anderson.scaleHeight m P.u) ∧ TrueSchurIdentity P.n₀ P.u E (trueConfig ω) s ∧ Fintype.card (Torus d m) ≤ 2 * s.active.card ∧ (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧ (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)
  ε : ℕ → ℕ → ℝ
  hε0 : ∀ n k, 0 ≤ ε n k
  hε : ∀ n, Filter.Tendsto (ε n) Filter.atTop (nhds 0)
  hhalt : ∀ n k, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P) (notHalted (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k) ≤ ENNReal.ofReal (ε n k)

/-- `RunOpsInputs` of one box from the run invariant package. -/
theorem runOpsInputs_of_box {n₀ : ℕ} {u E Cr cp cg c : ℝ} (Ch : ℝ) (P : TilePlan d m)
    (hn₀ : P.n₀ = n₀) (hu : P.u = u) (hu4 : 1 / 4 < u) (hu1 : u ≤ 1)
    (C : ℝ) (hfacts : ∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j))
    (hCh1 : (4 : ℝ) ^ 6 * C ≤ Ch) (hCh2 : u ^ (-nu d) + 1 ≤ Ch) (hCh : 1 ≤ Ch)
    (htmark : TileMarkingStatement) (htquery : TileQueryStatement)
    (htpat : TilePatternStatement) (htabort : TileAbortStatement)
    (hthalt : TileHaltPatternStatement)
    (hcmeas : ∀ j y, (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hfailG : ClearingFailGuarded d m) (hrad : ClearingCoreRadius d m)
    (helig : ClearingEligibleIntro d m)
    (B : BoxInvariant d m n₀ u E Cr cp cg c P) :
    Nonempty (RunOpsInputs d m n₀ u E Cr cp cg Ch c) := by
  subst hn₀ hu
  have hu0 : 0 < P.u := by linarith
  have hR : ∀ j, 0 ≤ stageScale P.u j m ^ (-nu d) * separationRadius j := by
    intro j
    have : 0 < stageScale P.u j m := by unfold stageScale; positivity
    unfold separationRadius; positivity
  refine ⟨{
    P := P
    hu := hu0
    ClSc := ClearScratch d m
    ts₀ := B.ts₀
    cl₀ := B.cl₀
    clr := clrOf P.n₀ P.u
    clrPat := fun j y => clearingPattern (d := d) (m := m) P.n₀ j P.u y
    rec₀ := B.rec₀
    hpend₀ := B.hpend₀
    hrec₀ := B.hrec₀
    htmark := htmark
    htquery := htquery
    htpat := htpat
    htabort := htabort
    hdiam := fun j T y hy => ((hfacts j).diam T y hy).trans (mul_le_mul_of_nonneg_right hCh1
      (by positivity))
    hcmeas := hcmeas
    hcorders := fun j y M S => clearingBlock_orders P.n₀ j P.u y M S
    hcaux := fun j y M S => clearingBlock_aux P.n₀ j P.u y M S
    hcpatm := fun j y => clearingPattern_measurable P.n₀ j P.u y
    hclocal := fun j y x => clearingBlock_fail_local P.n₀ j P.u y _ x
    hcmark := fun j y x s hs hh => clr_mark P.n₀ j P.u y
      (clrGuarded_of_fail P.n₀ j P.u y (fun rc sc p h => hfailG j P.u rc sc p h))
      (stageScale P.u j m ^ (-nu d) * separationRadius j) Ch
      (fun x' v hv => hrad j P.u y x' v hv) (clear_mark_radius P.u hu0 j Ch hCh2) x s hs hh
    hcabort := fun j y x s hs _ hab => clr_abort P.n₀ j P.u y x s hs hab
    hcquery := fun j y x k ω hk hh => clr_query P.n₀ j P.u y _ x k ω hk hh
    hcpat := fun j y x => clr_pat P.n₀ j P.u y x
    Inv := B.Inv
    hInv0 := B.hInv0
    hInv := B.hInv
    hTV0 := B.hTV0
    hTV := B.hTV
    hbound := B.hbound
    hfinal := B.hfinal
    hthalt := hthalt
    Kc := clearingHaltBound d m P.u
    hchalt := fun j y x k ω hk => clr_halts P.n₀ j P.u y _ x k ω hk
    ε := B.ε
    hε0 := B.hε0
    hε := B.hε
    hhalt := B.hhalt
    hCh := hCh
    huI := ⟨hu0, hu1⟩
    hccomp := fun j y x s hs _ => clr_comp P.n₀ j P.u y x s hs
    hcrelabel := ?_
    hckeep := fun j z x s hs hh => clr_keep P.n₀ j P.u z
      (clrGuarded_of_fail P.n₀ j P.u z (fun rc sc p h => hfailG j P.u rc sc p h)) x s hs hh
    hn₀ := rfl
    hu' := rfl }⟩
  intro j z x s hs hh hab hsch ⟨R, hcomp⟩ Bc hBc hzB hmin hcard
  have hBc' := hBc
  rw [hcomp] at hBc'
  obtain ⟨hz, hBeq⟩ := eq_snapComp_of_mem R (separationRadius j) Bc hBc' z hzB
  have hsep : 0 ≤ separationRadius j := by unfold separationRadius; positivity
  have hradB : ∀ v ∈ Bc, physicalDistance d m v z ≤
      stageScale P.u j m ^ (-nu d) * separationRadius j := by
    rw [hBeq]
    exact snapComp_radius_real R (separationRadius j) hsep z hz _ (hBeq ▸ hcard)
  have hel := helig j P.u z Bc hzB hmin hcard hradB
  exact clr_relabel_of_core P.n₀ j P.u z x s hs hh hab hsch hzB
    (theCore_snapshot j P.u z x R (separationRadius j) hcomp hBc hel)

theorem upow_le_four_pow (u : ℝ) (hu4 : 1 / 4 < u) : u ^ (-nu d) ≤ (4 : ℝ) ^ (nu d) := by
  have hν : 0 ≤ nu d := by unfold nu delta; positivity
  have h1 : u ^ (-nu d) ≤ (1 / 4 : ℝ) ^ (-nu d) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hu4.le (by linarith)
  have h2 : (1 / 4 : ℝ) ^ (-nu d) = (4 : ℝ) ^ (nu d) := by
    rw [Real.rpow_neg (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      one_div, inv_inv]
  linarith

/-- Assembles `S78.UniformCertificateInput d e₂` from the tile disciplines,
clearing-block measurability, and uniform run-invariant packages for each large box
and tile plan with the cover facts. -/
theorem uniformCertificateInput_of_boxInvariants (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (htmark : TileMarkingStatement) (htquery : TileQueryStatement)
    (htpat : TilePatternStatement) (htabort : TileAbortStatement)
    (hthalt : TileHaltPatternStatement)
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hfailG : ∀ m, ClearingFailGuarded d m) (hrad : ∀ m, ClearingCoreRadius d m)
    (helig : ∀ m, ClearingEligibleIntro d m)
    (hbox : ∀ C : ℝ, 1 ≤ C → ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariant d m n₀ u E Cr cp cg c P)) :
    UniformCertificateInput d e₂ := by
  obtain ⟨C, hC, hplan⟩ := tilePlan_exists d
  obtain ⟨Cr, cp, cg, c, hcp, hcg, hc, N₀, hN⟩ := hbox C hC
  set Ch : ℝ := (4 : ℝ) ^ 6 * C + (4 : ℝ) ^ (nu d) + 1 with hChdef
  have h4ν : 0 ≤ (4 : ℝ) ^ (nu d) := by positivity
  have hCh : 1 ≤ Ch := by
    have : 0 ≤ (4 : ℝ) ^ 6 * C := by positivity
    linarith
  refine uniformCertificateInput_of_runOpsInputs d hd e₂ Cr cp cg Ch c hcp hcg hCh hc (max N₀ 1)
    (fun n₀ m h1 h2 u hu E hE => ?_)
  obtain ⟨P, hPn, hPu, hfacts⟩ := hplan m n₀ u (by omega) (by omega) hu.1 hu.2
  obtain ⟨B⟩ := hN n₀ m (le_of_max_le_left h1) h2 u hu E hE P hPn hPu hfacts
  exact runOpsInputs_of_box Ch P hPn hPu hu.1 hu.2 C hfacts (by linarith)
    (by have := upow_le_four_pow (d := d) u hu.1; have : 0 ≤ (4 : ℝ) ^ 6 * C := by positivity
        linarith) hCh
    htmark htquery htpat htabort hthalt (fun j y => hcmeas m n₀ j u y) (hfailG m) (hrad m)
    (helig m) B

end AndersonAC.AgentS78
