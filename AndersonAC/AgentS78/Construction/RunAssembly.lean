import AndersonAC.AgentS78.Construction.RunOpsCut
import AndersonAC.AgentS78.Construction.TrueValues

/-!
# Block run of the schedule

`blockRun_of_runOps` constructs a `BlockRun` (BlockRun.lean) for
`scheduleBlocks (runOp P ts₀ cl₀ clr)` from the tile and clearing blocks. Its inputs
include their measurability and query disciplines, tile diameters bounded by
`Ch 4^{(8+ν)j}`, almost-sure reachability, a pathwise invariant and first-trial bound,
the snapshot dichotomy, and the final certificate data. The invariant is maintained
off `exceptionalSet` on records with the true values of `ω`.

`blockRun_of_disciplines` supplies the schedule fields such as slots, scales, pending
sets, labels, late slots, exceptional set, and success event.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources sourcesLaw querySigns)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

/-- **The block run of the schedule.** -/
theorem blockRun_of_runOps (P : TilePlan d m) (E Cr cp cg Ch c : ℝ) (hu : 0 < P.u)
    (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m))
    (rec₀ : RunRecord d m) (hpend₀ : rec₀.pending = ∅) (hrec₀ : rec₀.aborted = false)
    -- tile discipline statements (TileDisciplines.lean) and tile diameters
    (htmark : TileMarkingStatement) (htquery : TileQueryStatement)
    (htpat : TilePatternStatement) (htabort : TileAbortStatement)
    (hdiam : ∀ j (T : Fin (P.cover j).cover.count), ∀ y ∈ tileSites (P.cover j) T,
      physicalDistance d m y (tileAnchor (P.cover j) T) ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
    -- the clearing block
    (hcmeas : ∀ j y, (clr j y).IsMeasurable)
    (hcorders : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω o,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.nextOrder o →
      o ∈ S ∧ ((List.range k).filter fun k' =>
        (clr j y).halted (localState M (clr j y) x k' ω) = false ∧
        (clr j y).next (localState M (clr j y) x k' ω) = Query.nextOrder o).length < M o)
    (hcaux : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω a,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.auxiliary a →
      a ∈ S ∧ ∀ k' < k, (clr j y).halted (localState M (clr j y) x k' ω) = false →
        (clr j y).next (localState M (clr j y) x k' ω) ≠ Query.auxiliary a)
    (hcpatm : ∀ j y, Measurable (clrPat j y))
    (hclocal : ∀ j y x, DependsOnly (Torus d m) (M := tileOrderSize P) (clrPat j y x)
      (localFirstFail (tileOrderSize P) (clr j y) x))
    (hcmark : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ∀ z ∈ ((clr j y).exit s).pending,
        (z ∈ x.pending ∧ ((clr j y).exit s).latest z = x.latest z) ∨
        (((clr j y).exit s).latest z = ⟨j, BirthType.clearing, y⟩ ∧
          (clr j y).firstFail s = true ∧
          physicalDistance d m z y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))))
    (hcabort : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).aborted = true → x.aborted = true)
    (hcquery : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      (∀ k' < k, (clr j y).halted (localState (tileOrderSize P) (clr j y) x k' ω) = false) →
      (clr j y).halted (localState (tileOrderSize P) (clr j y) x k ω) = true →
      declaredFresh ((clr j y).exit (localState (tileOrderSize P) (clr j y) x k ω)) ⊆
        declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((clr j y).exit
          (localState (tileOrderSize P) (clr j y) x k ω)),
        z ∉ querySigns (Torus d m) ((clr j y).next
          (localState (tileOrderSize P) (clr j y) x k' ω)))
    (hcpat : ∀ j y x, (∀ z ∈ (clrPat j y x).signs, z ∈ declaredFresh x) ∧
      (clrPat j y x).orders = ∅)
    -- block reachability: halting
    (hfinite : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) (tileOrderSize P),
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω ≠ ⊤)
    -- run invariant and first-trial bounds (route R2: the invariant is kept only off the
    -- null `exceptionalSet`, on records with the true values of `ω`, jointly with those)
    (Inv : ℕ → Set (RunRecord d m)) (hInv0 : rec₀ ∈ Inv 0)
    (hInv : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
      x ∈ TrueValues P.n₀ P.u ω → x ∈ Inv n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω) = false) →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) = true →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) ∈ Inv (n + 1))
    (hTV0 : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), rec₀ ∈ TrueValues P.n₀ P.u ω)
    (hTV : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
      x ∈ TrueValues P.n₀ P.u ω → x ∈ Inv n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω) = false) →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) = true →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) ∈
          TrueValues P.n₀ P.u ω)
    (hbound : ∀ n, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P)
      (localFirstFail (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x) ≤
        ENNReal.ofReal (birthBound c (slotScaleOf d m n)))
    -- stage dichotomy: snapshot dichotomy at the end of each clearing stage
    (hdich : ∀ j x (ω : RandomSources (Torus d m) (tileOrderSize P)), P.n₀ < j →
      clearingScheduled j m →
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (j + 1)) ω ≠ ⊤ →
      x ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (j + 1)) ω).pending →
      ((blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (j + 1)) ω).latest x).scale = j ∨
      ∃ S : Finset (Torus d m), x ∈ S ∧ stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧
        (∀ y ∈ S, y ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr))
          rec₀ (stageStartIdx d m (j + 1)) ω).pending) ∧
        (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))))
    -- installed values: the final record
    (hfinal : ∀ ω : RandomSources (Torus d m) (tileOrderSize P),
      ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
      (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (m + 2)) ω).aborted = false →
      ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ),
        IsDampedEndpoint s r (OAI.Anderson.scaleHeight m P.u) ∧
        TrueSchurIdentity P.n₀ P.u E (trueConfig ω) s ∧
        Fintype.card (Torus d m) ≤ 2 * s.active.card ∧
        (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧
        (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)) :
    Nonempty (BlockRun d m P.n₀ P.u E Cr cp cg Ch c 1) := by
  have horders := runOps_orders P ts₀ cl₀ clr hcorders
  have haux := runOps_aux P ts₀ cl₀ clr (tileOrderSize P) (fun j y S => hcaux j y _ S)
  exact blockRun_of_disciplines P.n₀ P.u E Cr cp cg Ch c hu (ts₀, cl₀) (tileOrderSize P)
    (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
    (fun n => runOp_measurable P ts₀ cl₀ clr hcmeas _ _ _)
    (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P))
    (runOrderSet_disjoint P) (runAuxSet_disjoint P) horders haux hfinite
    (schedulePattern P clrPat) (schedulePattern_measurable P clrPat hcpatm)
    (runOps_local P ts₀ cl₀ clr clrPat (tileOrderSize P) hclocal)
    (runOps_query P ts₀ cl₀ clr (tileOrderSize P) htquery hcquery)
    (runOps_pat P clrPat htpat hcpat)
    Inv hInv0 (fun ω => TrueValues P.n₀ P.u ω) hInv hTV0 hTV hbound
    (runOps_mark P ts₀ cl₀ clr Ch htmark hdiam hcmark)
    (runOps_empty P ts₀ cl₀ clr) hpend₀ hdich hrec₀ (cutoffIndex d m)
    (runOps_abort P ts₀ cl₀ clr htabort hcabort)
    (fun ω he hc => runOps_cutkeep P ts₀ cl₀ clr (tileOrderSize P) rec₀ _ _
      (runOrderSet_disjoint P) horders haux ω he hc)
    hfinal

end AndersonAC.AgentS78
