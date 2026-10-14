import AndersonAC.AgentS78.Construction.RunOpsFinite
import AndersonAC.AgentS78.Construction.TrueValues

/-!
# blocks reached a.s. under an invariant kept off a null set (route R2)

`all_blocks_reached_of_good_ev`: `all_blocks_reached_of_inv_ev` with the pathwise closure of the
invariant replaced by its almost-sure validity at every reached block start.
`runOps_finite_det_tv`: `runOps_finite_det` for an invariant `Inv` that each block keeps only for
`ω ∉ exceptionalSet` and records in `TrueValues n₀ u ω`; the joint induction with
`TrueValues` gives the
almost-sure invariant (`blockPrestate_mem_joint`).
-/

open MeasureTheory Filter Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources Answer sourcesLaw querySigns ObeysQueryRules)

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
  [MeasurableSpace Rec]

/-- `all_blocks_reached_of_inv_ev` with an almost-sure invariant at reached block starts. -/
theorem all_blocks_reached_of_good_ev (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
    (orderSet auxSet : ℕ → Set ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (hQ : ObeysQueryRules ι (runQ M blocks rec₀))
    (hstart : ∀ n, IsStoppingTime (retainedFiltration ι hQ) (blockStart M blocks rec₀ n))
    (hprest : ∀ n, Measurable[(hstart n).measurableSpace] (blockPrestate M blocks rec₀ n))
    (K : ℕ → ℕ) (pat : ℕ → ℕ → Rec → FreshPattern ι)
    (hpat : ∀ n k, K n ≤ k → Measurable (pat n k))
    (hmeasNH : ∀ n k, K n ≤ k →
      MeasurableSet {p : Rec × RandomSources ι M | p.2 ∈ notHalted M (blocks n) p.1 k})
    (hloc : ∀ n k, K n ≤ k → ∀ x, DependsOnly ι (pat n k x) (notHalted M (blocks n) x k))
    (hfresh : ∀ n k, K n ≤ k → ∀ (ω : RandomSources ι M), blockStart M blocks rec₀ n ω ≠ ⊤ →
      UnqueriedAt ι (runQ M blocks rec₀)
        ((blockStart M blocks rec₀ n ω).untopD 0) (pat n k (blockPrestate M blocks rec₀ n ω)) ω)
    (Inv : ℕ → Set Rec)
    (hgood : ∀ᵐ ω ∂sourcesLaw ι M, ∀ n, blockStart M blocks rec₀ n ω ≠ ⊤ →
      blockPrestate M blocks rec₀ n ω ∈ Inv n)
    (ε : ℕ → ℕ → ℝ) (hε0 : ∀ n k, 0 ≤ ε n k) (hε : ∀ n, Tendsto (ε n) atTop (𝓝 0))
    (hbound : ∀ n k, K n ≤ k → ∀ x ∈ Inv n,
      sourcesLaw ι M (notHalted M (blocks n) x k) ≤ ENNReal.ofReal (ε n k)) :
    ∀ n, ∀ᵐ ω ∂sourcesLaw ι M, blockStart M blocks rec₀ n ω ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet
      (BlocksProof.entered_zero M blocks rec₀ orderSet auxSet ω)]
    exact WithTop.coe_ne_top
  | succ n ih =>
    have hgood' : ∀ᵐ ω ∂sourcesLaw ι M, blockPrestate M blocks rec₀ n ω ∈ Inv n := by
      filter_upwards [ih, hgood] with ω hω hg
      exact hg n hω
    have hfr : ∀ k, K n ≤ k → ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι (runQ M blocks rec₀)
        ((blockStart M blocks rec₀ n ω).untopD 0) (pat n k (blockPrestate M blocks rec₀ n ω)) ω :=
      fun k hk => by
        filter_upwards [ih] with ω hω
        exact hfresh n k hk ω hω
    exact next_block_reached_ev M blocks rec₀ orderSet auxSet hdisj horders haux hQ n (hstart n) ih
      (hprest n) (K n) (pat n) (hpat n) (hmeasNH n) (hloc n) hfr (Inv n) hgood' (ε n)
      (hε0 n) (hε n) (hbound n)

end Generic

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

theorem runOps_finite_det_tv (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (rec₀ : RunRecord d m)
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
    (htquery : TileQueryStatement)
    (hcquery : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      (∀ k' < k, (clr j y).halted (localState (tileOrderSize P) (clr j y) x k' ω) = false) →
      (clr j y).halted (localState (tileOrderSize P) (clr j y) x k ω) = true →
      declaredFresh ((clr j y).exit (localState (tileOrderSize P) (clr j y) x k ω)) ⊆
        declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((clr j y).exit
          (localState (tileOrderSize P) (clr j y) x k ω)),
        z ∉ querySigns (Torus d m) ((clr j y).next
          (localState (tileOrderSize P) (clr j y) x k' ω)))
    (hthalt : TileHaltPatternStatement)
    (Kc : ℕ) (hchalt : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)), Kc ≤ k →
      ω ∉ notHalted (tileOrderSize P) (clr j y) x k)
    (hu : 0 < P.u) (E : ℝ)
    (Inv : ℕ → Set (RunRecord d m)) (h₀ : rec₀ ∈ Inv 0)
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
    (ε : ℕ → ℕ → ℝ) (hε0 : ∀ n k, 0 ≤ ε n k) (hε : ∀ n, Tendsto (ε n) atTop (𝓝 0))
    (hbound : ∀ n k, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P)
      (notHalted (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k) ≤
        ENNReal.ofReal (ε n k)) :
    ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) (tileOrderSize P),
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω ≠ ⊤ := by
  have horders := runOps_orders P ts₀ cl₀ clr hcorders
  have haux := runOps_aux P ts₀ cl₀ clr (tileOrderSize P) (fun j y S => hcaux j y _ S)
  obtain ⟨hQ, hstart, -, hprest, -, -⟩ := blockComposition_proof machineRun_proof (Torus d m)
    (tileOrderSize P) (RunRecord d m) (RunRecord d m × (TileScratch d m × ClSc))
    (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (fun n => runOp_measurable P ts₀ cl₀ clr hcmeas _ _ _)
    (scheduleSets (runOrderSet P)) (runOrderSet_disjoint P) (scheduleSets (runAuxSet P))
    (runAuxSet_disjoint P) horders haux
  set clrHalt : ℕ → Torus d m → ℕ → RunRecord d m → FreshPattern (Torus d m) :=
    fun _ _ _ _ => emptyPattern d m with hclrHalt
  have hquery := runOps_query P ts₀ cl₀ clr (tileOrderSize P) htquery hcquery
  have hnh : ∀ j y x k, Kc ≤ k → notHalted (tileOrderSize P) (clr j y) x k = ∅ := by
    intro j y x k hk
    ext ω
    simp only [Set.mem_empty_iff_false, iff_false]
    exact hchalt j y x k ω hk
  have hgood : ∀ᵐ ω ∂sourcesLaw (Torus d m) (tileOrderSize P), ∀ n,
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω ≠ ⊤ →
      blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω ∈ Inv n := by
    filter_upwards [ae_notMem_exceptionalSet P.n₀ hu E (tileOrderSize P)] with ω hexc n hn
    exact (blockPrestate_mem_joint (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
      (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
      horders haux ω Inv (TrueValues P.n₀ P.u ω)
      (fun n x k hx hi hk hh => hInv n x k ω hexc hx hi hk hh)
      (fun n x k hx hi hk hh => hTV n x k ω hexc hx hi hk hh) h₀ (hTV0 ω) n hn).1
  refine all_blocks_reached_of_good_ev (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr))
    rec₀ (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
    horders haux hQ hstart hprest (fun _ => Kc) (scheduleHaltPattern P clrHalt) ?_ ?_ ?_ ?_ Inv
    hgood ε hε0 hε (fun n k _ => hbound n k)
  · intro n k _
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, -, -, -, hp⟩ | ⟨j, y, -, -, -, hp⟩ |
      ⟨f, -, -, -, hp⟩ <;> rw [hp]
    · exact (hthalt d m P j T (tileOrderSize P) k).1
    · exact measurable_const
    · exact measurable_const
  · intro n k hk
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, hB, -, -, -⟩ | ⟨j, y, hB, -, -, -⟩ |
      ⟨f, hB, -, -, -⟩ <;> rw [hB]
    · simp only [notHalted_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed cl₀) tileProj
        (fun _ => rfl)]
      exact (hthalt d m P j T (tileOrderSize P) k).2.1
    · simp only [notHalted_embed (tileOrderSize P) (clr j y) (clearEmbed ts₀) clearProj
        (fun _ => rfl)]
      simp only [hnh j y _ k hk, Set.mem_empty_iff_false, Set.ofPred_false]
      exact MeasurableSet.empty
    · simp only [notHalted_simple, Set.mem_empty_iff_false, Set.ofPred_false]
      exact MeasurableSet.empty
  · intro n k hk x
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, hB, -, -, hp⟩ | ⟨j, y, hB, -, -, hp⟩ |
      ⟨f, hB, -, -, hp⟩ <;> rw [hB, hp]
    · rw [notHalted_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed cl₀) tileProj
        (fun _ => rfl)]
      exact (hthalt d m P j T (tileOrderSize P) k).2.2 x
    · rw [notHalted_embed (tileOrderSize P) (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl)]
      rw [hnh j y x k hk]
      intro ω ω' _ _
      simp
    · rw [notHalted_simple]
      intro ω ω' _ _
      simp
  · intro n k _ ω hn
    refine fresh_of_declared_aux (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
      (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
      (runAuxSet_disjoint P) horders haux declaredFresh hquery
      (fun n => scheduleHaltPattern P clrHalt n k) (fun n' x => ?_) n ω hn
    rcases block_shape P ts₀ cl₀ clr clrHalt n' with ⟨j, T, -, hO, hA, hp⟩ |
      ⟨j, y, -, hO, hA, hp⟩ | ⟨f, -, hO, hA, hp⟩ <;> simp only [hO, hA, hp]
    · exact tileHaltPattern_disc P j T k x
    · refine ⟨fun z hz => ?_, fun o ho => ?_⟩
      · change z ∈ (emptyPattern d m).signs at hz
        rw [emptyPattern_signs] at hz; exact absurd hz (Set.notMem_empty z)
      · change o ∈ (emptyPattern d m).orders at ho
        simp [emptyPattern] at ho
    · refine ⟨fun z hz => ?_, fun o ho => ?_⟩
      · rw [emptyPattern_signs] at hz; exact absurd hz (Set.notMem_empty z)
      · simp [emptyPattern] at ho

end AndersonAC.AgentS78
