import AndersonAC.AgentS78.Construction.QueryRun
import AndersonAC.AgentS78.Construction.BlocksProof
import AndersonAC.AgentS78.Construction.MachineRunProof

/-!
# A run represented by its blocks

`BlockRun` consists of measurable blocks, one per schedule operation, with query
disciplines, fresh patterns, first-trial bounds, and run invariants for freshness,
prestates, marking, success, and certificates. `queryRun_of_blockRun` builds a
`QueryRun` using `MachineRunStatement` and `BlockCompositionStatement`. Each block's
slot is its schedule index.
-/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query ObeysQueryRules sourcesLaw Answer)

/-- One finite-volume run given by its blocks. -/
structure BlockRun (d m n₀ : ℕ) (u E Cr cp cg Ch c Clate : ℝ) where
  M : ℕ → ℕ
  Rec : Type
  St : Type
  [mRec : MeasurableSpace Rec]
  [mSt : MeasurableSpace St]
  blocks : ℕ → Block (Torus d m) Rec St
  rec₀ : Rec
  blocks_measurable : ∀ n, (blocks n).IsMeasurable
  orderSet : ℕ → Set ℕ
  orderSet_disjoint : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n')
  auxSet : ℕ → Set ℕ
  auxSet_disjoint : Pairwise fun n n' => Disjoint (auxSet n) (auxSet n')
  orders : ∀ n x k ω o, (blocks n).halted (localState M (blocks n) x k ω) = false →
    (blocks n).next (localState M (blocks n) x k ω) = Query.nextOrder o →
    o ∈ orderSet n ∧
    ((List.range k).filter fun k' =>
      (blocks n).halted (localState M (blocks n) x k' ω) = false ∧
      (blocks n).next (localState M (blocks n) x k' ω) = Query.nextOrder o).length < M o
  aux : ∀ n x k ω a, (blocks n).halted (localState M (blocks n) x k ω) = false →
    (blocks n).next (localState M (blocks n) x k ω) = Query.auxiliary a →
    a ∈ auxSet n ∧ ∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false →
      (blocks n).next (localState M (blocks n) x k' ω) ≠ Query.auxiliary a
  slotScale : ℕ → ℕ
  slot : BirthLabel (Torus d m) → ℕ
  slot_injective : Function.Injective slot
  slot_scale : ∀ a, slotScale (slot a) = a.scale
  /-- block reachability: every block is reached almost surely (retries terminate). -/
  start_finite : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) M, blockStart M blocks rec₀ n ω ≠ ⊤
  pattern : ℕ → Rec → FreshPattern (Torus d m)
  pattern_measurable : ∀ n, Measurable (pattern n)
  /-- the first trial reads only its pattern. -/
  fail_local : ∀ n x, DependsOnly (Torus d m) (pattern n x) (localFirstFail M (blocks n) x)
  /-- freshness: the pattern is unqueried when the block is entered. -/
  fresh : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) M,
    AgentS78.UnqueriedAt (Torus d m) (runQ M blocks rec₀)
      ((blockStart M blocks rec₀ n ω).untopD 0) (pattern n (blockPrestate M blocks rec₀ n ω)) ω
  good : ℕ → Set Rec
  /-- run invariant: entering records satisfy the trial hypotheses (deterministic induction). -/
  prestate_good : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) M, blockPrestate M blocks rec₀ n ω ∈ good n
  /-- The probability bound for a block's first trial. -/
  product_bound : ∀ n, ∀ x ∈ good n, sourcesLaw (Torus d m) M (localFirstFail M (blocks n) x) ≤
    ENNReal.ofReal (birthBound c (slotScale n))
  pending : ℕ → Torus d m → Set (RandomSources (Torus d m) M)
  latest : ℕ → Torus d m → RandomSources (Torus d m) M → BirthLabel (Torus d m)
  pending_measurable : ∀ j x, MeasurableSet (pending j x)
  before : ∀ j x, j ≤ n₀ → pending j x = ∅
  /-- stage dichotomy: status/marking rule. -/
  step : ∀ j x ω, n₀ ≤ j → ω ∈ pending (j + 1) x →
    (ω ∈ pending j x ∧ latest (j + 1) x ω = latest j x ω) ∨
    ((latest (j + 1) x ω).scale = j + 1 ∧
      (blockStart M blocks rec₀ (slot (latest (j + 1) x ω)) ω ≠ ⊤ ∧
        ω ∈ localFirstFail M (blocks (slot (latest (j + 1) x ω)))
          (blockPrestate M blocks rec₀ (slot (latest (j + 1) x ω)) ω)) ∧
      physicalDistance d m x (latest (j + 1) x ω).anchor ≤
        Ch * (4 : ℝ) ^ ((8 + nu d) * (((j + 1 : ℕ) : ℝ))))
  dichotomy : ∀ j x ω, n₀ < j → clearingScheduled j m → ω ∈ pending j x →
    ((latest j x ω).scale = j) ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
      stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, ω ∈ pending j y) ∧
      (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
  late : Finset ℕ
  late_card : (late.card : ℝ) ≤ Clate * ((m : ℝ) + 1) * (4 : ℝ) ^ (20 * d * m)
  late_scale : ∀ n ∈ late, m / 2 ≤ slotScale n
  exceptional : Set (RandomSources (Torus d m) M)
  exceptional_null : sourcesLaw (Torus d m) M exceptional = 0
  success : Set (RandomSources (Torus d m) M)
  /-- installed values: the two abort rules. -/
  failure_cover : successᶜ ⊆ (⋃ x, pending (m / 2) x) ∪
    (⋃ n ∈ late, {ω | blockStart M blocks rec₀ n ω ≠ ⊤ ∧
      ω ∈ localFirstFail M (blocks n) (blockPrestate M blocks rec₀ n ω)}) ∪ exceptional
  /-- installed values: the final certificate. -/
  certificate : success ⊆ trueConfig ⁻¹' boundedCertificateEvent d n₀ m u E Cr cp cg

attribute [instance] BlockRun.mRec BlockRun.mSt

/-- Joint measurability of the block-local first failure. -/
theorem localFirstFail_measurable (hmach : MachineRunStatement) {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type} [MeasurableSpace Rec] [MeasurableSpace St]
    (B : Block ι Rec St) (hB : B.IsMeasurable) :
    MeasurableSet {p : Rec × RandomSources ι M | p.2 ∈ localFirstFail M B p.1} := by
  have hloc : ∀ k, Measurable (fun p : Rec × RandomSources ι M => localState M B p.1 k p.2) :=
    fun k => (hmach ι M St B.next hB.next B.update hB.update).2.2 Rec B.enter hB.enter k
  have hset : {p : Rec × RandomSources ι M | p.2 ∈ localFirstFail M B p.1} =
      ⋃ k, ((⋂ k' ∈ Finset.range k,
        {p : Rec × RandomSources ι M | B.halted (localState M B p.1 k' p.2) = false}) ∩
        {p | B.firstFail (localState M B p.1 k p.2) = true}) := by
    ext p
    simp only [localFirstFail, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range]
  rw [hset]
  refine MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.biInter (Finset.range k).countable_toSet fun k' _ => ?_
    exact (hB.halted.comp (hloc k')) (measurableSet_singleton false)
  · exact (hB.firstFail.comp (hloc k)) (measurableSet_singleton true)

/-- **Layer D glue.** A block run defines a query run. -/
theorem queryRun_of_blockRun (hmach : MachineRunStatement) (hcomp : BlockCompositionStatement)
    {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ} (R : BlockRun d m n₀ u E Cr cp cg Ch c Clate) :
    Nonempty (QueryRun d m n₀ u E Cr cp cg Ch c Clate) := by
  obtain ⟨hQ, hstart, hmono, hprest, hlocal, hbirth⟩ := hcomp (Torus d m) R.M R.Rec R.St
    R.blocks R.rec₀ R.blocks_measurable R.orderSet R.orderSet_disjoint R.auxSet
    R.auxSet_disjoint R.orders R.aux
  refine ⟨{
    M := R.M
    Q := runQ R.M R.blocks R.rec₀
    rules := hQ
    start := blockStart R.M R.blocks R.rec₀
    start_stopping := hstart
    start_mono := hmono
    start_finite := R.start_finite
    slotScale := R.slotScale
    slot := R.slot
    slot_injective := R.slot_injective
    slot_scale := R.slot_scale
    S := R.Rec
    prestate := blockPrestate R.M R.blocks R.rec₀
    prestate_measurable := hprest
    pattern := R.pattern
    pattern_measurable := R.pattern_measurable
    fail := fun n => localFirstFail R.M (R.blocks n)
    fail_measurable := fun n => localFirstFail_measurable hmach R.M (R.blocks n)
      (R.blocks_measurable n)
    fail_local := R.fail_local
    fresh := R.fresh
    good := R.good
    prestate_good := R.prestate_good
    product_bound := R.product_bound
    birth_adapted := ?_
    pending := R.pending
    latest := R.latest
    pending_measurable := R.pending_measurable
    before := R.before
    step := R.step
    dichotomy := R.dichotomy
    late := R.late
    late_card := R.late_card
    late_scale := R.late_scale
    exceptional := R.exceptional
    exceptional_null := R.exceptional_null
    success := R.success
    failure_cover := R.failure_cover
    certificate := R.certificate }⟩
  intro n
  have hset : {ω | blockStart R.M R.blocks R.rec₀ n ω ≠ ⊤ ∧
      ω ∈ localFirstFail R.M (R.blocks n) (blockPrestate R.M R.blocks R.rec₀ n ω)} =
      globalFirstFail R.M R.blocks R.rec₀ n ∩ {ω | blockStart R.M R.blocks R.rec₀ n ω ≠ ⊤} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hlocal n ω h1).mpr h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, (hlocal n ω h1).mp h2⟩
  rw [hset]
  exact hbirth n

/-- **Reduction of `UniformCertificateInput` to block runs with uniform constants**,
conditional only on the contract machine run (`MachineRunStatement`); block composition is
`blockComposition_proof`. -/
theorem uniformCertificateInput_of_blockRuns
    (hmach : MachineRunStatement)
    (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (Cr cp cg Ch c Clate : ℝ) (hcp : 0 < cp) (hcg : 0 < cg) (hCh : 1 ≤ Ch) (hc : 0 < c)
    (hClate : 0 ≤ Clate) (N₀ : ℕ)
    (hrun : ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      Nonempty (BlockRun d m n₀ u E Cr cp cg Ch c Clate)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_queryRuns d hd e₂ Cr cp cg Ch c Clate hcp hcg hCh hc hClate N₀
    (fun n₀ m h1 h2 u hu E hE => by
      obtain ⟨R⟩ := hrun n₀ m h1 h2 u hu E hE
      exact queryRun_of_blockRun hmach (blockComposition_proof hmach) R)

/-- **Unconditional reduction of `UniformCertificateInput` to block runs with uniform
constants** (`machineRun_proof`). -/
theorem uniformCertificateInput_of_blockRuns'
    (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (Cr cp cg Ch c Clate : ℝ) (hcp : 0 < cp) (hcg : 0 < cg) (hCh : 1 ≤ Ch) (hc : 0 < c)
    (hClate : 0 ≤ Clate) (N₀ : ℕ)
    (hrun : ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      Nonempty (BlockRun d m n₀ u E Cr cp cg Ch c Clate)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_blockRuns machineRun_proof d hd e₂ Cr cp cg Ch c Clate hcp hcg hCh
    hc hClate N₀ hrun

end AndersonAC.AgentS78
