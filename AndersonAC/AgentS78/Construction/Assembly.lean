import AndersonAC.AgentS78.Construction.SimpleDisciplines
import AndersonAC.AgentS78.Construction.RecordFresh
import AndersonAC.AgentS78.Construction.AbortTrace
import AndersonAC.AgentS78.Construction.Exceptional
import AndersonAC.AgentS78.Construction.Schedule
import AndersonAC.AgentS78.Construction.PathwiseInvariant

/-!
# WP10 construction, layer E: a `BlockRun` from the per-block disciplines

`blockRun_of_disciplines` assembles one finite-volume `BlockRun` (BlockRun.lean) on the
committed records `RunRecord d m` from the per-block properties of a block family:
measurability and the order/auxiliary disciplines (C3), halting a.s. (C4d), the read pattern
and its locality, the query discipline against `declaredFresh` (C5a), a propagated record
invariant with the frozen first-trial bound on it (C4, C5b), the marking discipline with the
schedule labels `opLabel` (C5c), the per-stage snapshot dichotomy at the stage ends (C5c),
the abort discipline (late failures and the cutoff, C5d) and the final-record facts (C5d).
Every other field is computed here: slots and scales from the schedule (`slotIndex`,
`slotScaleOf`), pending sets and labels read at the stage starts `stageStartIdx`, the late
slots `lateSlots`, the exceptional set (singular true principal blocks, or the final block
never reached), success = "the final record is not aborted".
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query sourcesLaw querySigns SignIndex)

/-- The first block of stage `j` (`opIndex d m j 0` of the least site). -/
def stageStartIdx (d m j : ℕ) : ℕ := 4 * j * siteCount d m

theorem measurableSet_pending_mem {d m : ℕ} (x : Torus d m) :
    MeasurableSet {r : RunRecord d m | x ∈ r.pending} := by
  have hm : Measurable (fun r : RunRecord d m => (RunRecord.code r).2.2.2.2.1.2.1 x) :=
    (measurable_pi_apply x).comp (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (RunRecord.measurable_code d m))))))))
  have hset : {r : RunRecord d m | x ∈ r.pending} =
      (fun r : RunRecord d m => (RunRecord.code r).2.2.2.2.1.2.1 x) ⁻¹' {true} := by
    ext r
    simp [RunRecord.code, finsetCode]
  rw [hset]
  exact hm (measurableSet_singleton true)

/-- Almost every sample lies off the exceptional set. -/
theorem ae_notMem_exceptionalSet {d m : ℕ} (n₀ : ℕ) {u : ℝ} (hu : 0 < u) (E : ℝ) (M : ℕ → ℕ) :
    ∀ᵐ ω ∂sourcesLaw (Torus d m) M, ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M :=
  measure_eq_zero_iff_ae_notMem.mp (exceptionalSet_null n₀ hu E M)

/-- **Assembly of a block run from the per-block disciplines.** -/
theorem blockRun_of_disciplines {d m : ℕ} (n₀ : ℕ) (u E Cr cp cg Ch c : ℝ) (hu : 0 < u)
    {Sc : Type} [MeasurableSpace Sc] (sc₀ : Sc) (M : ℕ → ℕ)
    (blocks : ℕ → Block (Torus d m) (RunRecord d m) (RunRecord d m × Sc))
    (rec₀ : RunRecord d m) (hmeas : ∀ n, (blocks n).IsMeasurable)
    (orderSet auxSet : ℕ → Set ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (hauxdisj : Pairwise fun n n' => Disjoint (auxSet n) (auxSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    -- C4d: every block is reached almost surely
    (hfinite : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) M, blockStart M blocks rec₀ n ω ≠ ⊤)
    -- read patterns
    (pattern : ℕ → RunRecord d m → FreshPattern (Torus d m))
    (hpatm : ∀ n, Measurable (pattern n))
    (hlocal : ∀ n x, DependsOnly (Torus d m) (pattern n x) (localFirstFail M (blocks n) x))
    -- C5a: query discipline against the declared-fresh signs
    (hquery : ∀ n x k (ω : RandomSources (Torus d m) M),
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      declaredFresh ((blocks n).exit (localState M (blocks n) x k ω)) ⊆ declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((blocks n).exit (localState M (blocks n) x k ω)),
        z ∉ querySigns (Torus d m) ((blocks n).next (localState M (blocks n) x k' ω)))
    (hpat : ∀ n x, (∀ z ∈ (pattern n x).signs,
        z ∈ declaredFresh x ∨ ∃ a ∈ auxSet n, z = Sum.inr a) ∧
      ∀ o ∈ (pattern n x).orders, o ∈ orderSet n)
    -- C5b + C4: invariant and first-trial bound
    -- (route R2: kept only off the null `exceptionalSet`, on records in the companion set
    -- `TV ω` — `TrueValues n₀ u ω` in the run, which is kept jointly)
    (Inv : ℕ → Set (RunRecord d m)) (hInv0 : rec₀ ∈ Inv 0)
    (TV : RandomSources (Torus d m) M → Set (RunRecord d m))
    (hInv : ∀ n x k (ω : RandomSources (Torus d m) M),
      ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M → x ∈ TV ω → x ∈ Inv n →
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      (blocks n).exit (localState M (blocks n) x k ω) ∈ Inv (n + 1))
    (hTV0 : ∀ ω : RandomSources (Torus d m) M, rec₀ ∈ TV ω)
    (hTV : ∀ n x k (ω : RandomSources (Torus d m) M),
      ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M → x ∈ TV ω → x ∈ Inv n →
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      (blocks n).exit (localState M (blocks n) x k ω) ∈ TV ω)
    (hbound : ∀ n, ∀ x ∈ Inv n, sourcesLaw (Torus d m) M (localFirstFail M (blocks n) x) ≤
      ENNReal.ofReal (birthBound c (slotScaleOf d m n)))
    -- C5c: marking discipline with the schedule labels
    (hmark : ∀ n x s, BlockReach (blocks n) x s → (blocks n).halted s = true →
      ∀ y ∈ ((blocks n).exit s).pending,
        (y ∈ x.pending ∧ ((blocks n).exit s).latest y = x.latest y) ∨
        (((blocks n).exit s).latest y = opLabel d m n ∧ (blocks n).firstFail s = true ∧
          (physicalDistance d m y (opLabel d m n).anchor ≤
            Ch * (4 : ℝ) ^ ((8 + nu d) * ((opLabel d m n).scale : ℝ)) ∧
            slotIndex (opLabel d m n) = n)))
    -- before the run proper
    (hempty : ∀ n < stageStartIdx d m (n₀ + 1), blocks n = simpleBlock sc₀ id)
    (hpend₀ : rec₀.pending = ∅)
    -- C5c: the snapshot dichotomy at the end of a clearing stage
    (hdich : ∀ j x (ω : RandomSources (Torus d m) M), n₀ < j → clearingScheduled j m →
      blockStart M blocks rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤ →
      x ∈ (blockPrestate M blocks rec₀ (stageStartIdx d m (j + 1)) ω).pending →
      ((blockPrestate M blocks rec₀ (stageStartIdx d m (j + 1)) ω).latest x).scale = j ∨
      ∃ S : Finset (Torus d m), x ∈ S ∧ stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧
        (∀ y ∈ S, y ∈ (blockPrestate M blocks rec₀ (stageStartIdx d m (j + 1)) ω).pending) ∧
        (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))))
    -- C5d: abort discipline (late first failures, the cutoff block `ncut`)
    (hrec₀ : rec₀.aborted = false) (ncut : ℕ)
    (habort : ∀ n x s, BlockReach (blocks n) x s → (blocks n).halted s = true →
      ((blocks n).exit s).aborted = true → x.aborted = true ∨
        ((blocks n).firstFail s = true ∧ n ∈ lateSlots d m) ∨ (n = ncut ∧ x.pending.Nonempty))
    (hcutkeep : ∀ ω : RandomSources (Torus d m) M,
      blockStart M blocks rec₀ (stageStartIdx d m (m / 2 + 1)) ω ≠ ⊤ →
      blockStart M blocks rec₀ ncut ω ≠ ⊤ →
      (blockPrestate M blocks rec₀ ncut ω).pending ⊆
        (blockPrestate M blocks rec₀ (stageStartIdx d m (m / 2 + 1)) ω).pending)
    -- C5d: the final record (after the final residual sweep, stage `m + 1`)
    (hfinal : ∀ ω : RandomSources (Torus d m) M,
      ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M →
      blockStart M blocks rec₀ (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
      (blockPrestate M blocks rec₀ (stageStartIdx d m (m + 2)) ω).aborted = false →
      ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ),
        IsDampedEndpoint s r (OAI.Anderson.scaleHeight m u) ∧
        TrueSchurIdentity n₀ u E (trueConfig ω) s ∧
        Fintype.card (Torus d m) ≤ 2 * s.active.card ∧
        (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧
        (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)) :
    Nonempty (BlockRun d m n₀ u E Cr cp cg Ch c 1) := by
  classical
  obtain ⟨hQ, hstart, hmono, hprest, hloc, hbirth⟩ := blockComposition_proof machineRun_proof
    (Torus d m) M (RunRecord d m) (RunRecord d m × Sc) blocks rec₀ hmeas orderSet hdisj auxSet
    hauxdisj horders haux
  set e : ℕ → ℕ := fun j => stageStartIdx d m (j + 1) with he_def
  set fin := stageStartIdx d m (m + 2) with hfin
  have hreach_meas : ∀ n, MeasurableSet {ω : RandomSources (Torus d m) M |
      blockStart M blocks rec₀ n ω ≠ ⊤} := by
    intro n
    have hset : {ω : RandomSources (Torus d m) M | blockStart M blocks rec₀ n ω ≠ ⊤} =
        ⋃ i : ℕ, {ω | blockStart M blocks rec₀ n ω = (i : WithTop ℕ)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h; exact ⟨(blockStart M blocks rec₀ n ω).untop h, (WithTop.coe_untop _ h).symm⟩
      · rintro ⟨i, hi⟩; rw [hi]; exact WithTop.coe_ne_top
    rw [hset]
    exact MeasurableSet.iUnion fun i =>
      (retainedFiltration (Torus d m) hQ).le i _ ((hstart n).measurableSet_eq i)
  have hprest_meas : ∀ n, Measurable (blockPrestate M blocks rec₀ n) := fun n =>
    (hprest n).mono (hstart n).measurableSpace_le le_rfl
  let exc : Set (RandomSources (Torus d m) M) :=
    exceptionalSet (d := d) (m := m) n₀ u E M ∪ {ω | blockStart M blocks rec₀ fin ω = ⊤}
  refine ⟨{
    M := M
    Rec := RunRecord d m
    St := RunRecord d m × Sc
    blocks := blocks
    rec₀ := rec₀
    blocks_measurable := hmeas
    orderSet := orderSet
    orderSet_disjoint := hdisj
    auxSet := auxSet
    auxSet_disjoint := hauxdisj
    orders := horders
    aux := haux
    slotScale := slotScaleOf d m
    slot := slotIndex
    slot_injective := slotIndex_injective d m
    slot_scale := slotScaleOf_slotIndex
    start_finite := hfinite
    pattern := pattern
    pattern_measurable := hpatm
    fail_local := hlocal
    fresh := fun n => by
      filter_upwards [hfinite n] with ω hω
      exact fresh_of_declared_aux M blocks rec₀ orderSet auxSet hdisj hauxdisj horders haux
        declaredFresh hquery pattern hpat n ω hω
    good := Inv
    prestate_good := fun n => by
      filter_upwards [hfinite n, ae_notMem_exceptionalSet n₀ hu E M] with ω hω hexc
      exact (blockPrestate_mem_joint M blocks rec₀ orderSet auxSet hdisj horders haux ω Inv
        (TV ω) (fun n x k hx hi hk hh => hInv n x k ω hexc hx hi hk hh)
        (fun n x k hx hi hk hh => hTV n x k ω hexc hx hi hk hh) hInv0 (hTV0 ω) n hω).1
    product_bound := hbound
    pending := fun j x => {ω | blockStart M blocks rec₀ (e j) ω ≠ ⊤ ∧
      x ∈ (blockPrestate M blocks rec₀ (e j) ω).pending}
    latest := fun j x ω => (blockPrestate M blocks rec₀ (e j) ω).latest x
    pending_measurable := fun j x =>
      (hreach_meas (e j)).inter ((hprest_meas (e j)) (measurableSet_pending_mem x))
    before := ?_
    step := ?_
    dichotomy := ?_
    late := lateSlots d m
    late_card := lateSlots_card d m
    late_scale := lateSlots_scale d m
    exceptional := exc
    exceptional_null := ?_
    success := {ω | blockStart M blocks rec₀ fin ω ≠ ⊤ ∧
      (blockPrestate M blocks rec₀ fin ω).aborted = false} \ exc
    failure_cover := ?_
    certificate := ?_ }⟩
  · -- before
    intro j x hj
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hst
    have hle : e j ≤ stageStartIdx d m (n₀ + 1) := by
      simp only [he_def, stageStartIdx]
      exact Nat.mul_le_mul_right _ (by omega)
    rw [prestate_eq_init_of_empty M sc₀ blocks rec₀ _ hempty (e j) hle ω hst, hpend₀]
    exact Finset.notMem_empty x
  · -- step
    exact step_of_marking blocks rec₀ orderSet auxSet M hdisj horders haux
      RunRecord.pending RunRecord.latest (opLabel d m) slotIndex Ch e n₀
      (fun j => by simp only [he_def, stageStartIdx]; exact Nat.mul_le_mul_right _ (by omega))
      (fun j n _ h1 h2 => opLabel_scale d m (j + 1) n h1 (by
        simp only [he_def, stageStartIdx] at h2; exact h2))
      hmark hloc
  · -- dichotomy
    intro j x ω hj hsch hω
    rcases hdich j x ω hj hsch hω.1 hω.2 with h | ⟨S, hxS, hcard, hpend, hdist⟩
    · exact Or.inl h
    · exact Or.inr ⟨S, hxS, hcard, fun y hy => ⟨hω.1, hpend y hy⟩, hdist⟩
  · -- exceptional_null
    refine measure_union_null (exceptionalSet_null n₀ hu E M) ?_
    have h := hfinite fin
    rw [ae_iff] at h
    simpa using h
  · -- failure_cover
    intro ω hω
    by_cases hexc : ω ∈ exc
    · exact Or.inr hexc
    · have hreach : blockStart M blocks rec₀ fin ω ≠ ⊤ := fun h => hexc (Or.inr h)
      have hab : (blockPrestate M blocks rec₀ fin ω).aborted = true := by
        by_contra hne
        exact hω ⟨⟨hreach, by simpa using hne⟩, hexc⟩
      obtain ⟨n, hn, hns, hcause⟩ := abort_cover M blocks rec₀ orderSet auxSet hdisj horders haux
        (fun x => x.aborted = true) (fun n => n ∈ lateSlots d m)
        (fun n x => n = ncut ∧ x.pending.Nonempty) habort hloc (by simp [hrec₀]) ω fin hreach hab
      rcases hcause with ⟨hf, hl⟩ | ⟨rfl, y, hy⟩
      · exact Or.inl (Or.inr (Set.mem_biUnion hl ⟨hns, hf⟩))
      · have hle : stageStartIdx d m (m / 2 + 1) ≤ fin := by
          simp only [hfin, stageStartIdx]; exact Nat.mul_le_mul_right _ (by omega)
        have hreach' := reached_of_le M blocks rec₀ orderSet auxSet hdisj horders haux ω fin
          hreach _ hle
        exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨y, hreach', hcutkeep ω hreach' hns hy⟩))
  · -- certificate
    rintro ω ⟨⟨hreach, hnab⟩, hexc⟩
    have hnot : ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M := fun h => hexc (Or.inl h)
    obtain ⟨s, r, hs, hphys, hcard, hr, hlag⟩ := hfinal ω hnot hreach hnab
    exact certificate_of_final_record n₀ u E Cr cp cg (trueConfig ω) s r hs hphys hcard hr hlag
      (terminal_invertible n₀ u E M ω hnot s.active)

end AndersonAC.AgentS78
