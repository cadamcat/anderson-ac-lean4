import AndersonAC.AgentS78.Construction.ClearingBlock
import AndersonAC.AgentS78.Construction.Invariant
import AndersonAC.AgentS78.Construction.RecordFresh
import AndersonAC.AgentS78.Construction.TileBlockFacts
import AndersonAC.AgentS78.Construction.TorusMetric

/-!
# Clearing-block facts for `RunOpsInputs`

For `clr j y := clearingBlock n₀ j u y` (ClearingBlock.lean):

* `clr_reach`: along `BlockReach` the record is the entering record, the scratch core is
  `theCore j u y x`, and `coreLeft ⊆ core`;
* `clr_comp` (`hccomp`), `clr_abort` (`hcabort`), `clr_pat` (`hcpat`), `clr_query`
  (`hcquery`).

The marking facts `hcmark`, `hcrelabel`, and `hckeep` use guarded failure
candidates and the radius clause in `eligibleCand`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer querySigns SignIndex)

section ClearingFacts
variable {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (y : Torus d m)

/-! ## One update -/

theorem clr_update_core (s : RunRecord d m × ClearScratch d m) (a : Answer (Torus d m)) :
    (clearingUpdate (d := d) (m := m) n₀ j u s a).2.core = s.2.core := by
  unfold clearingUpdate
  dsimp only
  split
  · rfl
  · cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
    | fail po => rfl
    | coreReady => rfl
    | heat p hg =>
      dsimp only
      split_ifs <;> rfl
    | coreQuery y _ => rfl
    | finish => rfl

theorem clr_update_inspected (s : RunRecord d m × ClearScratch d m) (a : Answer (Torus d m)) :
    s.2.inspected ⊆ (clearingUpdate (d := d) (m := m) n₀ j u s a).2.inspected := by
  unfold clearingUpdate
  dsimp only
  split
  · exact Finset.Subset.refl _
  · cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
    | fail po =>
      cases po with
      | none => exact Finset.Subset.refl _
      | some p => exact Finset.subset_insert _ _
    | coreReady => exact Finset.Subset.refl _
    | heat p hg =>
      dsimp only
      split_ifs <;> exact Finset.subset_insert _ _
    | coreQuery y _ => exact Finset.Subset.refl _
    | finish => exact Finset.Subset.refl _

theorem clr_update_coreLeft (s : RunRecord d m × ClearScratch d m) (a : Answer (Torus d m))
    (h : s.2.coreLeft ⊆ s.2.core) :
    (clearingUpdate (d := d) (m := m) n₀ j u s a).2.coreLeft ⊆
      (clearingUpdate (d := d) (m := m) n₀ j u s a).2.core := by
  rw [clr_update_core]
  unfold clearingUpdate
  dsimp only
  split
  · exact h
  · cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
    | fail po => exact h
    | coreReady => exact h
    | heat p hg =>
      dsimp only
      split_ifs <;> exact h
    | coreQuery y _ => exact (Finset.erase_subset _ _).trans h
    | finish => exact h

/-! ## Reachable states -/

/-- Along `BlockReach` the record is the entering record, the core is `theCore`, and the
remaining core sites are core sites. -/
theorem clr_reach (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    s.1 = x ∧ s.2.core = theCore (d := d) (m := m) j u y x ∧ s.2.coreLeft ⊆ s.2.core := by
  induction h with
  | enter => exact ⟨rfl, rfl, Finset.Subset.refl _⟩
  | step s a _ _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · show (clearingUpdate (d := d) (m := m) n₀ j u s a).1 = x
      rw [update_fst]; exact ih.1
    · show (clearingUpdate (d := d) (m := m) n₀ j u s a).2.core = _
      rw [clr_update_core]; exact ih.2.1
    · exact clr_update_coreLeft n₀ j u s a ih.2.2

/-! ## The exits -/

theorem clr_exit_cases (s : RunRecord d m × ClearScratch d m) :
    clearingExit (d := d) (m := m) j y s = s.1 ∨
      clearingExit (d := d) (m := m) j y s = clearingFailExit (d := d) (m := m) j y s.1 s.2 ∨
      clearingExit (d := d) (m := m) j y s = clearingDoneExit s.1 s.2 := by
  unfold clearingExit
  split_ifs
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)

/-- `hccomp`: every exit keeps the components. -/
theorem clr_comp (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).components = x.components := by
  rw [← (clr_reach n₀ j u y x s h).1]
  show (clearingExit (d := d) (m := m) j y s).components = s.1.components
  rcases clr_exit_cases j y s with h | h | h <;> rw [h] <;> rfl

/-- `hcabort`: no exit aborts. -/
theorem clr_abort (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s)
    (hab : ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).aborted = true) :
    x.aborted = true := by
  rw [← (clr_reach n₀ j u y x s h).1]
  have : (clearingExit (d := d) (m := m) j y s).aborted = s.1.aborted := by
    rcases clr_exit_cases j y s with h | h | h <;> rw [h] <;> rfl
  rw [← this]; exact hab

/-- `hcpat`: the read pattern is declared fresh and reads no order. -/
theorem clr_pat (x : RunRecord d m) :
    (∀ z ∈ (clearingPattern (d := d) (m := m) n₀ j u y x).signs, z ∈ declaredFresh x) ∧
      (clearingPattern (d := d) (m := m) n₀ j u y x).orders = ∅ := by
  refine ⟨?_, rfl⟩
  rintro z (⟨i, hi, k, hk, rfl⟩ | ⟨a, ha, _⟩)
  · simp only [clearingPattern] at hi hk
    by_cases h1 : x.aborted = true
    · simp [h1] at hi
    by_cases h2 : clearingScheduled j m
    · by_cases h3 : theCore (d := d) (m := m) j u y x = ∅
      · simp [h1, h2, h3] at hi
      · simp [h1, h2, h3, coupledActive] at hi
        exact ⟨by simpa using h1, i, k, rfl, hi.1.2, hi.2, hk⟩
    · simp [h1, h2] at hi
  · simp [clearingPattern] at ha

/-- A fresh coordinate of the exit record is a fresh coordinate of the entering record. -/
theorem clr_exit_fresh (s : RunRecord d m × ClearScratch d m) :
    declaredFresh (clearingExit (d := d) (m := m) j y s) ⊆ declaredFresh s.1 := by
  rcases clr_exit_cases j y s with h | h | h
  · rw [h]
  · rw [h]
    apply declaredFresh_mono
    · intro hab; exact hab
    · intro _ i hp ht
      change i ∉ s.1.pending ∪ s.2.core ∪ s.2.inspected at hp
      change i ∉ s.1.terminal at ht
      simp only [Finset.mem_union, not_or] at hp
      exact ⟨hp.1.1, ht, le_rfl⟩
  · rw [h]
    apply declaredFresh_mono
    · intro hab; exact hab
    · intro _ i hp ht
      change i ∉ s.1.pending \ (s.2.core ∪ s.2.inspected) at hp
      change i ∉ s.1.terminal ∪ s.2.core ∪ s.2.inspected at ht
      simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at hp ht
      refine ⟨fun hpi => ?_, ht.1.1, le_rfl⟩
      by_cases hc : i ∈ s.2.core
      · exact ht.1.2 hc
      · exact ht.2 (hp hpi hc)

/-! ## Queries -/

/-- The site of a core query is a remaining core site. -/
theorem actionOf_coreQuery_mem (rc : RunRecord d m) (sc : ClearScratch d m) (p : Torus d m)
    (hc : sc.corePhase = true)
    (h : actionOf (d := d) (m := m) j u rc sc = .coreQuery p hc) : p ∈ sc.coreLeft := by
  unfold actionOf at h
  by_cases h1 : sc.failed = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : sc.done = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : sc.core = ∅
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3, dif_pos hc] at h
  split at h
  · rename_i y hy
    cases h
    have hmem := List.mem_of_mem_head? hy
    rw [List.mem_mergeSort] at hmem
    exact Finset.mem_toList.mp hmem
  · cases h

/-- A sign read by a running clearing state belongs to a site that the next state has
inspected, or to a remaining core site. -/
theorem clr_next_signs (s : RunRecord d m × ClearScratch d m) (a : Answer (Torus d m))
    (hnh : clearingHalted s = false) :
    ∀ z ∈ querySigns (Torus d m) (clearingNext (d := d) (m := m) n₀ j u s), ∃ p k,
      z = Sum.inl (p, k) ∧
        (p ∈ (clearingUpdate (d := d) (m := m) n₀ j u s a).2.inspected ∨ p ∈ s.2.coreLeft) := by
  intro z hz
  have hnot : ¬ (s.2.failed = true ∨ s.2.done = true) := by
    simp only [clearingHalted, Bool.or_eq_false_iff] at hnh
    simp [hnh.1, hnh.2]
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po => simp [clearingNext, hact, querySigns] at hz
  | coreReady => simp [clearingNext, hact, querySigns] at hz
  | finish => simp [clearingNext, hact, querySigns] at hz
  | coreQuery y hc =>
    simp only [clearingNext, hact, querySigns, Set.mem_setOf_eq] at hz
    obtain ⟨k, _, rfl⟩ := hz
    exact ⟨y, k, rfl, Or.inr (actionOf_coreQuery_mem j u s.1 s.2 y hc hact)⟩
  | heat p hg =>
    simp only [clearingNext, hact, querySigns, Set.mem_setOf_eq] at hz
    obtain ⟨k, _, rfl⟩ := hz
    refine ⟨p, k, rfl, Or.inl ?_⟩
    unfold clearingUpdate
    dsimp only
    rw [if_neg hnot]
    split
    · rename_i po hpo
      rw [hact] at hpo; cases hpo
    · rename_i hpo
      rw [hact] at hpo; cases hpo
    · rename_i p' hg' hpo
      rw [hact] at hpo
      cases hpo
      split_ifs <;> exact Finset.mem_insert_self _ _
    · rename_i y' hpo
      rw [hact] at hpo; cases hpo
    · rename_i hpo
      rw [hact] at hpo; cases hpo

/-- The scratch invariant along the block-local run. -/
theorem clr_local_inv (M : ℕ → ℕ) (x : RunRecord d m) (ω : RandomSources (Torus d m) M)
    (i : ℕ) :
    (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω).1 = x ∧
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω).2.core =
        theCore (d := d) (m := m) j u y x ∧
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω).2.coreLeft ⊆
        (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω).2.core := by
  refine localState_induct M (clearingBlock (d := d) (m := m) n₀ j u y) x
    (fun s => s.1 = x ∧ s.2.core = theCore (d := d) (m := m) j u y x ∧ s.2.coreLeft ⊆ s.2.core)
    ⟨rfl, rfl, Finset.Subset.refl _⟩ ?_ i ω
  intro s a ih
  refine ⟨?_, ?_, ?_⟩
  · show (clearingUpdate (d := d) (m := m) n₀ j u s a).1 = x
    rw [update_fst]; exact ih.1
  · show (clearingUpdate (d := d) (m := m) n₀ j u s a).2.core = _
    rw [clr_update_core]; exact ih.2.1
  · exact clr_update_coreLeft n₀ j u s a ih.2.2

/-- Inspected sites only accumulate along the block-local run. -/
theorem clr_local_inspected_mono (M : ℕ → ℕ) (x : RunRecord d m)
    (ω : RandomSources (Torus d m) M) (a : ℕ) :
    ∀ b, a ≤ b →
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x a ω).2.inspected ⊆
        (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x b ω).2.inspected := by
  intro b hab
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact Finset.Subset.refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · refine (ih (by omega)).trans ?_
      rw [localState_succ]
      exact clr_update_inspected n₀ j u _ _
    · have : a = b + 1 := by omega
      subst this; exact Finset.Subset.refl _

/-- A running block-local state comes from a non-empty block. -/
theorem clr_nonempty_of_running (M : ℕ → ℕ) (x : RunRecord d m)
    (ω : RandomSources (Torus d m) M)
    (h0 : (clearingBlock (d := d) (m := m) n₀ j u y).halted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x 0 ω) = false) :
    x.aborted = false ∧ clearingScheduled j m ∧ theCore (d := d) (m := m) j u y x ≠ ∅ := by
  have hd : (clearInitScratch (d := d) (m := m) j u y x).done = false := by
    have : clearingHalted (x, clearInitScratch (d := d) (m := m) j u y x) = false := h0
    simp only [clearingHalted, Bool.or_eq_false_iff] at this
    exact this.2
  by_contra hne
  have hempty : x.aborted = true ∨ ¬clearingScheduled j m ∨
      theCore (d := d) (m := m) j u y x = ∅ := by
    by_cases ha : x.aborted = true
    · exact Or.inl ha
    · by_cases hs : clearingScheduled j m
      · exact Or.inr (Or.inr (by
          by_contra hc; exact hne ⟨by simpa using ha, hs, hc⟩))
      · exact Or.inr (Or.inl hs)
  rw [init_done_true (j := j) (u := u) (x := y) x hempty] at hd
  exact Bool.noConfusion hd

/-- **`hcquery`** for the clearing block. -/
theorem clr_query (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hnh : ∀ k' < k, (clearingBlock (d := d) (m := m) n₀ j u y).halted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k' ω) = false)
    (hh : (clearingBlock (d := d) (m := m) n₀ j u y).halted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω) = true) :
    declaredFresh ((clearingBlock (d := d) (m := m) n₀ j u y).exit
        (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω)) ⊆ declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((clearingBlock (d := d) (m := m) n₀ j u y).exit
          (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω)),
        z ∉ querySigns (Torus d m) ((clearingBlock (d := d) (m := m) n₀ j u y).next
          (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k' ω)) := by
  set B := clearingBlock (d := d) (m := m) n₀ j u y with hB
  have hinvk := clr_local_inv n₀ j u y M x ω k
  refine ⟨?_, ?_⟩
  · have := clr_exit_fresh j y (localState M B x k ω)
    rw [hinvk.1] at this
    exact this
  intro k' hk' z hz hq
  have hnk' := hnh k' hk'
  obtain ⟨p, kk, rfl, hp⟩ := clr_next_signs n₀ j u (localState M B x k' ω)
    (localAnswer (Torus d m) M (machineRun (Torus d m) M (B.enter x) B.next B.update k' ω).2
      (B.next (localState M B x k' ω)) ω) hnk' _ hq
  have hpk : p ∈ (localState M B x k ω).2.inspected ∨ p ∈ (localState M B x k ω).2.core := by
    rcases hp with hp | hp
    · left
      exact clr_local_inspected_mono n₀ j u y M x ω (k' + 1) k (by omega) hp
    · right
      have h' := (clr_local_inv n₀ j u y M x ω k').2
      rw [hinvk.2.1, ← h'.1]
      exact h'.2 hp
  obtain ⟨hab, hsch, hcore⟩ := clr_nonempty_of_running n₀ j u y M x ω (hnh 0 (by omega))
  obtain ⟨_, i, k2, heq, hip, hit, _⟩ := hz
  have hpi : p = i := (Prod.mk.inj (Sum.inl.inj heq)).1
  subst hpi
  have hcore' : (localState M B x k ω).2.core ≠ ∅ := by rw [hinvk.2.1]; exact hcore
  change p ∉ (clearingExit (d := d) (m := m) j y (localState M B x k ω)).pending at hip
  change p ∉ (clearingExit (d := d) (m := m) j y (localState M B x k ω)).terminal at hit
  have hh' : clearingHalted (localState M B x k ω) = true := hh
  unfold clearingExit at hip hit
  rw [hinvk.1] at hip hit
  simp only [hab, hsch, hcore', Bool.false_eq_true, if_false, decide_true, Bool.not_true]
    at hip hit
  by_cases hf : (localState M B x k ω).2.failed = true
  · rw [if_pos hf] at hip
    apply hip
    change p ∈ x.pending ∪ (localState M B x k ω).2.core ∪ (localState M B x k ω).2.inspected
    rcases hpk with h | h
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  · have hd : (localState M B x k ω).2.done = true := by
      simp only [clearingHalted, Bool.or_eq_true] at hh'
      rcases hh' with h | h
      · exact absurd h hf
      · exact h
    rw [if_neg hf, if_pos hd] at hit
    apply hit
    change p ∈ x.terminal ∪ (localState M B x k ω).2.core ∪ (localState M B x k ω).2.inspected
    rcases hpk with h | h
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

/-! ## The core -/

/-- The parts of `eligibleCand` used by the marking facts (adapt here if the predicate gains
clauses). -/
theorem eligibleCand_parts {B : Finset (Torus d m)}
    (h : eligibleCand (d := d) (m := m) j u y B) :
    y ∈ B ∧ (∀ v ∈ B, (siteRank d m y).val ≤ (siteRank d m v).val) ∧
      (B.card : ℝ) ≤ stageScale u j m ^ (-nu d) :=
  ⟨h.1, h.2.1.2, h.2.2.1⟩

open Classical in
/-- A core site lies in an eligible component of the record. -/
theorem mem_theCore (x : RunRecord d m) {w : Torus d m}
    (hw : w ∈ theCore (d := d) (m := m) j u y x) :
    ∃ B ∈ x.components, eligibleCand (d := d) (m := m) j u y B ∧ w ∈ B := by
  unfold theCore at hw
  dsimp only at hw
  split_ifs at hw with h1
  · obtain ⟨B, hB, hwB⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hBc, hel⟩ := Finset.mem_filter.mp hB
    exact ⟨B, hBc, hel, hwB⟩
  · simp at hw

open Classical in
/-- If `Bc` is the only eligible component anchored at `y`, it is the core. -/
theorem theCore_eq_of_unique (x : RunRecord d m) {Bc : Finset (Torus d m)}
    (hBc : Bc ∈ x.components) (hel : eligibleCand (d := d) (m := m) j u y Bc)
    (huniq : ∀ B ∈ x.components, eligibleCand (d := d) (m := m) j u y B → B = Bc) :
    theCore (d := d) (m := m) j u y x = Bc := by
  have hS : x.components.filter (fun B => eligibleCand (d := d) (m := m) j u y B) = {Bc} := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact huniq B h1 h2
    · rintro rfl; exact ⟨hBc, hel⟩
  unfold theCore
  dsimp only
  rw [hS]
  simp

/-! ## The marking facts, from guarded inspections and a core radius -/

/-- Every inspected site of a reachable state passes the pivot guard. -/
def ClrGuarded (n₀ j : ℕ) (u : ℝ) (y : Torus d m) : Prop :=
  ∀ x s, BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s →
    ∀ p ∈ s.2.inspected, guardHolds (d := d) (m := m) j s.2.core (coupledActive x) x.terminal p

/-- `ClrGuarded` from the guard of the failure candidates : heat pivots
carry their guard evidence. -/
theorem clrGuarded_of_fail
    (hfail : ∀ (rc : RunRecord d m) (sc : ClearScratch d m) (p : Torus d m),
      actionOf (d := d) (m := m) j u rc sc = .fail (some p) →
        guardHolds (d := d) (m := m) j sc.core (coupledActive rc) rc.terminal p) :
    ClrGuarded n₀ j u y := by
  intro x s h
  induction h with
  | enter =>
    intro p hp
    exact absurd hp (Finset.notMem_empty p)
  | step s a hs _ ih =>
    obtain ⟨hx, _, _⟩ := clr_reach n₀ j u y x s hs
    intro p hp
    have hcore : (clearingUpdate (d := d) (m := m) n₀ j u s a).2.core = s.2.core :=
      clr_update_core n₀ j u s a
    change p ∈ (clearingUpdate (d := d) (m := m) n₀ j u s a).2.inspected at hp
    change guardHolds (d := d) (m := m) j
      (clearingUpdate (d := d) (m := m) n₀ j u s a).2.core (coupledActive x) x.terminal p
    rw [hcore]
    subst hx
    unfold clearingUpdate at hp
    dsimp only at hp
    split at hp
    · exact ih p hp
    · cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
      | fail po =>
        rw [hact] at hp
        cases po with
        | none => exact ih p hp
        | some q =>
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact hfail s.1 s.2 p hact
          · exact ih p hp'
      | coreReady => rw [hact] at hp; exact ih p hp
      | finish => rw [hact] at hp; exact ih p hp
      | coreQuery q hq => rw [hact] at hp; exact ih p hp
      | heat q hg =>
        rw [hact] at hp
        dsimp only at hp
        split_ifs at hp <;>
          (rcases Finset.mem_insert.mp hp with rfl | hp'
           · exact hg
           · exact ih p hp')

/-- **`hcmark`** for the clearing block. -/
theorem clr_mark (hg : ClrGuarded n₀ j u y) (R Ch : ℝ)
    (hR : ∀ x, ∀ v ∈ theCore (d := d) (m := m) j u y x, physicalDistance d m v y ≤ R)
    (hRCh : R + inspectionRadius j / 2 ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
    (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s)
    (hh : (clearingBlock (d := d) (m := m) n₀ j u y).halted s = true) :
    ∀ z ∈ ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).pending,
      (z ∈ x.pending ∧ ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).latest z =
          x.latest z) ∨
        (((clearingBlock (d := d) (m := m) n₀ j u y).exit s).latest z =
            ⟨j, BirthType.clearing, y⟩ ∧
          (clearingBlock (d := d) (m := m) n₀ j u y).firstFail s = true ∧
          physicalDistance d m z y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))) := by
  obtain ⟨hx, hcore, _⟩ := clr_reach n₀ j u y x s h
  have hRnn : 0 ≤ inspectionRadius j / 2 := by unfold inspectionRadius; positivity
  intro z hz
  change z ∈ (clearingExit (d := d) (m := m) j y s).pending at hz
  change (z ∈ x.pending ∧ (clearingExit (d := d) (m := m) j y s).latest z = x.latest z) ∨
    ((clearingExit (d := d) (m := m) j y s).latest z = ⟨j, BirthType.clearing, y⟩ ∧
      s.2.failed = true ∧ physicalDistance d m z y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
  unfold clearingExit at hz ⊢
  subst hx
  split_ifs at hz ⊢ with h1 h2 h3 h4 h5
  · exact Or.inl ⟨hz, rfl⟩
  · exact Or.inl ⟨hz, rfl⟩
  · exact Or.inl ⟨hz, rfl⟩
  · -- FAIL exit
    change z ∈ s.1.pending ∪ s.2.core ∪ s.2.inspected at hz
    by_cases hzc : z ∈ s.2.core ∪ s.2.inspected
    · right
      refine ⟨by simp only [clearingFailExit]; rw [if_pos hzc], h4, ?_⟩
      rcases Finset.mem_union.mp hzc with hzc | hzi
      · rw [hcore] at hzc
        exact (hR _ z hzc).trans (by linarith)
      · obtain ⟨_, _, b, hb, hzb⟩ := hg _ s h z hzi
        rw [hcore] at hb
        have htri := (torusConnected_proof d m).dist_triangle (u := z) (v := b) (w := y)
        have hby := hR _ b hb
        calc physicalDistance d m z y ≤ physicalDistance d m z b + physicalDistance d m b y := by
              unfold physicalDistance; exact_mod_cast htri
          _ ≤ inspectionRadius j / 2 + R := add_le_add hzb hby
          _ ≤ _ := by linarith
    · left
      have hzp : z ∈ s.1.pending := by
        rcases Finset.mem_union.mp hz with h' | h'
        · rcases Finset.mem_union.mp h' with h'' | h''
          · exact h''
          · exact absurd (Finset.mem_union_left _ h'') hzc
        · exact absurd (Finset.mem_union_right _ h') hzc
      exact ⟨hzp, by simp only [clearingFailExit]; rw [if_neg hzc]⟩
  · -- DONE exit
    left
    change z ∈ s.1.pending \ (s.2.core ∪ s.2.inspected) at hz
    exact ⟨(Finset.mem_sdiff.mp hz).1, rfl⟩
  · exact Or.inl ⟨hz, rfl⟩

/-- **`hckeep`** for the clearing block. -/
theorem clr_keep (hg : ClrGuarded n₀ j u y) (x : RunRecord d m)
    (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s)
    (_hh : (clearingBlock (d := d) (m := m) n₀ j u y).halted s = true) :
    ∀ w ∈ x.pending, (∀ Bc ∈ x.components, w ∈ Bc → y ∈ Bc →
        (∀ v ∈ Bc, (siteRank d m y).val ≤ (siteRank d m v).val) →
        ¬ ((Bc.card : ℝ) ≤ stageScale u j m ^ (-nu d))) →
      w ∈ ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).pending ∧
        ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).latest w = x.latest w := by
  obtain ⟨hx, hcore, _⟩ := clr_reach n₀ j u y x s h
  intro w hw hnot
  have hwc : w ∉ s.2.core ∪ s.2.inspected := by
    intro hwc
    rcases Finset.mem_union.mp hwc with hwc | hwi
    · rw [hcore] at hwc
      obtain ⟨B, hB, hel, hwB⟩ := mem_theCore j u y x hwc
      obtain ⟨hyB, hanc, hcard⟩ := eligibleCand_parts j u y hel
      exact hnot B hB hwB hyB hanc hcard
    · obtain ⟨hca, _⟩ := hg x s h w hwi
      simp only [coupledActive, Finset.mem_sdiff] at hca
      exact hca.2 hw
  change w ∈ (clearingExit (d := d) (m := m) j y s).pending ∧
    (clearingExit (d := d) (m := m) j y s).latest w = x.latest w
  unfold clearingExit
  subst hx
  split_ifs
  · exact ⟨hw, rfl⟩
  · exact ⟨hw, rfl⟩
  · exact ⟨hw, rfl⟩
  · refine ⟨?_, by simp only [clearingFailExit]; rw [if_neg hwc]⟩
    change w ∈ s.1.pending ∪ s.2.core ∪ s.2.inspected
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hw)
  · exact ⟨Finset.mem_sdiff.mpr ⟨hw, hwc⟩, rfl⟩
  · exact ⟨hw, rfl⟩

/-- **`hcrelabel`** for the clearing block, once the attempted component is the core. -/
theorem clr_relabel_of_core (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s)
    (hh : (clearingBlock (d := d) (m := m) n₀ j u y).halted s = true)
    (hab : x.aborted = false) (hsch : clearingScheduled j m) {Bc : Finset (Torus d m)}
    (hyB : y ∈ Bc) (hcoreEq : theCore (d := d) (m := m) j u y x = Bc) :
    ∀ w ∈ Bc, w ∈ ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).pending →
      ((clearingBlock (d := d) (m := m) n₀ j u y).exit s).latest w =
        ⟨j, BirthType.clearing, y⟩ := by
  obtain ⟨hx, hcore, _⟩ := clr_reach n₀ j u y x s h
  rw [hcoreEq] at hcore
  intro w hwB hwp
  have hne : s.2.core ≠ ∅ := by
    rw [hcore]; exact Finset.ne_empty_of_mem hyB
  have hh' : (s.2.failed || s.2.done) = true := hh
  change w ∈ (clearingExit (d := d) (m := m) j y s).pending at hwp
  change (clearingExit (d := d) (m := m) j y s).latest w = _
  unfold clearingExit at hwp ⊢
  subst hx
  simp only [hab, hsch, hne, Bool.false_eq_true, if_false, decide_true, Bool.not_true]
    at hwp ⊢
  by_cases hf : s.2.failed = true
  · rw [if_pos hf]
    have : w ∈ s.2.core ∪ s.2.inspected := Finset.mem_union_left _ (hcore ▸ hwB)
    simp only [clearingFailExit]; rw [if_pos this]
  · have hd : s.2.done = true := by
      simp only [Bool.or_eq_true] at hh'
      exact hh'.resolve_left hf
    rw [if_neg hf, if_pos hd] at hwp
    change w ∈ s.1.pending \ (s.2.core ∪ s.2.inspected) at hwp
    exact absurd (Finset.mem_union_left _ (hcore ▸ hwB)) (Finset.mem_sdiff.mp hwp).2

end ClearingFacts

end AndersonAC.AgentS78
