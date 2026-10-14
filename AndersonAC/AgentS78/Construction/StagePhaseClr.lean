import AndersonAC.AgentS78.Construction.ClearingHalt
import AndersonAC.AgentS78.Construction.StagePhaseSnoc
import AndersonAC.S6.CoreSchur

/-!
# The clearing block along its reachable states: the structural invariant. For the clearing attempt `clearingBlock n₀ j u y` entered from a record `x`
whose endpoint is damped at `t = t_j` with `x.r` (the clearing-phase data give this), every
reachable scratch state satisfies `ClrInv`:

* the provisional active set lies in the committed one, `Mnum` stays real symmetric, and on the
  provisional active set `hatG` is the damped inverse of the restricted `Mnum` (each
  elimination recomputes it, `elimStep`);
* the core bookkeeping: before the core phase `coreLeft = core`; in the core phase the core
  sites still active are exactly `coreLeft`, and the core lies in the committed active set;
* removed sites are core or inspected sites; a running (non-failed) state has at most `step`
  inspected sites and `step ≤ heatLimit t`;
* a DONE state of a scheduled non-aborted attempt with a nonempty core has finished its core
  phase (`coreLeft = ∅`).

Consequences for a DONE exit (`clr_done_*`): the committed endpoint is damped
(`IsDampedEndpoint`, the field `physical` of `ClearingStepFacts`), nested, and removes the
whole (nonempty) core; the damping `r` is unchanged by every exit; FAIL and empty exits keep
the endpoint.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

section ClrInvSec
variable {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (y : Torus d m)

/-! ## Facts about the action -/

theorem actionOf_heat_facts (rc : RunRecord d m) (sc : ClearScratch d m) (p : Torus d m)
    (hg : guardHolds (d := d) (m := m) j sc.core (coupledActive rc) rc.terminal p)
    (h : actionOf (d := d) (m := m) j u rc sc = .heat p hg) :
    sc.corePhase = false ∧ sc.core ⊆ sc.active ∧ p ∉ sc.core ∧
      sc.step < AndersonAC.S6.heatLimit (stageScale u j m) := by
  unfold actionOf at h
  by_cases h1 : sc.failed = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : sc.done = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : sc.core = ∅
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases hc : sc.corePhase = true
  · rw [dif_pos hc] at h
    split at h <;> cases h
  rw [dif_neg hc] at h
  revert h
  dsimp only
  split_ifs with hA hB hS
  all_goals first
    | (intro h; cases h; done)
    | (split <;> (try split_ifs) <;> intro h <;> first
        | (cases h; done)
        | (cases h; exact ⟨by simpa using hc, hA, by assumption, hS⟩))

theorem actionOf_coreReady_facts (rc : RunRecord d m) (sc : ClearScratch d m)
    (h : actionOf (d := d) (m := m) j u rc sc = .coreReady) :
    sc.corePhase = false ∧ sc.core ⊆ sc.active := by
  unfold actionOf at h
  by_cases h1 : sc.failed = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : sc.done = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : sc.core = ∅
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases hc : sc.corePhase = true
  · rw [dif_pos hc] at h
    split at h <;> cases h
  rw [dif_neg hc] at h
  revert h
  dsimp only
  split_ifs with hA
  all_goals first
    | (intro h; cases h; done)
    | (intro _; exact ⟨by simpa using hc, hA⟩)
    | (split <;> (try split_ifs) <;> intro h <;> first
        | (cases h; done)
        | exact ⟨by simpa using hc, hA⟩)

theorem actionOf_finish_facts (rc : RunRecord d m) (sc : ClearScratch d m)
    (hf : sc.failed = false) (hd : sc.done = false) (hne : sc.core ≠ ∅)
    (h : actionOf (d := d) (m := m) j u rc sc = .finish) :
    sc.corePhase = true ∧ sc.coreLeft = ∅ := by
  unfold actionOf at h
  rw [if_neg (by simp [hf]), if_neg (by simp [hd]), if_neg hne] at h
  by_cases hc : sc.corePhase = true
  · rw [dif_pos hc] at h
    refine ⟨hc, ?_⟩
    split at h
    · cases h
    · rename_i hnone
      rw [List.head?_eq_none_iff] at hnone
      have hl := congrArg List.length hnone
      rw [List.length_mergeSort, List.length_nil] at hl
      exact Finset.toList_eq_nil.mp (List.eq_nil_of_length_eq_zero hl)
  · rw [dif_neg hc] at h
    revert h
    dsimp only
    split_ifs
    all_goals first
      | (intro h; cases h; done)
      | (split <;> (try split_ifs) <;> intro h <;> cases h)

/-! ## The invariant -/

/-- The damped inverse of the restriction of `Mnum` to `A`, padded by zero. -/
def fullInv (A : Finset (Torus d m)) (Mnum : Matrix (Torus d m) (Torus d m) ℝ) (t : ℝ)
    (r : Torus d m → ℂ) : Matrix (Torus d m) (Torus d m) ℂ := fun i k =>
  if h : i ∈ A ∧ k ∈ A then
    AndersonAC.S6.activeInverse (restrictM A Mnum) t (fun a : {a // a ∈ A} => r a.val)
      ⟨i, h.1⟩ ⟨k, h.2⟩
  else 0

/-- **The structural invariant of a reachable clearing scratch state** (entering record `x`). -/
structure ClrInv (x : RunRecord d m) (sc : ClearScratch d m) : Prop where
  sub : sc.active ⊆ x.endpoint.active
  symm : ∀ i k, sc.Mnum i k = sc.Mnum k i
  inv : ∀ i k, i ∈ sc.active → k ∈ sc.active →
    sc.hatG i k = fullInv sc.active sc.Mnum (stageScale u j m) x.r i k
  pre : sc.corePhase = false → sc.coreLeft = sc.core
  post : sc.corePhase = true → sc.core ∩ sc.active = sc.coreLeft ∧ sc.core ⊆ x.endpoint.active
  removed : x.endpoint.active \ sc.active ⊆ sc.core ∪ sc.inspected
  count : sc.failed = false → sc.inspected.card ≤ sc.step
  inspA : sc.failed = false → Disjoint sc.inspected sc.active
  stepLe : sc.step ≤ AndersonAC.S6.heatLimit (stageScale u j m)
  done : sc.done = true → sc.failed = false → x.aborted = false → clearingScheduled j m →
    sc.core ≠ ∅ → sc.corePhase = true ∧ sc.coreLeft = ∅

/-- The damped inverse of a damped endpoint, on its active block. -/
theorem damped_g_eq_activeInverse (x : RunRecord d m) (t : ℝ)
    (hD : IsDampedEndpoint x.endpoint x.r t) (i : Torus d m) (hi : i ∈ x.endpoint.active)
    (k : Torus d m) (hk : k ∈ x.endpoint.active) :
    x.endpoint.g i k = fullInv x.endpoint.active (fun a b => (x.endpoint.M a b).re) t x.r i k := by
  unfold fullInv
  rw [dif_pos ⟨hi, hk⟩]
  obtain ⟨hMs, _, hBG, hGB⟩ := hD
  set A := x.endpoint.active
  have hBeq : x.endpoint.M.submatrix (fun a : A => a.val) (fun a : A => a.val) -
      (t : ℂ) • Matrix.diagonal (fun a : A => x.r a.val) =
      AndersonAC.S6.dampedMatrix (restrictM A (fun a b => (x.endpoint.M a b).re)) t
        (fun a : A => x.r a.val) := by
    ext a b
    simp only [AndersonAC.S6.dampedMatrix, restrictM, Matrix.sub_apply, Matrix.submatrix_apply,
      Matrix.map_apply]
    congr 1
    apply Complex.ext
    · first | rfl | simp
    · simp [(hMs a.val b.val).2]
  rw [hBeq] at hGB
  have := Matrix.inv_eq_left_inv hGB
  have h2 := congrFun (congrFun this ⟨i, hi⟩) ⟨k, hk⟩
  simp only [Matrix.submatrix_apply] at h2
  unfold AndersonAC.S6.activeInverse
  rw [← h2]

/-- The invariant at entry. -/
theorem clrInv_enter (x : RunRecord d m)
    (hD : IsDampedEndpoint x.endpoint x.r (stageScale u j m)) :
    ClrInv j u x (clearInitScratch (d := d) (m := m) j u y x) where
  sub := Finset.Subset.refl _
  symm := fun i k => by
    show (x.endpoint.M i k).re = (x.endpoint.M k i).re
    rw [(hD.1 i k).1]
  inv := fun i k hi hk => damped_g_eq_activeInverse x _ hD i hi k hk
  pre := fun _ => rfl
  post := fun h => by simp [clearInitScratch] at h
  removed := by simp [clearInitScratch]
  count := fun _ => by simp [clearInitScratch]
  inspA := fun _ => by simp [clearInitScratch]
  stepLe := by simp [clearInitScratch]
  done := by
    intro hdone _ hab hsch hne
    exfalso
    simp only [clearInitScratch] at hdone hne
    simp [hab, hsch, hne] at hdone

/-- The elimination step keeps the active-inverse clause. -/
theorem elimStep_inv (t : ℝ) (r : Torus d m → ℂ) (sc : ClearScratch d m) (p : Torus d m) (ξ : ℝ)
    (i k : Torus d m) (hi : i ∈ sc.active.erase p) (hk : k ∈ sc.active.erase p) :
    (elimStep (d := d) (m := m) t r sc p ξ).2 i k =
      fullInv (sc.active.erase p) (elimStep (d := d) (m := m) t r sc p ξ).1 t r i k := by
  unfold elimStep fullInv
  dsimp only
  rw [dif_pos ⟨hi, hk⟩, dif_pos ⟨hi, hk⟩]

theorem elimStep_symm (sc : ClearScratch d m) (p : Torus d m) (ξ : ℝ) (t : ℝ)
    (r : Torus d m → ℂ) (hs : ∀ i k, sc.Mnum i k = sc.Mnum k i) (i k : Torus d m) :
    (elimStep (d := d) (m := m) t r sc p ξ).1 i k = (elimStep (d := d) (m := m) t r sc p ξ).1 k i := by
  unfold elimStep schurStepM
  dsimp only
  by_cases h : i = p ∨ k = p
  · rw [if_pos h, if_pos (Or.comm.mp h)]
    by_cases hik : i = k
    · subst hik; rfl
    · rw [if_neg hik, if_neg (Ne.symm hik)]
  · rw [if_neg h, if_neg (fun h' => h (Or.comm.mp h'))]
    rw [hs i k, hs i p, hs p k, mul_comm (sc.Mnum p i)]

/-- **One update keeps the invariant.** -/
theorem clrInv_update (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (a : Answer (Torus d m)) (hx : s.1 = x) (hI : ClrInv j u x s.2) :
    ClrInv j u x (clearingUpdate (d := d) (m := m) n₀ j u s a).2 := by
  subst hx
  unfold clearingUpdate
  dsimp only
  split
  · exact hI
  rename_i hnot
  have hf : s.2.failed = false := by simpa using (not_or.mp hnot).1
  have hd : s.2.done = false := by simpa using (not_or.mp hnot).2
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po =>
    refine { hI with
      removed := hI.removed.trans (Finset.union_subset_union (Finset.Subset.refl _) ?_)
      count := fun h => by simp at h
      inspA := fun h => by simp at h
      done := fun _ h => by simp at h }
    cases po with
    | none => exact Finset.Subset.refl _
    | some p => exact Finset.subset_insert _ _
  | coreReady =>
    obtain ⟨hcp, hsub⟩ := actionOf_coreReady_facts j u s.1 s.2 hact
    refine { hI with
      pre := fun h => by simp at h
      post := fun _ => ⟨?_, hsub.trans hI.sub⟩
      done := fun h => by simp [hd] at h }
    show s.2.core ∩ s.2.active = s.2.coreLeft
    rw [Finset.inter_eq_left.mpr hsub, hI.pre hcp]
  | finish =>
    refine { hI with done := fun _ hf' hab hsch hne => ?_ }
    exact actionOf_finish_facts j u s.1 s.2 hf hd hne hact
  | coreQuery p hcp =>
    have hmem := actionOf_coreQuery_mem j u s.1 s.2 p hcp hact
    obtain ⟨hpost, hcx⟩ := hI.post hcp
    have hpa : p ∈ s.2.active := (Finset.mem_inter.mp (hpost ▸ hmem : p ∈ s.2.core ∩ s.2.active)).2
    have hpc : p ∈ s.2.core := (Finset.mem_inter.mp (hpost ▸ hmem : p ∈ s.2.core ∩ s.2.active)).1
    dsimp only
    refine
      { sub := ?_, symm := ?_, inv := ?_, pre := ?_, post := ?_, removed := ?_, count := ?_,
        inspA := ?_, stepLe := ?_, done := ?_ }
    · exact (Finset.erase_subset _ _).trans hI.sub
    · intro i k
      exact elimStep_symm s.2 p (residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p 0 a -
        s.1.installed p) (stageScale u j m) s.1.r hI.symm i k
    · intro i k hi hk
      exact elimStep_inv _ _ s.2 p _ i k hi hk
    · intro h; simp [hcp] at h
    · intro _
      refine ⟨?_, hcx⟩
      show s.2.core ∩ s.2.active.erase p = s.2.coreLeft.erase p
      rw [← hpost, Finset.inter_erase]
    · show s.1.endpoint.active \ s.2.active.erase p ⊆ s.2.core ∪ s.2.inspected
      intro z hz
      rw [Finset.mem_sdiff, Finset.mem_erase] at hz
      by_cases hzp : z = p
      · subst hzp; exact Finset.mem_union_left _ hpc
      · exact hI.removed (Finset.mem_sdiff.mpr ⟨hz.1, fun h => hz.2 ⟨hzp, h⟩⟩)
    · exact hI.count
    · intro h
      exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (hI.inspA h)
    · exact hI.stepLe
    · intro hdn _ _ _ _
      refine ⟨hcp, ?_⟩
      simpa using hdn
  | heat p hg =>
    obtain ⟨hcp, hsub, hpc, hstep⟩ := actionOf_heat_facts j u s.1 s.2 p hg hact
    have hpre := hI.pre hcp
    dsimp only
    split_ifs
    all_goals
      refine
        { sub := ?_, symm := ?_, inv := ?_, pre := ?_, post := ?_, removed := ?_, count := ?_,
          inspA := ?_, stepLe := ?_, done := ?_ }
    all_goals first
      | exact (Finset.erase_subset _ _).trans hI.sub
      | (intro i k
         exact elimStep_symm s.2 p (residOfAnswer (d := d) (m := m) (clearingLam n₀ u) p
           (s.1.prefixLength p) a) (stageScale u j m) s.1.r hI.symm i k)
      | (intro i k hi hk; exact elimStep_inv _ _ s.2 p _ i k hi hk)
      | (intro _; exact hpre)
      | (intro _
         refine ⟨?_, hsub.trans hI.sub⟩
         show s.2.core ∩ s.2.active.erase p = s.2.coreLeft
         rw [hpre, Finset.inter_eq_left]
         intro z hz
         exact Finset.mem_erase.mpr ⟨fun h => hpc (h ▸ hz), hsub hz⟩)
      | (show s.1.endpoint.active \ s.2.active.erase p ⊆ s.2.core ∪ insert p s.2.inspected
         intro z hz
         rw [Finset.mem_sdiff, Finset.mem_erase] at hz
         by_cases hzp : z = p
         · subst hzp; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
         · rcases Finset.mem_union.mp (hI.removed (Finset.mem_sdiff.mpr ⟨hz.1,
             fun h => hz.2 ⟨hzp, h⟩⟩)) with h | h
           · exact Finset.mem_union_left _ h
           · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h))
      | (intro _
         show (insert p s.2.inspected).card ≤ s.2.step + 1
         exact (Finset.card_insert_le _ _).trans (by have := hI.count hf; omega))
      | (intro _
         show Disjoint (insert p s.2.inspected) (s.2.active.erase p)
         rw [Finset.disjoint_insert_left]
         exact ⟨Finset.notMem_erase _ _,
           Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (hI.inspA hf)⟩)
      | (show s.2.step + 1 ≤ _; omega)
      | (intro h; exfalso; revert h; show ¬ (s.2.done = true); simp [hd])

/-- **The invariant along every reachable state** (arbitrary answers). -/
theorem clrInv_reach (x : RunRecord d m)
    (hD : IsDampedEndpoint x.endpoint x.r (stageScale u j m))
    (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    ClrInv j u x s.2 := by
  induction h with
  | enter => exact clrInv_enter j u y x hD
  | step s a hs _ ih =>
    exact clrInv_update n₀ j u x s a (clr_reach n₀ j u y x s hs).1 ih

end ClrInvSec

end AndersonAC.AgentS78
