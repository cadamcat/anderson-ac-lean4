import AndersonAC.AgentS78.Construction.StagePhaseDone
import AndersonAC.AgentS78.Construction.StagePhaseClrExit

/-!
# The DONE exit of a clearing attempt: the core-phase snapshot

agent-s78donea. Along every reachable state of `clearingBlock n₀ j u y` from `x`, once the core
phase has started (and no failure latched) there is a **snapshot** `sh` of the scratch state at
the start of the core phase (06-clearing.tex:826–857, the DONE output of the stopped trial;
07-assembly.tex:399–405):

* the S6 heat budgets hold for `sh.hatG` against the frozen `g0 = x.endpoint.g` (they are checked
  after every heat, `clearingUpdate`, and before every action, `actionOf`);
* on `sh.active` the snapshot inverse is the damped inverse of the restricted `sh.Mnum`;
* the core lies in `sh.active`, and the projection cap `xReady` holds there
  (`candPivot = none` is impossible: the ridge stays `≥ 0`, so the weights are `≥ 0`);
* the current `(active, Mnum)` arise from `(sh.active, sh.Mnum)` by sequential core
  eliminations (`CoreElim`, the core-suffix phase).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.DoneA

open AndersonAC.S78 AndersonAC.AgentS78
open AndersonAC.S2 (Answer)

variable {d m : ℕ}

/-- **Sequential core eliminations** from `(A, M)`: each step Schur-eliminates a core site of
the current active set with an arbitrary real shift (`schurStepM`, the core-suffix phase). -/
inductive CoreElim (core A : Finset (Torus d m)) (M : Matrix (Torus d m) (Torus d m) ℝ) :
    Finset (Torus d m) → Matrix (Torus d m) (Torus d m) ℝ → Prop
  | refl : CoreElim core A M A M
  | step {A' : Finset (Torus d m)} {M' : Matrix (Torus d m) (Torus d m) ℝ} (p : Torus d m) (ξ : ℝ) :
      CoreElim core A M A' M' → p ∈ A' → p ∈ core →
      CoreElim core A M (A'.erase p) (schurStepM M' p ξ)

theorem CoreElim.sub {core A A' : Finset (Torus d m)} {M M' : Matrix (Torus d m) (Torus d m) ℝ}
    (h : CoreElim core A M A' M') : A' ⊆ A ∧ A \ A' ⊆ core := by
  induction h with
  | refl => exact ⟨Finset.Subset.refl _, by simp⟩
  | step p ξ _ hp hc ih =>
    refine ⟨(Finset.erase_subset _ _).trans ih.1, ?_⟩
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_erase] at hz
    by_cases hzp : z = p
    · exact hzp ▸ hc
    · exact ih.2 (Finset.mem_sdiff.mpr ⟨hz.1, fun h => hz.2 ⟨hzp, h⟩⟩)

/-- The snapshot clauses at the start of the core phase. -/
structure Snap (t : ℝ) (r : Torus d m → ℂ) (g0 : Matrix (Torus d m) (Torus d m) ℂ)
    (sh : ClearScratch d m) : Prop where
  budgets : AndersonAC.S6.BudgetsHold t g0 sh.hatG
  inv : ∀ i k, i ∈ sh.active → k ∈ sh.active → sh.hatG i k = fullInv sh.active sh.Mnum t r i k
  symm : ∀ i k, sh.Mnum i k = sh.Mnum k i
  coreSub : sh.core ⊆ sh.active
  ready : xReady t r sh.active (restrictM sh.active sh.Mnum) sh.core

/-- **The snapshot invariant** of a reachable clearing scratch state. -/
structure SnapInv (j : ℕ) (u : ℝ) (x : RunRecord d m) (sc : ClearScratch d m) : Prop where
  g0 : sc.g0 = x.endpoint.g
  ridge : 0 ≤ sc.ridge
  snap : sc.failed = false → sc.corePhase = true →
    ∃ sh : ClearScratch d m, Snap (stageScale u j m) x.r x.endpoint.g sh ∧ sh.core = sc.core ∧
      sh.active ⊆ x.endpoint.active ∧
      CoreElim sc.core sh.active sh.Mnum sc.active sc.Mnum

/-! ## Weights are nonnegative, so a candidate pivot exists -/

theorem leastMaximizer_ne_none {ι : Type*} [Fintype ι] [DecidableEq ι]
    (order : ι ≃ Fin (Fintype.card ι)) (w : ι → ℝ) (i : ι)
    (hi : w i = AndersonAC.S6.maxWeight w) : AndersonAC.S6.leastMaximizer order w ≠ none := by
  unfold AndersonAC.S6.leastMaximizer
  intro h
  rw [Option.map_eq_none_iff, List.head?_eq_none_iff] at h
  have hmem : order i ∈ (Finset.univ.filter
      (fun j => w (order.symm j) = AndersonAC.S6.maxWeight w)).sort (· ≤ ·) := by
    rw [Finset.mem_sort]; simp [hi]
  rw [h] at hmem
  simp at hmem

theorem exists_eq_maxWeight {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : ∃ i, w i = AndersonAC.S6.maxWeight w := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
    (fun i => Real.toNNReal (w i))
  refine ⟨i, ?_⟩
  unfold AndersonAC.S6.maxWeight
  rw [hi, Real.coe_toNNReal _ (hw i)]

theorem candPivot_ne_none (r : Torus d m → ℂ) (sc : ClearScratch d m) (t τ : ℝ) (hτ : 0 ≤ τ) :
    candPivot r sc t τ ≠ none := by
  haveI : Nonempty (Torus d m) := ⟨fun _ => 0⟩
  obtain ⟨i, hi⟩ := exists_eq_maxWeight (scratchWeights t r sc τ)
    (fun i => AndersonAC.AgentS6.leverage_nonneg _ hτ i)
  exact leastMaximizer_ne_none _ _ i hi

theorem chooseRidge_nonneg {R B : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
    (C : Matrix R B ℂ) (l τ : ℝ) (hτ : 0 ≤ τ) : 0 ≤ AndersonAC.S6.chooseRidge C l τ := by
  unfold AndersonAC.S6.chooseRidge
  split_ifs
  · unfold AndersonAC.S6.ridgeThreshold
    exact Real.sSup_nonneg fun x hx => hx.1.le
  · exact hτ

/-! ## The action leading into the core phase -/

theorem actionOf_coreReady_snap (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc : ClearScratch d m)
    (h : actionOf (d := d) (m := m) j u rc sc = .coreReady) :
    AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc.hatG ∧
      (xReady (stageScale u j m) rc.r sc.active (restrictM sc.active sc.Mnum) sc.core ∨
        candPivot rc.r sc (stageScale u j m) sc.ridge = none) := by
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
  split_ifs with hA hB hS hW hX
  all_goals first
    | (intro h; cases h; done)
    | (intro _; exact ⟨hB, Or.inl hX⟩)
    | (split
       · split_ifs <;> intro h <;> cases h
       · rename_i hnone; intro _; exact ⟨hB, Or.inr hnone⟩)

/-! ## The invariant -/

section Reach
variable (n₀ j : ℕ) (u : ℝ) (y : Torus d m)

theorem snapInv_enter (x : RunRecord d m) :
    SnapInv j u x (clearInitScratch (d := d) (m := m) j u y x) where
  g0 := rfl
  ridge := by
    simp only [clearInitScratch]
    apply chooseRidge_nonneg
    exact Even.zpow_nonneg ⟨-1, by norm_num⟩ _
  snap := fun _ h => by simp [clearInitScratch] at h

/-- **One update keeps the snapshot invariant.** -/
theorem snapInv_update (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (a : Answer (Torus d m)) (hx : s.1 = x) (hI : ClrInv j u x s.2) (hS : SnapInv j u x s.2) :
    SnapInv j u x (clearingUpdate (d := d) (m := m) n₀ j u s a).2 := by
  subst hx
  unfold clearingUpdate
  dsimp only
  split
  · exact hS
  rename_i hnot
  have hf : s.2.failed = false := by simpa using (not_or.mp hnot).1
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po =>
    exact { g0 := hS.g0, ridge := hS.ridge, snap := fun h => by simp at h }
  | coreReady =>
    obtain ⟨hcp, hsub⟩ := actionOf_coreReady_facts j u s.1 s.2 hact
    obtain ⟨hB, hR⟩ := actionOf_coreReady_snap j u s.1 s.2 hact
    refine { g0 := hS.g0, ridge := hS.ridge, snap := fun _ _ => ?_ }
    refine ⟨s.2, ⟨hS.g0 ▸ hB, hI.inv, hI.symm, hsub,
      hR.resolve_right (candPivot_ne_none _ _ _ _ hS.ridge)⟩, rfl, hI.sub, CoreElim.refl⟩
  | finish =>
    exact { g0 := hS.g0, ridge := hS.ridge, snap := fun hf' hc' => hS.snap hf' hc' }
  | coreQuery p hcp =>
    have hmem := actionOf_coreQuery_mem j u s.1 s.2 p hcp hact
    obtain ⟨hpost, -⟩ := hI.post hcp
    have hpa : p ∈ s.2.active :=
      (Finset.mem_inter.mp (hpost ▸ hmem : p ∈ s.2.core ∩ s.2.active)).2
    have hpc : p ∈ s.2.core :=
      (Finset.mem_inter.mp (hpost ▸ hmem : p ∈ s.2.core ∩ s.2.active)).1
    refine { g0 := hS.g0, ridge := hS.ridge, snap := fun _ _ => ?_ }
    obtain ⟨sh, hsh, hcore, hsub, hce⟩ := hS.snap hf hcp
    exact ⟨sh, hsh, hcore, hsub, CoreElim.step p _ hce hpa hpc⟩
  | heat p hg =>
    obtain ⟨hcp, hsub, hpc, -⟩ := actionOf_heat_facts j u s.1 s.2 p hg hact
    have hpa : s.2.core ⊆ s.2.active.erase p := fun z hz =>
      Finset.mem_erase.mpr ⟨fun h => hpc (h ▸ hz), hsub hz⟩
    dsimp only
    split_ifs
    all_goals first
      | (refine { g0 := hS.g0, ridge := (chooseRidge_nonneg _ _ _ hS.ridge), snap := ?_ }
         intro h; simp at h; done)
      | (refine { g0 := hS.g0, ridge := (chooseRidge_nonneg _ _ _ hS.ridge), snap := ?_ }
         intro _ h; simp [hcp] at h; done)
      | (refine { g0 := hS.g0, ridge := (chooseRidge_nonneg _ _ _ hS.ridge), snap := fun _ _ => ?_ }
         refine ⟨_, ⟨?_, ?_, ?_, hpa, by assumption⟩, rfl, (Finset.erase_subset _ _).trans hI.sub,
           CoreElim.refl⟩
         · rw [← hS.g0]
           first
             | assumption
             | exact not_not.mp (by assumption)
         · intro i k hi hk; exact elimStep_inv _ _ s.2 p _ i k hi hk
         · intro i k; exact elimStep_symm s.2 p _ (stageScale u j m) s.1.r hI.symm i k)

/-- **The snapshot invariant along every reachable state.** -/
theorem snapInv_reach (x : RunRecord d m)
    (hD : IsDampedEndpoint x.endpoint x.r (stageScale u j m))
    (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    SnapInv j u x s.2 := by
  induction h with
  | enter => exact snapInv_enter j u y x
  | step s a hs _ ih =>
    exact snapInv_update n₀ j u x s a (clr_reach n₀ j u y x s hs).1
      (clrInv_reach n₀ j u y x hD s hs) ih

end Reach

end AndersonAC.AgentS78.DoneA
