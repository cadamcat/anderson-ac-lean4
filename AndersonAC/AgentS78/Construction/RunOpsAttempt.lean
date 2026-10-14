import AndersonAC.AgentS78.Construction.RunOpsDich
import AndersonAC.AgentS78.Construction.SnapshotComponents

/-!
# WP10 construction: attempt and locality facts of a clearing stage

The hypotheses `hatt`, `hloc` of `runOps_dich`, from three properties of the clearing block
`clr j z` (to be proved for muse-s78clear's block):
* `hcomp`: it keeps the snapshot components;
* `hrelabel`: from a non-aborted record, every site of the eligible component anchored at `z`
  that is pending at exit carries the label `⟨j, clearing, z⟩` (FAIL marks the core; DONE
  makes it terminal);
* `hkeep`: a pending site outside the eligible component anchored at `z` stays pending with
  its label (inspected exterior sites are coupled, 07-assembly.tex:18–34).
The schedule's other blocks between the snapshot and the next stage keep pending sites,
labels and components; no record before the cutoff is aborted (`not_aborted_before_cutoff`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

theorem site₀_rank : (siteRank d m (site₀ d m)).val = 0 := by
  unfold site₀; rw [Equiv.apply_symm_apply]

/-- Decoding the blocks strictly between the snapshot and the next stage. -/
theorem decode_stage_tail (j n : ℕ) (h1 : afterSnapshotIdx d m j ≤ n)
    (h2 : n < stageStartIdx d m (j + 1)) :
    decodeJ d m n = j ∧ 1 ≤ decodeK d m n ∧ (decodeK d m n = 1 → decodeY d m n ≠ site₀ d m) := by
  have hS := siteCount_pos d m
  have hr := site₀_rank (d := d) (m := m)
  unfold afterSnapshotIdx opIndex at h1
  rw [hr] at h1
  unfold stageStartIdx at h2
  have hq1 : 4 * j + 1 ≤ n / siteCount d m := by
    rw [Nat.le_div_iff_mul_le hS]; omega
  have hq2 : n / siteCount d m < 4 * j + 4 := by
    rw [Nat.div_lt_iff_lt_mul hS]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold decodeJ
    rw [Nat.mul_comm 4, ← Nat.div_div_eq_div_mul]; omega
  · unfold decodeK; omega
  · intro hk heq
    unfold decodeK at hk
    have hq : n / siteCount d m = 4 * j + 1 := by omega
    have hmod : n % siteCount d m = 0 := by
      have := congrArg (fun y => (siteRank d m y).val) heq
      simp only [decodeY, Equiv.apply_symm_apply, hr] at this
      exact this
    have := Nat.div_add_mod n (siteCount d m)
    rw [hq, hmod] at this
    nlinarith

theorem stageMap_components (P : TilePlan d m) (j : ℕ) (x : RunRecord d m) :
    (guardMap (stageMap P j) x).components = x.components := by
  unfold guardMap stageMap
  split_ifs <;> rfl

/-- The blocks strictly between the snapshot and the next stage of a clearing stage. -/
theorem tail_block (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (j n : ℕ) (hj : P.n₀ < j) (hjm : j ≤ m / 2) (h1 : afterSnapshotIdx d m j ≤ n)
    (h2 : n < stageStartIdx d m (j + 1)) :
    (decodeK d m n = 2 ∧ scheduleBlocks (runOp P ts₀ cl₀ clr) n =
        (clr j (decodeY d m n)).embed (clearEmbed ts₀) clearProj) ∨
    ∃ f : RunRecord d m → RunRecord d m,
      scheduleBlocks (runOp P ts₀ cl₀ clr) n = simpleBlock (ts₀, cl₀) f ∧ KeepsMarks f ∧
        ∀ x, (f x).components = x.components := by
  obtain ⟨hJ, hK1, hY⟩ := decode_stage_tail j n h1 h2
  have hk4 := decodeK_lt (d := d) (m := m) n
  unfold scheduleBlocks runOp
  rw [hJ, if_pos ⟨hj, by omega⟩, if_neg (by omega)]
  by_cases hk1 : decodeK d m n = 1
  · rw [if_pos hk1, if_neg (hY hk1)]
    exact Or.inr ⟨id, rfl, keepsMarks_id, fun _ => rfl⟩
  · rw [if_neg hk1]
    by_cases hk2 : decodeK d m n = 2
    · rw [if_pos hk2, if_pos hjm]
      exact Or.inl ⟨hk2, rfl⟩
    · rw [if_neg hk2]
      split_ifs
      · exact Or.inr ⟨_, rfl, (keepsMarks_stageMap P j).guardMap, stageMap_components P j⟩
      · exact Or.inr ⟨id, rfl, keepsMarks_id, fun _ => rfl⟩

section Run
variable (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
  (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
  (M : ℕ → ℕ) (rec₀ : RunRecord d m) (orderSet auxSet : ℕ → Set ℕ)

/-- The record after the snapshot of a clearing stage lists the snapshot components. -/
theorem snapshot_components
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M (scheduleBlocks (runOp P ts₀ cl₀ clr)) orderSet)
    (haux : BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) auxSet)
    (ω : RandomSources (Torus d m) M) (j : ℕ) (hj : P.n₀ < j) (hjm : j ≤ m / 2)
    (hreach : blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j) ω ≠ ⊤)
    (hab : (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
      (opIndex d m j 1 (site₀ d m)) ω).aborted = false) :
    (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j) ω).components =
      snapshotComponents (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (afterSnapshotIdx d m j) ω).pending (separationRadius j) := by
  obtain ⟨s, hs, _, hx⟩ := run_chain M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ orderSet auxSet
    hdisj horders haux ω _ hreach (opIndex d m j 1 (site₀ d m)) (Nat.lt_succ_self _)
  rw [scheduleBlocks_opIndex _ j 1 (site₀ d m) (by norm_num)] at hs hx
  have hblock : runOp P ts₀ cl₀ clr j 1 (site₀ d m) =
      simpleBlock (ts₀, cl₀) (guardMap (endMap P j)) := by
    unfold runOp
    rw [if_pos ⟨hj, by omega⟩, if_neg (by norm_num), if_pos rfl, if_pos rfl]
  rw [hblock] at hs hx
  rw [simpleBlock_reach (ts₀, cl₀) _ _ s hs] at hx
  unfold afterSnapshotIdx
  rw [hx]
  simp only [simpleBlock, guardMap, hab, Bool.false_eq_true, if_false, endMap, Function.comp,
    if_pos hjm]
  rfl

/-- The components stay those of the snapshot until the next stage. -/
theorem tail_components
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M (scheduleBlocks (runOp P ts₀ cl₀ clr)) orderSet)
    (haux : BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) auxSet)
    (hcomp : ∀ j y x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).components = x.components)
    (ω : RandomSources (Torus d m) M) (j : ℕ) (hj : P.n₀ < j) (hjm : j ≤ m / 2)
    (hreach : blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤) :
    ∀ i, afterSnapshotIdx d m j + i ≤ stageStartIdx d m (j + 1) →
      (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j + i) ω).components =
      (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j) ω).components := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hlt : afterSnapshotIdx d m j + i < stageStartIdx d m (j + 1) := by omega
    obtain ⟨s, hs, hh, hx⟩ := run_chain M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ orderSet
      auxSet hdisj horders haux ω _ hreach _ hlt
    rw [← Nat.add_assoc, hx, ← ih hlt.le]
    rcases tail_block P ts₀ cl₀ clr j _ hj hjm (Nat.le_add_right _ _) hlt with ⟨_, hB⟩ | ⟨f, hB, _, hf⟩
    · rw [hB] at hs hh ⊢
      obtain ⟨s0, hs0, rfl⟩ := blockReach_embed (clr j _) (clearEmbed ts₀) clearProj
        (fun _ => rfl) _ s hs
      exact hcomp j _ _ s0 hs0 hh
    · rw [hB] at hs ⊢
      rw [simpleBlock_reach (ts₀, cl₀) f _ s hs]
      exact hf _

end Run

section Main
variable (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
  (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
  (M : ℕ → ℕ) (rec₀ : RunRecord d m) (orderSet auxSet : ℕ → Set ℕ)

open Classical in
/-- **Locality** (`hloc` of `runOps_dich`). -/
theorem runOps_loc
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M (scheduleBlocks (runOp P ts₀ cl₀ clr)) orderSet)
    (haux : BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) auxSet)
    (hrec₀ : rec₀.aborted = false) (htabort : TileAbortStatement)
    (hcabort : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).aborted = true → x.aborted = true)
    (hcomp : ∀ j y x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).components = x.components)
    (hkeep : ∀ j (z : Torus d m) x s, BlockReach (clr j z) x s → (clr j z).halted s = true →
      ∀ w ∈ x.pending, (∀ Bc ∈ x.components, w ∈ Bc → z ∈ Bc →
        (∀ v ∈ Bc, (siteRank d m z).val ≤ (siteRank d m v).val) →
        ¬ ((Bc.card : ℝ) ≤ stageScale P.u j m ^ (-nu d))) →
      w ∈ ((clr j z).exit s).pending ∧ ((clr j z).exit s).latest w = x.latest w) :
    ∀ j (ω : RandomSources (Torus d m) M), P.n₀ < j → clearingScheduled j m →
      blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤ →
      ∀ y (hy : y ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
          (afterSnapshotIdx d m j) ω).pending),
        ⌊stageScale P.u j m ^ (-nu d)⌋₊ < (Finset.univ.filter ((snapshotGraph d m (blockPrestate M
          (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j) ω).pending
          (separationRadius j)).Reachable ⟨y, hy⟩)).card →
        ∀ n, afterSnapshotIdx d m j ≤ n → n < stageStartIdx d m (j + 1) → ∀ x',
          BlockStep (scheduleBlocks (runOp P ts₀ cl₀ clr)) n
            (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω) x' →
          y ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω).pending →
          y ∈ x'.pending ∧ x'.latest y =
            (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω).latest y := by
  intro j ω hj hsch hreach y hy hbig n h1 h2 x' hst hyn
  have hjm : j ≤ m / 2 := hsch
  obtain ⟨s, hs, hh, rfl⟩ := hst
  rcases tail_block P ts₀ cl₀ clr j n hj hjm h1 h2 with ⟨_, hB⟩ | ⟨f, hB, hf, _⟩
  · rw [hB] at hs hh ⊢
    obtain ⟨s0, hs0, rfl⟩ := blockReach_embed (clr j _) (clearEmbed ts₀) clearProj
      (fun _ => rfl) _ s hs
    refine hkeep j _ _ s0 hs0 hh y hyn ?_
    intro Bc hBc hyBc _ _ hel
    -- the components of the record are the snapshot components
    have hreach_a := reached_of_le M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ orderSet auxSet hdisj horders haux ω _ hreach _
      (afterSnapshotIdx_le j)
    have hcutle : opIndex d m j 1 (site₀ d m) ≤ cutoffIndex d m := by
      have hS := siteCount_pos d m
      unfold cutoffIndex opIndex; nlinarith
    have hab := not_aborted_before_cutoff P ts₀ cl₀ clr M rec₀ hrec₀ orderSet auxSet hdisj
      horders haux htabort hcabort ω _ hcutle (reached_of_le M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ orderSet auxSet hdisj
        horders haux ω _ hreach_a _ (Nat.le_succ _))
    have hcs := snapshot_components P ts₀ cl₀ clr M rec₀ orderSet auxSet hdisj horders haux ω j
      hj hjm hreach_a hab
    have htc := tail_components P ts₀ cl₀ clr M rec₀ orderSet auxSet hdisj horders haux hcomp ω
      j hj hjm hreach (n - afterSnapshotIdx d m j) (by omega)
    rw [Nat.add_sub_cancel' h1] at htc
    rw [htc, hcs] at hBc
    obtain ⟨hy', rfl⟩ := eq_snapComp_of_mem _ _ Bc hBc y hyBc
    rw [snapComp_card] at hel
    have hle : (Finset.univ.filter ((snapshotGraph d m (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (afterSnapshotIdx d m j) ω).pending (separationRadius j)).Reachable ⟨y, hy'⟩)).card ≤
        ⌊stageScale P.u j m ^ (-nu d)⌋₊ := Nat.le_floor hel
    exact absurd hle (not_le.mpr hbig)
  · rw [hB] at hs ⊢
    rw [simpleBlock_reach (ts₀, cl₀) f _ s hs]
    show y ∈ (f _).pending ∧ (f _).latest y = _
    rw [(hf _).1, (hf _).2]
    exact ⟨hyn, rfl⟩

open Classical in
/-- **Attempt** (`hatt` of `runOps_dich`). -/
theorem runOps_att (hu : P.u ∈ Set.Ioc (0 : ℝ) 1)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M (scheduleBlocks (runOp P ts₀ cl₀ clr)) orderSet)
    (haux : BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) auxSet)
    (hrec₀ : rec₀.aborted = false) (htabort : TileAbortStatement)
    (hcabort : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).aborted = true → x.aborted = true)
    (hcomp : ∀ j y x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).components = x.components)
    (hrelabel : ∀ j (z : Torus d m) x s, BlockReach (clr j z) x s → (clr j z).halted s = true →
      x.aborted = false → clearingScheduled j m →
        (∃ R : Finset (Torus d m), x.components = snapshotComponents R (separationRadius j)) →
        ∀ Bc ∈ x.components, z ∈ Bc →
        (∀ v ∈ Bc, (siteRank d m z).val ≤ (siteRank d m v).val) →
        (Bc.card : ℝ) ≤ stageScale P.u j m ^ (-nu d) →
        ∀ w ∈ Bc, w ∈ ((clr j z).exit s).pending →
          ((clr j z).exit s).latest w = ⟨j, BirthType.clearing, z⟩) :
    ∀ j (ω : RandomSources (Torus d m) M), P.n₀ < j → clearingScheduled j m →
      blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (stageStartIdx d m (j + 1)) ω ≠ ⊤ →
      ∀ y (hy : y ∈ (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
          (afterSnapshotIdx d m j) ω).pending),
        (Finset.univ.filter ((snapshotGraph d m (blockPrestate M
          (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (afterSnapshotIdx d m j) ω).pending
          (separationRadius j)).Reachable ⟨y, hy⟩)).card ≤ ⌊stageScale P.u j m ^ (-nu d)⌋₊ →
        ∃ n, afterSnapshotIdx d m j ≤ n ∧ n < stageStartIdx d m (j + 1) ∧ ∀ x',
          BlockStep (scheduleBlocks (runOp P ts₀ cl₀ clr)) n
            (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω) x' →
          y ∈ x'.pending → x'.latest y = opLabel d m n := by
  intro j ω hj hsch hreach y hy hsmall
  have hjm : j ≤ m / 2 := hsch
  set R := (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
    (afterSnapshotIdx d m j) ω).pending with hR
  obtain ⟨z, hzB, hzmin⟩ := (snapComp R (separationRadius j) y hy).exists_min_image
    (fun w => (siteRank d m w).val) ⟨y, self_mem_snapComp _ _ y hy⟩
  have hS := siteCount_pos d m
  have hr0 := site₀_rank (d := d) (m := m)
  have hzlt := (siteRank d m z).isLt
  have h1 : afterSnapshotIdx d m j ≤ opIndex d m j 2 z := by
    unfold afterSnapshotIdx opIndex; rw [hr0]; nlinarith
  have h2 : opIndex d m j 2 z < stageStartIdx d m (j + 1) := by
    unfold opIndex stageStartIdx; nlinarith
  refine ⟨opIndex d m j 2 z, h1, h2, ?_⟩
  rintro x' ⟨s, hs, hh, rfl⟩ hyx
  have hB : scheduleBlocks (runOp P ts₀ cl₀ clr) (opIndex d m j 2 z) =
      (clr j z).embed (clearEmbed ts₀) clearProj := by
    rw [scheduleBlocks_opIndex _ j 2 z (by norm_num)]
    unfold runOp
    rw [if_pos ⟨hj, by omega⟩, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl,
      if_pos hjm]
  rw [hB] at hs hh hyx ⊢
  obtain ⟨s0, hs0, rfl⟩ := blockReach_embed (clr j z) (clearEmbed ts₀) clearProj
    (fun _ => rfl) _ s hs
  have hreach_a := reached_of_le M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ orderSet auxSet
    hdisj horders haux ω _ hreach _ (afterSnapshotIdx_le j)
  have hreach_n := reached_of_le M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ orderSet auxSet
    hdisj horders haux ω _ hreach _ h2.le
  have hcut1 : opIndex d m j 1 (site₀ d m) ≤ cutoffIndex d m := by
    unfold cutoffIndex opIndex; nlinarith
  have hcutn : opIndex d m j 2 z ≤ cutoffIndex d m := by
    unfold cutoffIndex opIndex; rw [hr0]; nlinarith
  have hab1 := not_aborted_before_cutoff P ts₀ cl₀ clr M rec₀ hrec₀ orderSet auxSet hdisj
    horders haux htabort hcabort ω _ hcut1 (reached_of_le M (scheduleBlocks (runOp P ts₀ cl₀ clr))
      rec₀ orderSet auxSet hdisj horders haux ω _ hreach_a _ (Nat.le_succ _))
  have habn := not_aborted_before_cutoff P ts₀ cl₀ clr M rec₀ hrec₀ orderSet auxSet hdisj
    horders haux htabort hcabort ω _ hcutn hreach_n
  have hcs := snapshot_components P ts₀ cl₀ clr M rec₀ orderSet auxSet hdisj horders haux ω j
    hj hjm hreach_a hab1
  have htc := tail_components P ts₀ cl₀ clr M rec₀ orderSet auxSet hdisj horders haux hcomp ω
    j hj hjm hreach (opIndex d m j 2 z - afterSnapshotIdx d m j) (by omega)
  rw [Nat.add_sub_cancel' h1] at htc
  have hmem : snapComp R (separationRadius j) y hy ∈
      (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (opIndex d m j 2 z) ω).components := by
    rw [htc, hcs]; exact snapComp_mem _ _ y hy
  have hel : ((snapComp R (separationRadius j) y hy).card : ℝ) ≤
      stageScale P.u j m ^ (-nu d) := by
    rw [snapComp_card]
    have hpos : 0 ≤ stageScale P.u j m ^ (-nu d) := by
      apply Real.rpow_nonneg
      unfold stageScale
      have := hu.1
      positivity
    exact le_trans (Nat.cast_le.mpr hsmall) (Nat.floor_le hpos)
  have := hrelabel j z _ s0 hs0 hh habn hsch ⟨_, htc.trans hcs⟩ _ hmem hzB hzmin hel y
    (self_mem_snapComp _ _ y hy) hyx
  show ((clr j z).exit s0).latest y = opLabel d m (opIndex d m j 2 z)
  rw [this, opLabel_clearing]

end Main

end AndersonAC.AgentS78
