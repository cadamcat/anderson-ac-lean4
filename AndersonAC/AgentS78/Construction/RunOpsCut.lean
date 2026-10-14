import AndersonAC.AgentS78.Construction.RunOpsFresh
import AndersonAC.AgentS78.Construction.RunChain

/-!
# WP10 construction: from the cutoff to the end of stage `⌊m/2⌋`

The blocks from the cutoff operation `cutoffIndex` to the first block of stage `⌊m/2⌋ + 1`
are stage operations (`k = 3`), which keep the pending sites. Hence the pending set entering
the cutoff is still pending at the start of stage `⌊m/2⌋ + 1` (`hcutkeep` of
`blockRun_of_disciplines`, `runOps_cutkeep`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

/-- Stage operations keep the pending sites. -/
theorem runOp_kind3_pending (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (j : ℕ) (y : Torus d m) :
    ∀ x s, BlockReach (runOp P ts₀ cl₀ clr j 3 y) x s →
      ((runOp P ts₀ cl₀ clr j 3 y).exit s).pending = x.pending := by
  have hs : ∀ f : RunRecord d m → RunRecord d m, KeepsMarks f → ∀ x s,
      BlockReach (simpleBlock (ts₀, cl₀) f) x s →
      ((simpleBlock (ts₀, cl₀) f).exit s).pending = x.pending := by
    intro f hf x s h
    rw [simpleBlock_reach (ts₀, cl₀) f x s h]
    exact (hf x).1
  unfold runOp
  rw [if_neg (show ¬((3 : ℕ) = 0) by decide), if_neg (show ¬((3 : ℕ) = 1) by decide),
    if_neg (show ¬((3 : ℕ) = 2) by decide)]
  split_ifs
  · exact hs _ (keepsMarks_stageMap P j).guardMap
  · exact hs id keepsMarks_id
  · exact hs id keepsMarks_id

theorem decodeK_eq_three (n J : ℕ) (h1 : opIndex d m J 3 (site₀ d m) ≤ n)
    (h2 : n < stageStartIdx d m (J + 1)) : decodeK d m n = 3 := by
  have hS := siteCount_pos d m
  have hr : (siteRank d m (site₀ d m)).val = 0 := by
    unfold site₀; rw [Equiv.apply_symm_apply]
  unfold opIndex at h1
  rw [hr] at h1
  unfold stageStartIdx at h2
  unfold decodeK
  have : n / siteCount d m = 4 * J + 3 := by
    apply Nat.div_eq_of_lt_le
    · linarith
    · calc n < 4 * (J + 1) * siteCount d m := h2
        _ = (4 * J + 3 + 1) * siteCount d m := by ring
  rw [this]; omega

/-- **Pending sites survive from the cutoff to the end of stage `⌊m/2⌋`.** -/
theorem runOps_cutkeep (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (M : ℕ → ℕ) (rec₀ : RunRecord d m) (orderSet auxSet : ℕ → Set ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M (scheduleBlocks (runOp P ts₀ cl₀ clr)) orderSet)
    (haux : BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) auxSet)
    (ω : RandomSources (Torus d m) M)
    (he : blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
      (stageStartIdx d m (m / 2 + 1)) ω ≠ ⊤) :
    blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (cutoffIndex d m) ω ≠ ⊤ →
    (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (cutoffIndex d m) ω).pending ⊆
      (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
        (stageStartIdx d m (m / 2 + 1)) ω).pending := by
  intro _
  set B := scheduleBlocks (runOp P ts₀ cl₀ clr)
  set e := stageStartIdx d m (m / 2 + 1)
  have hle : cutoffIndex d m ≤ e := by
    have hS := siteCount_pos d m
    have hr : (siteRank d m (site₀ d m)).val = 0 := by
      unfold site₀; rw [Equiv.apply_symm_apply]
    unfold cutoffIndex opIndex e stageStartIdx
    rw [hr]; nlinarith
  have hchain := run_chain M B rec₀ orderSet auxSet hdisj horders haux ω e he
  have key : ∀ i, cutoffIndex d m + i ≤ e →
      (blockPrestate M B rec₀ (cutoffIndex d m + i) ω).pending =
        (blockPrestate M B rec₀ (cutoffIndex d m) ω).pending := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hlt : cutoffIndex d m + i < e := by omega
      obtain ⟨s, hs, _, hx⟩ := hchain _ hlt
      rw [← Nat.add_assoc, hx, ← ih hlt.le]
      have h3 := decodeK_eq_three (d := d) (m := m) (cutoffIndex d m + i) (m / 2)
        (by unfold cutoffIndex; omega) hlt
      have hB : B (cutoffIndex d m + i) = runOp P ts₀ cl₀ clr
          (decodeJ d m (cutoffIndex d m + i)) 3 (decodeY d m (cutoffIndex d m + i)) := by
        show scheduleBlocks _ _ = _
        unfold scheduleBlocks; rw [h3]
      rw [hB] at hs ⊢
      exact runOp_kind3_pending P ts₀ cl₀ clr _ _ _ _ hs
  have := key (e - cutoffIndex d m) (by omega)
  rw [Nat.add_sub_cancel' hle] at this
  rw [this]

end AndersonAC.AgentS78
