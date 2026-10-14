import AndersonAC.AgentS78.Construction.RunOpsCut

/-!
# no abort before the cutoff

The run aborts only at a late slot (tile slots of the stages after `⌊m/2⌋`) or at the cutoff
operation (`runOps_abort`). All of them come at or after the cutoff index, so every record
entering a block up to the cutoff is not aborted (`not_aborted_before_cutoff`). Used for the
clearing stages (`j ≤ ⌊m/2⌋`), whose operations precede the cutoff.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

theorem cutoffIndex_le_late (n : ℕ) (hn : n ∈ lateSlots d m) : cutoffIndex d m < n := by
  classical
  unfold lateSlots at hn
  obtain ⟨⟨j, y⟩, hp, rfl⟩ := Finset.mem_image.mp hn
  simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_univ, and_true] at hp
  have hS := siteCount_pos d m
  have hr : (siteRank d m (site₀ d m)).val = 0 := by
    unfold site₀; rw [Equiv.apply_symm_apply]
  show (4 * (m / 2) + 3) * siteCount d m + (siteRank d m (site₀ d m)).val <
    (4 * j + kindIndex BirthType.tile) * siteCount d m + (siteRank d m y).val
  rw [hr]
  simp only [kindIndex]
  have : 4 * (m / 2) + 3 < 4 * j := by omega
  nlinarith

/-- **No record is aborted up to the cutoff.** -/
theorem not_aborted_before_cutoff (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (M : ℕ → ℕ) (rec₀ : RunRecord d m) (hrec₀ : rec₀.aborted = false)
    (orderSet auxSet : ℕ → Set ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M (scheduleBlocks (runOp P ts₀ cl₀ clr)) orderSet)
    (haux : BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) auxSet)
    (htabort : TileAbortStatement)
    (hcabort : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).aborted = true → x.aborted = true)
    (ω : RandomSources (Torus d m) M) (b : ℕ) (hb : b ≤ cutoffIndex d m)
    (hreach : blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ b ω ≠ ⊤) :
    (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ b ω).aborted = false := by
  by_contra hne
  have hab : (blockPrestate M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ b ω).aborted = true := by
    simpa using hne
  rcases abort_along_run M _ rec₀ orderSet auxSet hdisj horders haux (fun x => x.aborted = true)
      (fun n => n ∈ lateSlots d m) (fun n x => n = cutoffIndex d m ∧ x.pending.Nonempty)
      (runOps_abort P ts₀ cl₀ clr htabort hcabort) 0 ω b (Nat.zero_le b) hreach hab with
    h | ⟨n, -, hnb, -, hc⟩
  · have hstart0 : blockStart M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ 0 ω ≠ ⊤ :=
      reached_of_le M _ rec₀ orderSet auxSet hdisj horders haux ω b hreach 0 (Nat.zero_le b)
    have hpre0 := blockPrestate_mem M (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
      (fun n => {x | n = 0 → x = rec₀}) (fun _ => rfl)
      (fun n x _ s _ _ h => absurd h (Nat.succ_ne_zero n)) 0 ω hstart0 rfl

    rw [hpre0, hrec₀] at h
    exact Bool.false_ne_true h
  · rcases hc with ⟨_, hl⟩ | ⟨rfl, _⟩
    · have := cutoffIndex_le_late (d := d) (m := m) n hl; omega
    · omega

end AndersonAC.AgentS78
