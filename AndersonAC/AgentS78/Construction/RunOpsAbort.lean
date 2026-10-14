import AndersonAC.AgentS78.Construction.RunOpsMark

/-!
# WP10 construction: abort discipline of the schedule

The `habort` hypothesis of `blockRun_of_disciplines` for `scheduleBlocks (runOp …)`: a block
exits aborted from a non-aborted record only if it is a tile block after the cutoff whose
first trial failed (a late slot), or the cutoff operation `cutoffIndex` entered with a
pending site. From `TileAbortStatement` and a clearing block that never aborts.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

/-- The cutoff operation: the stage operation of stage `⌊m/2⌋`. -/
def cutoffIndex (d m : ℕ) : ℕ := opIndex d m (m / 2) 3 (site₀ d m)

theorem opIndex_mem_lateSlots (j : ℕ) (y : Torus d m) (h1 : m / 2 < j) (h2 : j ≤ m + 1) :
    opIndex d m j 0 y ∈ lateSlots d m := by
  classical
  unfold lateSlots
  refine Finset.mem_image.mpr ⟨(j, y), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_univ, and_true]
    exact ⟨h1, h2⟩
  · rfl

/-- **Abort discipline of the schedule** (`habort` of `blockRun_of_disciplines`). -/
theorem runOps_abort (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (htile : TileAbortStatement)
    (hclr : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ((clr j y).exit s).aborted = true → x.aborted = true) :
    ∀ n x s, BlockReach (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x s →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted s = true →
      ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit s).aborted = true →
      x.aborted = true ∨
        ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).firstFail s = true ∧ n ∈ lateSlots d m) ∨
        (n = cutoffIndex d m ∧ x.pending.Nonempty) := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  have hk := decodeK_lt (d := d) (m := m) n
  generalize decodeJ d m n = j
  generalize decodeK d m n = k at hk
  generalize decodeY d m n = y
  rw [scheduleBlocks_opIndex _ j k y hk]
  have hsimple : ∀ f : RunRecord d m → RunRecord d m, (∀ x, (f x).aborted = x.aborted) →
      ∀ x s, BlockReach (simpleBlock (ts₀, cl₀) (guardMap f)) x s →
        ((simpleBlock (ts₀, cl₀) (guardMap f)).exit s).aborted = true → x.aborted = true := by
    intro f hf x s hs ha
    rw [simpleBlock_reach (ts₀, cl₀) _ x s hs] at ha
    simp only [simpleBlock, AgentS78.guardMap] at ha
    split_ifs at ha with h
    · exact ha
    · rw [hf x] at ha; exact ha
  have hid : ∀ x s, BlockReach (simpleBlock (ts₀, cl₀) (id : RunRecord d m → RunRecord d m)) x s →
      ((simpleBlock (ts₀, cl₀) (id : RunRecord d m → RunRecord d m)).exit s).aborted = true →
      x.aborted = true := by
    intro x s hs ha
    rw [simpleBlock_reach (ts₀, cl₀) _ x s hs] at ha
    exact ha
  unfold runOp
  split_ifs with hj hk0 hk1 hy hk2 hjm hjy
  · subst hk0
    cases hT : tileAt P j y with
    | none => exact fun x s hs _ ha => Or.inl (hid x s hs ha)
    | some T =>
      intro x s' hs' hh ha
      obtain ⟨s, hs, rfl⟩ := blockReach_embed (tileBlock P j T) (tileEmbed cl₀) tileProj
        (fun _ => rfl) x s' hs'
      rcases htile d m P j T x s hs hh ha with h | ⟨hf, hlate⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hf, opIndex_mem_lateSlots j y hlate hj.2⟩)
  · intro x s hs _ ha
    refine Or.inl (hsimple _ (fun x => ?_) x s hs ha)
    unfold endMap
    simp only [Function.comp]
    split_ifs <;> rfl
  · exact fun x s hs _ ha => Or.inl (hid x s hs ha)
  · subst hk2
    intro x s' hs' hh ha
    obtain ⟨s, hs, rfl⟩ := blockReach_embed (clr j y) (clearEmbed ts₀) clearProj
      (fun _ => rfl) x s' hs'
    exact Or.inl (hclr j y x s hs hh ha)
  · exact fun x s hs _ ha => Or.inl (hid x s hs ha)
  · intro x s hs _ ha
    rw [simpleBlock_reach (ts₀, cl₀) _ x s hs] at ha
    simp only [simpleBlock, AgentS78.guardMap] at ha
    split_ifs at ha with hab
    · exact Or.inl ha
    · unfold stageMap at ha
      simp only [Function.comp] at ha
      by_cases hcut : j = m / 2
      · rw [if_pos hcut] at ha
        simp only [sweepStartMap, resetMapA, cutoffMap, Bool.or_eq_true, bne_iff_ne, ne_eq] at ha
        rcases ha with h | h
        · exact Or.inl h
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · rw [hcut, hjy.2, show k = 3 by omega]; rfl
          · exact Finset.card_pos.mp (Nat.pos_of_ne_zero h)
      · rw [if_neg hcut] at ha
        exact Or.inl ha
  · exact fun x s hs _ ha => Or.inl (hid x s hs ha)
  · exact fun x s hs _ ha => Or.inl (hid x s hs ha)

end AndersonAC.AgentS78
