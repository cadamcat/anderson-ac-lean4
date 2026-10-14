import AndersonAC.AgentS78.Construction.RunOpsDisc
import AndersonAC.AgentS78.Construction.TransitionDisciplines
import AndersonAC.AgentS78.Construction.TileDisciplines
import AndersonAC.AgentS78.Construction.Assembly

/-!
# marking discipline of the schedule

The `hmark` hypothesis of `blockRun_of_disciplines` for `scheduleBlocks (runOp …)`, from the
tile marking discipline (`TileMarkingStatement`), the tile diameter of the plan,
and the clearing marking discipline. The
query-free operations keep pending sites and labels (`KeepsMarks`). Also: the blocks before
stage `n₀ + 1` are empty (`hempty`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

theorem KeepsMarks.guardMap {f : RunRecord d m → RunRecord d m} (hf : KeepsMarks f) :
    KeepsMarks (guardMap f) := by
  intro x
  unfold AgentS78.guardMap
  split_ifs
  · exact ⟨rfl, rfl⟩
  · exact hf x

theorem keepsMarks_endMap (P : TilePlan d m) (j : ℕ) : KeepsMarks (endMap P j) := by
  unfold endMap
  refine KeepsMarks.comp ?_ (keepsMarks_sweepEndMapTheta _)
  split_ifs
  · exact keepsMarks_snapshotMap j
  · exact keepsMarks_id

theorem keepsMarks_resetMapA (t : ℝ) : KeepsMarks (resetMapA (d := d) (m := m) t) :=
  fun _ => ⟨rfl, rfl⟩

theorem keepsMarks_stageMap (P : TilePlan d m) (j : ℕ) : KeepsMarks (stageMap P j) := by
  unfold stageMap
  refine KeepsMarks.comp (keepsMarks_sweepStartMap _ _) (KeepsMarks.comp ?_ (keepsMarks_resetMapA _))
  split_ifs
  · exact keepsMarks_cutoffMap
  · exact keepsMarks_id

/-- The blocks before stage `n₀ + 1` are empty. -/
theorem runOps_empty (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc)) :
    ∀ n < stageStartIdx d m (P.n₀ + 1),
      scheduleBlocks (runOp P ts₀ cl₀ clr) n = simpleBlock (ts₀, cl₀) id := by
  intro n hn
  have hj : decodeJ d m n ≤ P.n₀ := by
    unfold decodeJ
    unfold stageStartIdx at hn
    have hpos : 0 < 4 * siteCount d m := by have := siteCount_pos d m; omega
    have : n / (4 * siteCount d m) < P.n₀ + 1 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      calc n < 4 * (P.n₀ + 1) * siteCount d m := hn
        _ = (P.n₀ + 1) * (4 * siteCount d m) := by ring
    omega
  unfold scheduleBlocks runOp
  rw [if_neg (fun h => by omega)]

/-- The schedule label of a tile operation. -/
theorem opLabel_tile (j : ℕ) (y : Torus d m) :
    opLabel d m (opIndex d m j 0 y) = ⟨j, BirthType.tile, y⟩ := by
  rw [opLabel_opIndex d m j 0 y (by norm_num)]
  simp

/-- The schedule label of a clearing operation. -/
theorem opLabel_clearing (j : ℕ) (y : Torus d m) :
    opLabel d m (opIndex d m j 2 y) = ⟨j, BirthType.clearing, y⟩ := by
  rw [opLabel_opIndex d m j 2 y (by norm_num)]
  simp

/-- **Marking discipline of the schedule** (`hmark` of `blockRun_of_disciplines`). -/
theorem runOps_mark (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc)) (Ch : ℝ)
    (htile : TileMarkingStatement)
    (hdiam : ∀ j (T : Fin (P.cover j).cover.count), ∀ y ∈ tileSites (P.cover j) T,
      physicalDistance d m y (tileAnchor (P.cover j) T) ≤
        Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
    (hclr : ∀ j (y : Torus d m) x s, BlockReach (clr j y) x s → (clr j y).halted s = true →
      ∀ z ∈ ((clr j y).exit s).pending,
        (z ∈ x.pending ∧ ((clr j y).exit s).latest z = x.latest z) ∨
        (((clr j y).exit s).latest z = ⟨j, BirthType.clearing, y⟩ ∧
          (clr j y).firstFail s = true ∧
          physicalDistance d m z y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))) :
    ∀ n x s, BlockReach (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x s →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted s = true →
      ∀ y ∈ ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit s).pending,
        (y ∈ x.pending ∧ ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit s).latest y =
          x.latest y) ∨
        (((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit s).latest y = opLabel d m n ∧
          (scheduleBlocks (runOp P ts₀ cl₀ clr) n).firstFail s = true ∧
          (physicalDistance d m y (opLabel d m n).anchor ≤
            Ch * (4 : ℝ) ^ ((8 + nu d) * ((opLabel d m n).scale : ℝ)) ∧
            slotIndex (opLabel d m n) = n)) := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  have hk := decodeK_lt (d := d) (m := m) n
  generalize decodeJ d m n = j
  generalize decodeK d m n = k at hk
  generalize decodeY d m n = y
  rw [scheduleBlocks_opIndex _ j k y hk]
  have hsimple : ∀ f : RunRecord d m → RunRecord d m, KeepsMarks f →
      ∀ x s, BlockReach (simpleBlock (ts₀, cl₀) f) x s →
        (simpleBlock (ts₀, cl₀) f).halted s = true →
        ∀ z ∈ ((simpleBlock (ts₀, cl₀) f).exit s).pending,
          (z ∈ x.pending ∧ ((simpleBlock (ts₀, cl₀) f).exit s).latest z = x.latest z) ∨
          (((simpleBlock (ts₀, cl₀) f).exit s).latest z = opLabel d m (opIndex d m j k y) ∧
            (simpleBlock (ts₀, cl₀) f).firstFail s = true ∧
            (physicalDistance d m z (opLabel d m (opIndex d m j k y)).anchor ≤
              Ch * (4 : ℝ) ^ ((8 + nu d) * ((opLabel d m (opIndex d m j k y)).scale : ℝ)) ∧
              slotIndex (opLabel d m (opIndex d m j k y)) = opIndex d m j k y)) :=
    fun f hf x s hs _ z hz => by
      rw [simpleBlock_reach (ts₀, cl₀) f x s hs] at hz ⊢
      left
      simp only [simpleBlock] at hz ⊢
      exact ⟨(hf x).1 ▸ hz, by rw [(hf x).2]⟩
  unfold runOp
  split_ifs with hj hk0 hk1 hy hk2 hjm hjy
  · subst hk0
    cases hT : tileAt P j y with
    | none => exact hsimple id keepsMarks_id
    | some T =>
      have hanchor := tileAt_anchor P j y T hT
      refine embed_reach_exit (tileBlock P j T) (tileEmbed cl₀) tileProj (fun _ => rfl)
        (fun x s x' => ∀ z ∈ x'.pending, (z ∈ x.pending ∧ x'.latest z = x.latest z) ∨
          (x'.latest z = opLabel d m (opIndex d m j 0 y) ∧ (tileBlock P j T).firstFail s = true ∧
            (physicalDistance d m z (opLabel d m (opIndex d m j 0 y)).anchor ≤
              Ch * (4 : ℝ) ^ ((8 + nu d) * ((opLabel d m (opIndex d m j 0 y)).scale : ℝ)) ∧
              slotIndex (opLabel d m (opIndex d m j 0 y)) = opIndex d m j 0 y))) ?_
      intro x s hs hh z hz
      rcases htile d m P j T x s hs hh z hz with h | ⟨hl, hf, hzT⟩
      · exact Or.inl h
      · refine Or.inr ⟨?_, hf, ?_, slotIndex_opLabel d m j y 0 (Or.inl rfl)⟩
        · rw [hl, opLabel_tile, hanchor]
        · rw [opLabel_tile]
          have := hdiam j T z hzT
          rw [hanchor] at this
          exact this
  · exact hsimple _ (keepsMarks_endMap P j).guardMap
  · exact hsimple id keepsMarks_id
  · subst hk2
    refine embed_reach_exit (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl)
      (fun x s x' => ∀ z ∈ x'.pending, (z ∈ x.pending ∧ x'.latest z = x.latest z) ∨
        (x'.latest z = opLabel d m (opIndex d m j 2 y) ∧ (clr j y).firstFail s = true ∧
          (physicalDistance d m z (opLabel d m (opIndex d m j 2 y)).anchor ≤
            Ch * (4 : ℝ) ^ ((8 + nu d) * ((opLabel d m (opIndex d m j 2 y)).scale : ℝ)) ∧
            slotIndex (opLabel d m (opIndex d m j 2 y)) = opIndex d m j 2 y))) ?_
    intro x s hs hh z hz
    rcases hclr j y x s hs hh z hz with h | ⟨hl, hf, hd⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, hf, ?_, slotIndex_opLabel d m j y 2 (Or.inr rfl)⟩
      · rw [hl, opLabel_clearing]
      · rw [opLabel_clearing]; exact hd
  · exact hsimple id keepsMarks_id
  · exact hsimple _ (keepsMarks_stageMap P j).guardMap
  · exact hsimple id keepsMarks_id
  · exact hsimple id keepsMarks_id

end AndersonAC.AgentS78
