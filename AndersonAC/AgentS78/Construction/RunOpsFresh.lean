import AndersonAC.AgentS78.Construction.RunOpsAbort

/-!
# read patterns and query discipline of the schedule

The read pattern of operation `(j, k, y)` (`runPattern`): the tile pattern of the tile block,
the clearing pattern (a parameter) of the clearing block, the empty pattern otherwise. Proved
for `scheduleBlocks (runOp …)`: pattern measurability, locality of the first-trial failure
(`hlocal`), the query discipline against `declaredFresh` (`hquery`) and the pattern
discipline (`hpat`) of `blockRun_of_disciplines`, from the tile statements
(`TileQueryStatement`, `TilePatternStatement`), `tileBlock_fail_local`, and the
corresponding clearing hypotheses.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources querySigns SignIndex)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

/-- The empty read pattern. -/
def emptyPattern (d m : ℕ) : FreshPattern (Torus d m) := ⟨∅, fun _ => 0, ∅, ∅⟩

theorem emptyPattern_signs : (emptyPattern d m).signs = ∅ := by
  ext z; simp [emptyPattern, FreshPattern.signs]

/-- The read pattern of operation `(j, k, y)`. -/
def runPattern (P : TilePlan d m)
    (clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m)) (j k : ℕ)
    (y : Torus d m) (x : RunRecord d m) : FreshPattern (Torus d m) :=
  if P.n₀ < j ∧ j ≤ m + 1 then
    if k = 0 then
      match tileAt P j y with
      | some T => tilePattern P j T x
      | none => emptyPattern d m
    else if k = 2 ∧ j ≤ m / 2 then clrPat j y x
    else emptyPattern d m
  else emptyPattern d m

/-- The schedule's pattern of block `n`. -/
def schedulePattern (P : TilePlan d m)
    (clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m)) (n : ℕ) :
    RunRecord d m → FreshPattern (Torus d m) :=
  runPattern P clrPat (decodeJ d m n) (decodeK d m n) (decodeY d m n)

theorem schedulePattern_opIndex (P : TilePlan d m)
    (clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m)) (j k : ℕ)
    (y : Torus d m) (hk : k < 4) :
    schedulePattern P clrPat (opIndex d m j k y) = runPattern P clrPat j k y := by
  obtain ⟨h1, h2, h3⟩ := decode_opIndex j k y hk
  unfold schedulePattern
  rw [h1, h2, h3]

theorem schedulePattern_measurable (P : TilePlan d m)
    (clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m))
    (hclrPat : ∀ j y, Measurable (clrPat j y)) (n : ℕ) :
    Measurable (schedulePattern P clrPat n) := by
  unfold schedulePattern runPattern
  split_ifs
  · cases tileAt P (decodeJ d m n) (decodeY d m n) with
    | some T => exact tilePattern_measurable P _ T
    | none => exact measurable_const
  · exact hclrPat _ _
  · exact measurable_const
  · exact measurable_const

theorem guardMap_fresh {f : RunRecord d m → RunRecord d m} (hf : ShrinksFresh f Set.univ)
    (x : RunRecord d m) : declaredFresh (guardMap f x) ⊆ declaredFresh x := by
  unfold guardMap
  split_ifs
  · exact le_rfl
  · exact hf x trivial

theorem shrinksFresh_endMap (P : TilePlan d m) (j : ℕ) : ShrinksFresh (endMap P j) Set.univ := by
  unfold endMap
  refine ShrinksFresh.comp (J := Set.univ) ?_ (shrinksFresh_sweepEndMapTheta _ _) (fun _ _ => Set.mem_univ _)
  split_ifs
  · exact shrinksFresh_snapshotMap j _
  · exact shrinksFresh_id _

theorem shrinksFresh_resetMapA (t : ℝ) (I : Set (RunRecord d m)) :
    ShrinksFresh (resetMapA (d := d) (m := m) t) I := fun _ _ => le_rfl

theorem shrinksFresh_stageMap (P : TilePlan d m) (j : ℕ) :
    ShrinksFresh (stageMap P j) Set.univ := by
  unfold stageMap
  refine ShrinksFresh.comp (J := Set.univ) (shrinksFresh_sweepStartMap _ _ _)
    (ShrinksFresh.comp (J := Set.univ) ?_ (shrinksFresh_resetMapA _ _) (fun _ _ => Set.mem_univ _)) (fun _ _ => Set.mem_univ _)
  split_ifs
  · exact shrinksFresh_cutoffMap _
  · exact shrinksFresh_id _

/-- **Locality of the first-trial failure** (`hlocal` of `blockRun_of_disciplines`). -/
theorem runOps_local (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m)) (M : ℕ → ℕ)
    (hclr : ∀ j y x, DependsOnly (Torus d m) (M := M) (clrPat j y x)
      (localFirstFail M (clr j y) x)) :
    ∀ n x, DependsOnly (Torus d m) (M := M) (schedulePattern P clrPat n x)
      (localFirstFail M (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x) := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  have hk := decodeK_lt (d := d) (m := m) n
  generalize decodeJ d m n = j
  generalize decodeK d m n = k at hk
  generalize decodeY d m n = y
  rw [scheduleBlocks_opIndex _ j k y hk, schedulePattern_opIndex _ _ j k y hk]
  intro x
  unfold runOp runPattern
  by_cases hj : P.n₀ < j ∧ j ≤ m + 1
  · rw [if_pos hj, if_pos hj]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, if_pos rfl]
      cases tileAt P j y with
      | some T =>
        show DependsOnly _ _ (localFirstFail M ((tileBlock P j T).embed (tileEmbed cl₀) tileProj) x)
        rw [localFirstFail_embed M (tileBlock P j T) (tileEmbed cl₀) tileProj (fun _ => rfl)]
        exact tileBlock_fail_local P j T M x
      | none => exact simpleBlock_dependsOnly M (ts₀, cl₀) _ _ x
    · rw [if_neg hk0, if_neg hk0]
      by_cases hk1 : k = 1
      · subst hk1
        rw [if_pos rfl, if_neg (by omega)]
        split_ifs <;> exact simpleBlock_dependsOnly M (ts₀, cl₀) _ _ x
      · rw [if_neg hk1]
        by_cases hk2 : k = 2 ∧ j ≤ m / 2
        · obtain ⟨rfl, hjm⟩ := hk2
          rw [if_pos rfl, if_pos hjm, if_pos ⟨rfl, hjm⟩]
          rw [localFirstFail_embed M (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl)]
          exact hclr j y x
        · rw [if_neg hk2]
          split_ifs <;> first
            | exact simpleBlock_dependsOnly M (ts₀, cl₀) _ _ x
            | (exfalso; exact hk2 ⟨by assumption, by assumption⟩)
  · rw [if_neg hj, if_neg hj]
    exact simpleBlock_dependsOnly M (ts₀, cl₀) _ _ x

/-- **Query discipline of the schedule** (`hquery` of `blockRun_of_disciplines`). -/
theorem runOps_query (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (M : ℕ → ℕ) (htile : TileQueryStatement)
    (hclr : ∀ j y x k (ω : RandomSources (Torus d m) M),
      (∀ k' < k, (clr j y).halted (localState M (clr j y) x k' ω) = false) →
      (clr j y).halted (localState M (clr j y) x k ω) = true →
      declaredFresh ((clr j y).exit (localState M (clr j y) x k ω)) ⊆ declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((clr j y).exit (localState M (clr j y) x k ω)),
        z ∉ querySigns (Torus d m) ((clr j y).next (localState M (clr j y) x k' ω))) :
    ∀ n x k (ω : RandomSources (Torus d m) M),
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState M (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω) = false) →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState M (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) = true →
      declaredFresh ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
        (localState M (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω)) ⊆ declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
          (localState M (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω)),
        z ∉ querySigns (Torus d m) ((scheduleBlocks (runOp P ts₀ cl₀ clr) n).next
          (localState M (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω)) := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  have hk := decodeK_lt (d := d) (m := m) n
  generalize decodeJ d m n = j
  generalize decodeK d m n = k at hk
  generalize decodeY d m n = y
  rw [scheduleBlocks_opIndex _ j k y hk]
  have hid := simpleBlock_query M (ts₀, cl₀) (id : RunRecord d m → RunRecord d m) declaredFresh
    (fun _ => le_rfl)
  unfold runOp
  split_ifs with hj hk0 hk1 hy hk2 hjm hjy
  · subst hk0
    cases tileAt P j y with
    | some T =>
      exact embed_query M (tileBlock P j T) (tileEmbed cl₀) tileProj (fun _ => rfl) declaredFresh
        (querySigns (Torus d m)) (htile d m P j T M)
    | none => exact hid
  · exact simpleBlock_query M (ts₀, cl₀) _ declaredFresh (guardMap_fresh (shrinksFresh_endMap P j))
  · exact hid
  · exact embed_query M (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl) declaredFresh
      (querySigns (Torus d m)) (hclr j y)
  · exact hid
  · exact simpleBlock_query M (ts₀, cl₀) _ declaredFresh
      (guardMap_fresh (shrinksFresh_stageMap P j))
  · exact hid
  · exact hid

/-- **Pattern discipline of the schedule** (`hpat` of `blockRun_of_disciplines`). -/
theorem runOps_pat (P : TilePlan d m)
    (clrPat : ℕ → Torus d m → RunRecord d m → FreshPattern (Torus d m))
    (htile : TilePatternStatement)
    (hclr : ∀ j y x, (∀ z ∈ (clrPat j y x).signs, z ∈ declaredFresh x) ∧
      (clrPat j y x).orders = ∅) :
    ∀ n x, (∀ z ∈ (schedulePattern P clrPat n x).signs,
        z ∈ declaredFresh x ∨ ∃ a ∈ scheduleSets (d := d) (m := m) (runAuxSet P) n,
          z = Sum.inr a) ∧
      ∀ o ∈ (schedulePattern P clrPat n x).orders, o ∈ scheduleSets (runOrderSet P) n := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  have hk := decodeK_lt (d := d) (m := m) n
  generalize decodeJ d m n = j
  generalize decodeK d m n = k at hk
  generalize decodeY d m n = y
  rw [schedulePattern_opIndex _ _ j k y hk, scheduleSets_opIndex _ j k y hk,
    scheduleSets_opIndex _ j k y hk]
  intro x
  have hempty : (∀ z ∈ (emptyPattern d m).signs, z ∈ declaredFresh x ∨
      ∃ a ∈ runAuxSet P j k y, z = Sum.inr a) ∧
      ∀ o ∈ (emptyPattern d m).orders, o ∈ runOrderSet P j k y := by
    refine ⟨fun z hz => ?_, fun o ho => ?_⟩
    · rw [emptyPattern_signs] at hz; exact absurd hz (Set.notMem_empty z)
    · simp [emptyPattern] at ho
  unfold runPattern
  by_cases hj : P.n₀ < j ∧ j ≤ m + 1
  · rw [if_pos hj]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl]
      unfold runAuxSet runOrderSet
      rw [if_pos ⟨hj.1, hj.2, rfl⟩, if_pos ⟨hj.1, hj.2, rfl⟩]
      cases tileAt P j y with
      | some T => exact htile d m P j T x
      | none =>
        refine ⟨fun z hz => ?_, fun o ho => ?_⟩
        · rw [emptyPattern_signs] at hz; exact absurd hz (Set.notMem_empty z)
        · simp [emptyPattern] at ho
    · rw [if_neg hk0]
      split_ifs with hk2
      · refine ⟨fun z hz => Or.inl ((hclr j y x).1 z hz), fun o ho => ?_⟩
        rw [(hclr j y x).2] at ho
        exact absurd ho (Finset.notMem_empty o)
      · exact hempty
  · rw [if_neg hj]
    exact hempty

end AndersonAC.AgentS78
