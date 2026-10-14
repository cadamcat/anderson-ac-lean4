import AndersonAC.AgentS78.Construction.RunOps
import AndersonAC.AgentS78.Construction.BlocksProof

/-!
# WP10 construction: order and auxiliary disciplines of the schedule

The block sequence `scheduleBlocks (runOp …)` with the order sizes `tileOrderSize P` and the
index sets `runOrderSet`, `runAuxSet` satisfies the order and auxiliary disciplines of
`BlockRun` (`BlocksProof.HOrders`, `HAux`), given that the clearing blocks issue no order or
auxiliary query (muse-s78clear's `clearingBlock_orders`/`clearingBlock_aux`, for every target
set).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

theorem scheduleSets_opIndex {α : Type} (S : ℕ → ℕ → Torus d m → Set α) (j k : ℕ)
    (y : Torus d m) (hk : k < 4) : scheduleSets S (opIndex d m j k y) = S j k y := by
  obtain ⟨h1, h2, h3⟩ := decode_opIndex j k y hk
  unfold scheduleSets
  rw [h1, h2, h3]

/-- **Order discipline of the schedule.** -/
theorem runOps_orders (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (hclr : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω o,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.nextOrder o →
      o ∈ S ∧ ((List.range k).filter fun k' =>
        (clr j y).halted (localState M (clr j y) x k' ω) = false ∧
        (clr j y).next (localState M (clr j y) x k' ω) = Query.nextOrder o).length < M o) :
    BlocksProof.HOrders (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr))
      (scheduleSets (runOrderSet P)) := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  have hk := decodeK_lt (d := d) (m := m) n
  generalize decodeJ d m n = j
  generalize decodeK d m n = k at hk
  generalize decodeY d m n = y
  rw [scheduleBlocks_opIndex _ j k y hk, scheduleSets_opIndex _ j k y hk]
  unfold runOp runOrderSet
  by_cases hj : P.n₀ < j ∧ j ≤ m + 1
  · rw [if_pos hj]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, if_pos ⟨hj.1, hj.2, rfl⟩]
      cases tileAt P j y with
      | some T =>
        exact embed_orders _ (tileBlock P j T) (tileEmbed cl₀) tileProj (fun _ => rfl) _
          (tileBlock_orders P j T _ (tileOrderSize_index P j T))
      | none => exact simpleBlock_orders _ _ _ _
    · rw [if_neg hk0, if_neg (show ¬(P.n₀ < j ∧ j ≤ m + 1 ∧ k = 0) from fun h => hk0 h.2.2)]
      split_ifs
      · exact simpleBlock_orders _ _ _ _
      · exact simpleBlock_orders _ _ _ _
      · exact embed_orders _ (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl) _
          (hclr j y _ _)
      · exact simpleBlock_orders _ _ _ _
      · exact simpleBlock_orders _ _ _ _
      · exact simpleBlock_orders _ _ _ _
  · rw [if_neg hj, if_neg (show ¬(P.n₀ < j ∧ j ≤ m + 1 ∧ k = 0) from fun h => hj ⟨h.1, h.2.1⟩)]
    exact simpleBlock_orders _ _ _ _

/-- **Auxiliary discipline of the schedule.** -/
theorem runOps_aux (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (M : ℕ → ℕ)
    (hclr : ∀ j y (S : Set ℕ), ∀ x k ω a,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.auxiliary a →
      a ∈ S ∧ ∀ k' < k, (clr j y).halted (localState M (clr j y) x k' ω) = false →
        (clr j y).next (localState M (clr j y) x k' ω) ≠ Query.auxiliary a) :
    BlocksProof.HAux M (scheduleBlocks (runOp P ts₀ cl₀ clr)) (scheduleSets (runAuxSet P)) := by
  intro n
  rw [← opIndex_decode (d := d) (m := m) n]
  have hk := decodeK_lt (d := d) (m := m) n
  generalize decodeJ d m n = j
  generalize decodeK d m n = k at hk
  generalize decodeY d m n = y
  rw [scheduleBlocks_opIndex _ j k y hk, scheduleSets_opIndex _ j k y hk]
  unfold runOp runAuxSet
  by_cases hj : P.n₀ < j ∧ j ≤ m + 1
  · rw [if_pos hj]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, if_pos ⟨hj.1, hj.2, rfl⟩]
      cases tileAt P j y with
      | some T =>
        exact embed_aux _ (tileBlock P j T) (tileEmbed cl₀) tileProj (fun _ => rfl) _
          (tileBlock_aux P j T M)
      | none => exact simpleBlock_aux _ _ _ _
    · rw [if_neg hk0, if_neg (show ¬(P.n₀ < j ∧ j ≤ m + 1 ∧ k = 0) from fun h => hk0 h.2.2)]
      split_ifs
      · exact simpleBlock_aux _ _ _ _
      · exact simpleBlock_aux _ _ _ _
      · exact embed_aux _ (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl) _ (hclr j y _)
      · exact simpleBlock_aux _ _ _ _
      · exact simpleBlock_aux _ _ _ _
      · exact simpleBlock_aux _ _ _ _
  · rw [if_neg hj, if_neg (show ¬(P.n₀ < j ∧ j ≤ m + 1 ∧ k = 0) from fun h => hj ⟨h.1, h.2.1⟩)]
    exact simpleBlock_aux _ _ _ _

end AndersonAC.AgentS78
