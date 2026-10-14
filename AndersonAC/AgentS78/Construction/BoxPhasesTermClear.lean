import AndersonAC.AgentS78.Construction.BoxPhasesClear

/-!
# Clearing blocks: sites leaving the active set become terminal (agent-s78box)

`clear_exit_inactive`: if every inactive site of the entering record is terminal, so is every
inactive site of the exit of a clearing block (DONE removes `core` from the active set and makes
`core ∪ inspected` terminal; the scratch only erases inspected pivots and core sites from its
active set).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

section Reach
variable (n₀ j : ℕ) (u : ℝ) (yy : Torus d m) (x : RunRecord d m)

/-- Reachable scratch states: the core list stays inside the core, and every active site of the
entering record erased from the scratch active set is an inspected pivot or a core site. -/
theorem clear_reach_inactive (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock n₀ j u yy) x s) :
    s.2.coreLeft ⊆ s.2.core ∧
      ∀ i ∈ x.endpoint.active, i ∉ s.2.active → i ∈ s.2.inspected ∨ i ∈ s.2.core := by
  classical
  induction hs with
  | enter =>
    refine ⟨?_, ?_⟩
    · simp [clearingBlock, clearInitScratch]
    · intro i hi hn; simp [clearingBlock, clearInitScratch] at hn; exact absurd hi hn
  | step s a _ _ ih =>
    obtain ⟨h1, h2⟩ := ih
    show (clearingUpdate n₀ j u s a).2.coreLeft ⊆ (clearingUpdate n₀ j u s a).2.core ∧
      ∀ i ∈ x.endpoint.active, i ∉ (clearingUpdate n₀ j u s a).2.active →
        i ∈ (clearingUpdate n₀ j u s a).2.inspected ∨ i ∈ (clearingUpdate n₀ j u s a).2.core
    unfold clearingUpdate
    dsimp only
    split
    · exact ⟨h1, h2⟩
    · cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
      | fail po =>
        refine ⟨h1, fun i hi hn => ?_⟩
        rcases h2 i hi hn with h | h
        · left
          cases po with
          | none => exact h
          | some p => exact Finset.mem_insert_of_mem h
        · exact Or.inr h
      | coreReady => exact ⟨h1, h2⟩
      | heat p hg =>
        dsimp only
        have key : ∀ i ∈ x.endpoint.active, i ∉ s.2.active.erase p →
            i ∈ insert p s.2.inspected ∨ i ∈ s.2.core := by
          intro i hi hn
          by_cases hip : i = p
          · exact Or.inl (Finset.mem_insert.mpr (Or.inl hip))
          · have : i ∉ s.2.active := fun h' => hn (Finset.mem_erase.mpr ⟨hip, h'⟩)
            rcases h2 i hi this with h | h
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · exact Or.inr h
        split_ifs <;> exact ⟨h1, key⟩
      | coreQuery y hc =>
        dsimp only
        have hy : y ∈ s.2.core := h1 (actionOf_coreQuery_mem (j := j) (u := u) s.1 s.2 y hc hact)
        refine ⟨fun i hi => h1 (Finset.mem_of_mem_erase hi), fun i hi hn => ?_⟩
        by_cases hiy : i = y
        · exact Or.inr (hiy ▸ hy)
        · have : i ∉ s.2.active := fun h' => hn (Finset.mem_erase.mpr ⟨hiy, h'⟩)
          exact h2 i hi this
      | finish => exact ⟨h1, h2⟩

/-- **Inactive sites stay terminal through a clearing block.** -/
theorem clear_exit_inactive (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock n₀ j u yy) x s)
    (hx : ∀ i, i ∉ x.endpoint.active → i ∈ x.terminal) :
    ∀ i, i ∉ ((clearingBlock n₀ j u yy).exit s).endpoint.active →
      i ∈ ((clearingBlock n₀ j u yy).exit s).terminal := by
  classical
  obtain ⟨h1, -, -⟩ := clear_reach n₀ j u yy x s hs
  obtain ⟨-, h2⟩ := clear_reach_inactive n₀ j u yy x s hs
  obtain ⟨r, sc⟩ := s
  simp only at h1 h2
  subst h1
  have hex : (clearingBlock n₀ j u yy).exit (r, sc) = clearingExit j yy (r, sc) := rfl
  rw [hex]
  unfold clearingExit
  simp only
  split_ifs with ha hsch hcore hfail hdone
  · exact hx
  · exact hx
  · exact hx
  · exact hx
  · intro i hi
    simp only [clearingDoneExit, Finset.mem_sdiff, not_and, not_not] at hi ⊢
    by_cases hia : i ∈ r.endpoint.active
    · by_cases his : i ∈ sc.active
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hi his))
      · rcases h2 i hia his with h | h
        · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hx i hia))
  · exact hx

end Reach

end AndersonAC.AgentS78
