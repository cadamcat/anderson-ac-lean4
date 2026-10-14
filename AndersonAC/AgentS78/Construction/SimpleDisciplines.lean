import AndersonAC.AgentS78.Construction.Freshness
import AndersonAC.AgentS78.Construction.Transitions

/-!
# WP10 construction: the per-block disciplines of query-free blocks

For a query-free block `simpleBlock sc₀ f` the only reachable state is the entering one,
and it halts at once with exit record `f x`. Hence it satisfies the marking discipline of
`step_of_marking`, the query discipline of `fresh_of_declared` and the invariant step of
`runState_inv` as soon as `f` does at the record level. The snapshot and cutoff maps keep
the pending sets and labels.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources querySigns SignIndex)

variable {d m : ℕ} {Sc : Type}

theorem simpleBlock_reach (sc₀ : Sc) (f : RunRecord d m → RunRecord d m) (x : RunRecord d m)
    (s : RunRecord d m × Sc) (h : BlockReach (simpleBlock sc₀ f) x s) : s = (f x, sc₀) := by
  cases h with
  | enter => rfl
  | step s a _ hh => simp [simpleBlock] at hh

/-- Invariant step of a query-free block. -/
theorem simpleBlock_inv (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (I I' : Set (RunRecord d m)) (hf : ∀ x ∈ I, f x ∈ I') :
    ∀ x, x ∈ I → ∀ s, BlockReach (simpleBlock sc₀ f) x s →
      (simpleBlock sc₀ f).halted s = true → (simpleBlock sc₀ f).exit s ∈ I' := by
  intro x hx s hs _
  rw [simpleBlock_reach sc₀ f x s hs]
  exact hf x hx

/-- Marking discipline of a query-free block that keeps pending sites and their labels. -/
theorem simpleBlock_marking {α L : Type} (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (pend : RunRecord d m → Finset α) (lab : RunRecord d m → α → L) (P : α → Prop)
    (hf : ∀ x, pend (f x) ⊆ pend x ∧ ∀ y ∈ pend (f x), lab (f x) y = lab x y) :
    ∀ x s, BlockReach (simpleBlock sc₀ f) x s → (simpleBlock sc₀ f).halted s = true →
      ∀ y ∈ pend ((simpleBlock sc₀ f).exit s),
        (y ∈ pend x ∧ lab ((simpleBlock sc₀ f).exit s) y = lab x y) ∨ P y := by
  intro x s hs _ y hy
  rw [simpleBlock_reach sc₀ f x s hs] at hy ⊢
  exact Or.inl ⟨(hf x).1 hy, (hf x).2 y hy⟩

/-- Query discipline of a query-free block whose map only shrinks the declared set. -/
theorem simpleBlock_query (M : ℕ → ℕ) (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (freshSet : RunRecord d m → Set (SignIndex (Torus d m)))
    (hf : ∀ x, freshSet (f x) ⊆ freshSet x) :
    ∀ x k (ω : RandomSources (Torus d m) M),
      (∀ k' < k, (simpleBlock sc₀ f).halted (localState M (simpleBlock sc₀ f) x k' ω) = false) →
      (simpleBlock sc₀ f).halted (localState M (simpleBlock sc₀ f) x k ω) = true →
      freshSet ((simpleBlock sc₀ f).exit (localState M (simpleBlock sc₀ f) x k ω)) ⊆ freshSet x ∧
      ∀ k' < k, ∀ z ∈ freshSet ((simpleBlock sc₀ f).exit (localState M (simpleBlock sc₀ f) x k ω)),
        z ∉ querySigns (Torus d m) ((simpleBlock sc₀ f).next (localState M (simpleBlock sc₀ f) x k' ω)) := by
  intro x k ω hk _
  cases k with
  | zero =>
    refine ⟨?_, fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩
    show freshSet (f x) ⊆ freshSet x
    exact hf x
  | succ k =>
    have := hk 0 (Nat.succ_pos k)
    simp [simpleBlock] at this

theorem snapshotMap_keeps (j : ℕ) (x : RunRecord d m) :
    (snapshotMap j x).pending = x.pending ∧ (snapshotMap j x).latest = x.latest := ⟨rfl, rfl⟩

theorem cutoffMap_keeps (x : RunRecord d m) :
    (cutoffMap x).pending = x.pending ∧ (cutoffMap x).latest = x.latest := ⟨rfl, rfl⟩

/-- Before the first operation of the run proper all blocks are empty, so every reached
block below `N` is entered with the initial record (the `before` field of `BlockRun`:
no site is pending before stage `n₀+1`). -/
theorem prestate_eq_init_of_empty (M : ℕ → ℕ) (sc₀ : Sc)
    (blocks : ℕ → Block (Torus d m) (RunRecord d m) (RunRecord d m × Sc)) (rec₀ : RunRecord d m)
    (N : ℕ) (hempty : ∀ n < N, blocks n = simpleBlock sc₀ id)
    (n : ℕ) (hn : n ≤ N) (ω : RandomSources (Torus d m) M)
    (hst : blockStart M blocks rec₀ n ω ≠ ⊤) : blockPrestate M blocks rec₀ n ω = rec₀ := by
  have h := blockPrestate_mem M blocks rec₀ (fun n => {x | n ≤ N → x = rec₀})
    (fun _ => rfl)
    (fun n x hx s hs hh => by
      intro hn1
      have hlt : n < N := by omega
      rw [hempty n hlt] at hs hh ⊢
      rw [simpleBlock_reach sc₀ id x s hs]
      exact hx (by omega))
    n ω hst
  exact h hn

end AndersonAC.AgentS78
