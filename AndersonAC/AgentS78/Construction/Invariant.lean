import AndersonAC.AgentS78.Construction.Blocks

/-!
# WP10 construction, C5b glue: invariants along every history of the run

07-assembly.tex:939–946: the stage bounds hold "along every finite history produced by
the ordinary-sweep and clearing rules, with failed trials rolled back". For the block run
this is a pathwise induction: if the initial record satisfies `Inv 0`, and every block `n`
started from a record in `Inv n` can only halt (whatever the answers) with an exit record
in `Inv (n+1)`, then, for every sample, the record with which block `n` is entered lies in
`Inv n` (`blockPrestate_mem`). No probability is involved.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources Query Answer)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Rec St : Type}

/-- States a block can reach from a record, whatever the answers. -/
inductive BlockReach (B : Block ι Rec St) (x : Rec) : St → Prop
  | enter : BlockReach B x (B.enter x)
  | step (s : St) (a : Answer ι) : BlockReach B x s → B.halted s = false →
      BlockReach B x (B.update s a)

/-- The global run state after `q + 1` operations. -/
theorem runState_succ (M : ℕ → ℕ) (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (q : ℕ)
    (ω : RandomSources ι M) : ∃ a : Answer ι,
    runState M blocks rec₀ (q + 1) ω = gupdate blocks (runState M blocks rec₀ q ω) a :=
  ⟨_, rfl⟩

theorem runState_zero (M : ℕ → ℕ) (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
    (ω : RandomSources ι M) : runState M blocks rec₀ 0 ω = gInit blocks rec₀ := rfl

/-- **Invariants propagate along every history of the block run.** -/
theorem runState_inv (M : ℕ → ℕ) (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
    (Inv : ℕ → Set Rec) (h₀ : rec₀ ∈ Inv 0)
    (hblock : ∀ n x, x ∈ Inv n → ∀ s, BlockReach (blocks n) x s →
      (blocks n).halted s = true → (blocks n).exit s ∈ Inv (n + 1))
    (q : ℕ) (ω : RandomSources ι M) :
    (runState M blocks rec₀ q ω).2.1 ∈ Inv (runState M blocks rec₀ q ω).1 ∧
      BlockReach (blocks (runState M blocks rec₀ q ω).1) (runState M blocks rec₀ q ω).2.1
        (runState M blocks rec₀ q ω).2.2 := by
  induction q with
  | zero =>
    rw [runState_zero]
    exact ⟨h₀, BlockReach.enter⟩
  | succ q ih =>
    obtain ⟨a, ha⟩ := runState_succ M blocks rec₀ q ω
    rw [ha]
    obtain ⟨hinv, hreach⟩ := ih
    set g := runState M blocks rec₀ q ω
    unfold gupdate
    cases hh : (blocks g.1).halted g.2.2
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨hinv, BlockReach.step _ a hreach hh⟩
    · simp only [ite_true]
      exact ⟨hblock g.1 g.2.1 hinv g.2.2 hreach hh, BlockReach.enter⟩

/-- **The record entering block `n` satisfies `Inv n`** whenever block `n` is reached. -/
theorem blockPrestate_mem (M : ℕ → ℕ) (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
    (Inv : ℕ → Set Rec) (h₀ : rec₀ ∈ Inv 0)
    (hblock : ∀ n x, x ∈ Inv n → ∀ s, BlockReach (blocks n) x s →
      (blocks n).halted s = true → (blocks n).exit s ∈ Inv (n + 1))
    (n : ℕ) (ω : RandomSources ι M) (hn : blockStart M blocks rec₀ n ω ≠ ⊤) :
    blockPrestate M blocks rec₀ n ω ∈ Inv n := by
  classical
  unfold blockPrestate
  unfold blockStart at hn ⊢
  by_cases h : ∃ q, (runState M blocks rec₀ q ω).1 = n
  · rw [dif_pos h]
    have hq := Nat.find_spec h
    have hinv := (runState_inv M blocks rec₀ Inv h₀ hblock (Nat.find h) ω).1
    rw [hq] at hinv
    exact hinv
  · rw [dif_neg h] at hn
    exact absurd rfl hn

/-- The `prestate_good` field of `BlockRun` from a propagated invariant. -/
theorem prestate_good_of_inv (M : ℕ → ℕ) (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
    (Inv : ℕ → Set Rec) (h₀ : rec₀ ∈ Inv 0)
    (hblock : ∀ n x, x ∈ Inv n → ∀ s, BlockReach (blocks n) x s →
      (blocks n).halted s = true → (blocks n).exit s ∈ Inv (n + 1))
    (μ : Measure (RandomSources ι M)) (good : ℕ → Set Rec) (hgood : ∀ n, Inv n ⊆ good n)
    (n : ℕ) (hfin : ∀ᵐ ω ∂μ, blockStart M blocks rec₀ n ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, blockPrestate M blocks rec₀ n ω ∈ good n := by
  filter_upwards [hfin] with ω hω
  exact hgood n (blockPrestate_mem M blocks rec₀ Inv h₀ hblock n ω hω)

end AndersonAC.AgentS78
