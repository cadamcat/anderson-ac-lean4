import AndersonAC.AgentS78.Construction.MarkingRule

/-!
# the chain of entering records of a reached block

If block `b` is reached, every earlier block was reached, and the entering records of
consecutive blocks are related by the earlier block: the later one is the exit record of a
halting state reachable from the earlier one (`run_chain`). This feeds the record-level
lemmas (`chain_untouched`, `snapshot_rule`, `stage_dichotomy`) with the actual run.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
variable (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (orderSet auxSet : ℕ → Set ℕ)

/-- The block relation: `x'` is the exit record of a halting state reachable from `x`. -/
def BlockStep (n : ℕ) (x x' : Rec) : Prop :=
  ∃ s, BlockReach (blocks n) x s ∧ (blocks n).halted s = true ∧ x' = (blocks n).exit s

theorem reached_of_le
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (ω : RandomSources ι M) (b : ℕ) (hb : blockStart M blocks rec₀ b ω ≠ ⊤) :
    ∀ n, n ≤ b → blockStart M blocks rec₀ n ω ≠ ⊤ := by
  have key : ∀ k n, n + k = b → blockStart M blocks rec₀ n ω ≠ ⊤ := by
    intro k
    induction k with
    | zero => intro n h; simp at h; rw [h]; exact hb
    | succ k ih =>
      intro n h
      obtain ⟨_, -, -, -, -, -, hprev⟩ :=
        prestate_succ M blocks rec₀ orderSet auxSet hdisj horders haux n ω (ih (n + 1) (by omega))
      exact hprev
  intro n hn
  exact key (b - n) n (by omega)

/-- **The chain of entering records.** -/
theorem run_chain
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (ω : RandomSources ι M) (b : ℕ) (hb : blockStart M blocks rec₀ b ω ≠ ⊤) :
    ∀ n, n < b → BlockStep blocks n (blockPrestate M blocks rec₀ n ω)
      (blockPrestate M blocks rec₀ (n + 1) ω) := by
  intro n hn
  obtain ⟨q, -, hq2, hhalt, hexit, hreach, -⟩ := prestate_succ M blocks rec₀ orderSet auxSet
    hdisj horders haux n ω (reached_of_le M blocks rec₀ orderSet auxSet hdisj horders haux ω b hb
      (n + 1) hn)
  exact ⟨_, hreach, hhalt, hexit⟩

end AndersonAC.AgentS78
