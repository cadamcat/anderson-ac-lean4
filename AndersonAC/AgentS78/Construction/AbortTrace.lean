import AndersonAC.AgentS78.Construction.RunChain

/-!
# tracing an abort back to its cause

02-state.tex:349–362, 05:519–521, 08:299–305: the run aborts only at a late first-trial
failure (a tile trial after the cutoff, or of the final residual sweep) or at the cutoff when
a site is still pending. `abort_along_run` proves pathwise, from the per-block abort
discipline (`hblock`: a block that exits aborted was entered aborted, or its first trial
failed and it is late, or it has the other cause, e.g. it is the cutoff entered with a
pending site), that an aborted entering record of block `b` comes from an aborted record at
`a ≤ b` or from such a cause at a reached block `n ∈ [a, b)`. This is the `failure_cover`
field of `BlockRun` once `success` is "the final record is not aborted".
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
variable (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (orderSet auxSet : ℕ → Set ℕ)

/-- **Abort trace along the run.** -/
theorem abort_along_run
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (ab : Rec → Prop) (late : ℕ → Prop) (cause : ℕ → Rec → Prop)
    (hblock : ∀ n x s, BlockReach (blocks n) x s → (blocks n).halted s = true →
      ab ((blocks n).exit s) → ab x ∨ ((blocks n).firstFail s = true ∧ late n) ∨ cause n x)
    (a : ℕ) (ω : RandomSources ι M) :
    ∀ b, a ≤ b → blockStart M blocks rec₀ b ω ≠ ⊤ → ab (blockPrestate M blocks rec₀ b ω) →
      ab (blockPrestate M blocks rec₀ a ω) ∨
      ∃ n, a ≤ n ∧ n < b ∧ blockStart M blocks rec₀ n ω ≠ ⊤ ∧
        ((ω ∈ globalFirstFail M blocks rec₀ n ∧ late n) ∨
          cause n (blockPrestate M blocks rec₀ n ω)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _ h; exact Or.inl h
  | succ b hab ih =>
    intro hb habort
    obtain ⟨q, hq1, hq2, hhalt, hexit, hreach, hbn⟩ :=
      prestate_succ M blocks rec₀ orderSet auxSet hdisj horders haux b ω hb
    rw [hexit] at habort
    rcases hblock b _ _ hreach hhalt habort with h | ⟨hff, hl⟩ | hc
    · rcases ih hbn h with h' | ⟨n, h1, h2, h3, h4⟩
      · exact Or.inl h'
      · exact Or.inr ⟨n, h1, Nat.lt_succ_of_lt h2, h3, h4⟩
    · exact Or.inr ⟨b, hab, Nat.lt_succ_self b, hbn, Or.inl ⟨⟨q, hq1, hff⟩, hl⟩⟩
    · exact Or.inr ⟨b, hab, Nat.lt_succ_self b, hbn, Or.inr hc⟩

/-- **The `failure_cover` shape.** If the initial record is not aborted, an aborted entering
record of a reached block `b` comes from a late global first failure, with the block-local
failure from its entering record (`hloc`, clause 4 of `blockComposition_proof`), or from the
other cause at a reached block before `b`. -/
theorem abort_cover
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (ab : Rec → Prop) (late : ℕ → Prop) (cause : ℕ → Rec → Prop)
    (hblock : ∀ n x s, BlockReach (blocks n) x s → (blocks n).halted s = true →
      ab ((blocks n).exit s) → ab x ∨ ((blocks n).firstFail s = true ∧ late n) ∨ cause n x)
    (hloc : ∀ n ω, blockStart M blocks rec₀ n ω ≠ ⊤ →
      (ω ∈ globalFirstFail M blocks rec₀ n ↔
        ω ∈ localFirstFail M (blocks n) (blockPrestate M blocks rec₀ n ω)))
    (h₀ : ¬ ab rec₀) (ω : RandomSources ι M) (b : ℕ)
    (hb : blockStart M blocks rec₀ b ω ≠ ⊤) (habort : ab (blockPrestate M blocks rec₀ b ω)) :
    ∃ n, n < b ∧ blockStart M blocks rec₀ n ω ≠ ⊤ ∧
      ((ω ∈ localFirstFail M (blocks n) (blockPrestate M blocks rec₀ n ω) ∧ late n) ∨
        cause n (blockPrestate M blocks rec₀ n ω)) := by
  have hstart0 : blockStart M blocks rec₀ 0 ω ≠ ⊤ :=
    reached_of_le M blocks rec₀ orderSet auxSet hdisj horders haux ω b hb 0 (Nat.zero_le b)
  have hpre0 : blockPrestate M blocks rec₀ 0 ω = rec₀ := by
    have h := blockPrestate_mem M blocks rec₀ (fun n => {x | n = 0 → x = rec₀}) (fun _ => rfl)
      (fun n x _ s _ _ h => absurd h (Nat.succ_ne_zero n)) 0 ω hstart0
    exact h rfl
  rcases abort_along_run M blocks rec₀ orderSet auxSet hdisj horders haux ab late cause hblock 0 ω
      b (Nat.zero_le b) hb habort with h | ⟨n, -, h2, h3, h4⟩
  · rw [hpre0] at h; exact absurd h h₀
  · refine ⟨n, h2, h3, ?_⟩
    rcases h4 with ⟨hf, hl⟩ | hc
    · exact Or.inl ⟨(hloc n ω h3).mp hf, hl⟩
    · exact Or.inr hc

end AndersonAC.AgentS78
