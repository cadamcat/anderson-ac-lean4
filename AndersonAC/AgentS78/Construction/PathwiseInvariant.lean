import AndersonAC.AgentS78.Construction.RunChain

/-!
# WP10 construction, C5b glue: pathwise invariants along the actual run

`runState_inv` / `blockPrestate_mem` propagate record invariants over *all* answers. Some
invariants of the run hold only along the answers of the sample `ω` itself, e.g. that the
installed values are `λ` times the true binary prefixes of `ω` (02-state.tex:96–103), which
gives `installed = λ V(ω)` after the final residual sweep (PhysicalIdentity.lean,
`installedShifted_eq_true`). `blockPrestate_mem_pathwise` propagates an invariant along the
block-local runs with the answers of `ω` (the global run inside block `n` is the block-local
run from the entering record with the same `ω`, `BlocksProof.at_time`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources Query Answer)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
variable (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (orderSet auxSet : ℕ → Set ℕ)

/-- **Consecutive entering records along the actual run**: the exit record of block `n`'s
block-local run with the answers of `ω` enters block `n+1`. -/
theorem prestate_succ_local
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (n : ℕ) (ω : RandomSources ι M) (h : blockStart M blocks rec₀ (n + 1) ω ≠ ⊤) :
    ∃ k, (∀ k' < k, (blocks n).halted
          (localState M (blocks n) (blockPrestate M blocks rec₀ n ω) k' ω) = false) ∧
      (blocks n).halted (localState M (blocks n) (blockPrestate M blocks rec₀ n ω) k ω) = true ∧
      blockPrestate M blocks rec₀ (n + 1) ω =
        (blocks n).exit (localState M (blocks n) (blockPrestate M blocks rec₀ n ω) k ω) := by
  obtain ⟨s', x', hE'⟩ := BlocksProof.entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet
    hdisj horders haux h
  have hs'1 := hE'.1
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    have := congrArg (fun g => g.1) hs'1
    simp only at this
    have h0 := BlocksProof.index_zero M blocks rec₀ ω
    rw [this] at h0
    exact Nat.succ_ne_zero n h0
  obtain ⟨q, rfl⟩ : ∃ q, s' = q + 1 := ⟨s' - 1, by omega⟩
  obtain ⟨n₁, s, x, hsq, hE, hrun, hG⟩ := BlocksProof.at_time M blocks rec₀ orderSet auxSet
    hdisj horders haux ω q
  have hlt : (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.1 < n + 1 :=
    hE'.2.2 q (Nat.lt_succ_self q)
  rw [hG] at hlt
  simp only at hlt
  have hsucc := BlocksProof.machineRun_succ M (gInit blocks rec₀) (gnext blocks) (gupdate blocks)
    q ω
  rw [hG] at hsucc
  rw [hsucc] at hs'1
  simp only at hs'1
  set st := localState M (blocks n₁) x (q - s) ω with hst
  have hhalt : (blocks n₁).halted st = true := by
    by_contra hne
    have hf : (blocks n₁).halted st = false := by simpa using hne
    have := congrArg (fun g => g.1) hs'1
    simp only [gupdate, hf] at this
    simp at this
    omega
  have hn₁ : n₁ = n := by
    have := congrArg (fun g => g.1) hs'1
    simp only [gupdate, hhalt, ite_true] at this
    omega
  subst hn₁
  have hx' : x' = (blocks n₁).exit st := by
    have := congrArg (fun g => g.2.1) hs'1
    simp only [gupdate, hhalt, ite_true] at this
    exact this.symm
  have hpre : blockPrestate M blocks rec₀ n₁ ω = x :=
    BlocksProof.blockPrestate_eq M blocks rec₀ orderSet auxSet hE
  have hpre' : blockPrestate M blocks rec₀ (n₁ + 1) ω = x' :=
    BlocksProof.blockPrestate_eq M blocks rec₀ orderSet auxSet hE'
  have hrs : runState M blocks rec₀ q ω = (n₁, x, st) := by
    rw [BlocksProof.runState_eq, hG]
  refine ⟨q - s, ?_, ?_, ?_⟩
  · rw [hpre]; exact hrun
  · rw [hpre]; exact hhalt
  · rw [hpre', hpre, hx']

/-- The record entering block `0` is the initial record. -/
theorem blockPrestate_zero (ω : RandomSources ι M) (h : blockStart M blocks rec₀ 0 ω ≠ ⊤) :
    blockPrestate M blocks rec₀ 0 ω = rec₀ :=
  blockPrestate_mem M blocks rec₀ (fun n => {x | n = 0 → x = rec₀}) (fun _ => rfl)
    (fun n _ _ _ _ _ h => absurd h (Nat.succ_ne_zero n)) 0 ω h rfl

/-- **Pathwise invariants along the actual run.** -/
theorem blockPrestate_mem_pathwise
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (ω : RandomSources ι M) (Inv : ℕ → Set Rec)
    (hblock : ∀ n x k, x ∈ Inv n →
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      (blocks n).exit (localState M (blocks n) x k ω) ∈ Inv (n + 1))
    (h₀ : blockStart M blocks rec₀ 0 ω ≠ ⊤ → blockPrestate M blocks rec₀ 0 ω ∈ Inv 0) :
    ∀ n, blockStart M blocks rec₀ n ω ≠ ⊤ → blockPrestate M blocks rec₀ n ω ∈ Inv n := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    intro hn
    obtain ⟨k, hk, hh, he⟩ := prestate_succ_local M blocks rec₀ orderSet auxSet hdisj horders
      haux n ω hn
    have hprev := reached_of_le M blocks rec₀ orderSet auxSet hdisj horders haux ω (n + 1) hn n
      (Nat.le_succ n)
    rw [he]
    exact hblock n _ k (ih hprev) hk hh

/-- **Joint pathwise invariants** (route R2): an invariant `Inv` kept by every block only on
records in a companion set `TV` (e.g. `TrueValues` of `ω`), which every block keeps on `Inv`
records, holds jointly with `TV` along the actual run. -/
theorem blockPrestate_mem_joint
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (ω : RandomSources ι M) (Inv : ℕ → Set Rec) (TV : Set Rec)
    (hblock : ∀ n x k, x ∈ TV → x ∈ Inv n →
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      (blocks n).exit (localState M (blocks n) x k ω) ∈ Inv (n + 1))
    (hTV : ∀ n x k, x ∈ TV → x ∈ Inv n →
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      (blocks n).exit (localState M (blocks n) x k ω) ∈ TV)
    (h₀ : rec₀ ∈ Inv 0) (hTV₀ : rec₀ ∈ TV) :
    ∀ n, blockStart M blocks rec₀ n ω ≠ ⊤ →
      blockPrestate M blocks rec₀ n ω ∈ Inv n ∧ blockPrestate M blocks rec₀ n ω ∈ TV :=
  blockPrestate_mem_pathwise M blocks rec₀ orderSet auxSet hdisj horders haux ω
    (fun n => {x | x ∈ Inv n ∧ x ∈ TV})
    (fun n x k hx hk hh => ⟨hblock n x k hx.2 hx.1 hk hh, hTV n x k hx.2 hx.1 hk hh⟩)
    (fun h0 => by rw [blockPrestate_zero M blocks rec₀ ω h0]; exact ⟨h₀, hTV₀⟩)

end AndersonAC.AgentS78
