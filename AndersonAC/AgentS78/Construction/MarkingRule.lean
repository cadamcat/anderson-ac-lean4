import AndersonAC.AgentS78.Construction.BlocksProof
import AndersonAC.AgentS78.Construction.Invariant
import AndersonAC.S78.Definitions

/-!
# WP10 construction, C5c: the marking rule along the block run

08-history.tex:44–50 and 02-state.tex:107–113: a site pending after a run of blocks either
was pending before them with the same latest label, or it was (re)marked by one of them,
whose first trial failed; it then carries that block's label. `marking_along_run` proves
this pathwise for the composed run from the per-block marking discipline
(`hblock`, stated on the halting states reachable from the entering record). With
`a, b` = the first blocks of stages `j` and `j+1` it is the status rule `step` of
`BlockRun` (births are global first failures, equal to the block-local ones by
`blockComposition_proof`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources Query Answer)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}

/-- Block-local states before halting are reachable states of the block. -/
theorem localState_reach (B : Block ι Rec St) (x : Rec) (ω : RandomSources ι M) :
    ∀ k, (∀ k' < k, B.halted (localState M B x k' ω) = false) →
      BlockReach B x (localState M B x k ω) := by
  intro k
  induction k with
  | zero => intro _; exact BlockReach.enter
  | succ k ih =>
    intro hk
    have h1 := ih (fun k' hk' => hk k' (Nat.lt_succ_of_lt hk'))
    exact BlockReach.step _ _ h1 (hk k (Nat.lt_succ_self k))

variable (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (orderSet auxSet : ℕ → Set ℕ)

/-- **Consecutive entering records.** If block `n+1` is reached, block `n` was reached and
halted at a reachable state whose exit record enters block `n+1`. -/
theorem prestate_succ
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (n : ℕ) (ω : RandomSources ι M) (h : blockStart M blocks rec₀ (n + 1) ω ≠ ⊤) :
    ∃ q, (runState M blocks rec₀ q ω).1 = n ∧
      (runState M blocks rec₀ q ω).2.1 = blockPrestate M blocks rec₀ n ω ∧
      (blocks n).halted (runState M blocks rec₀ q ω).2.2 = true ∧
      blockPrestate M blocks rec₀ (n + 1) ω = (blocks n).exit (runState M blocks rec₀ q ω).2.2 ∧
      BlockReach (blocks n) (blockPrestate M blocks rec₀ n ω) (runState M blocks rec₀ q ω).2.2 ∧
      blockStart M blocks rec₀ n ω ≠ ⊤ := by
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
  refine ⟨q, by rw [hrs], by rw [hrs, hpre], by rw [hrs]; exact hhalt, ?_, ?_, ?_⟩
  · rw [hrs, hpre', hx']
  · rw [hrs, hpre]; exact localState_reach M (blocks n₁) x ω (q - s) hrun
  · rw [BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet hE]; exact WithTop.coe_ne_top

/-- **Marking rule along the run.** -/
theorem marking_along_run {α L : Type}
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (pend : Rec → Set α) (lab : Rec → α → L) (label : ℕ → L) (extra : ℕ → α → Prop)
    (hblock : ∀ n x s, BlockReach (blocks n) x s → (blocks n).halted s = true →
      ∀ y ∈ pend ((blocks n).exit s),
        (y ∈ pend x ∧ lab ((blocks n).exit s) y = lab x y) ∨
        (lab ((blocks n).exit s) y = label n ∧ (blocks n).firstFail s = true ∧ extra n y))
    (a : ℕ) (ω : RandomSources ι M) :
    ∀ b, a ≤ b → blockStart M blocks rec₀ b ω ≠ ⊤ →
      ∀ y ∈ pend (blockPrestate M blocks rec₀ b ω),
        (y ∈ pend (blockPrestate M blocks rec₀ a ω) ∧
          lab (blockPrestate M blocks rec₀ b ω) y = lab (blockPrestate M blocks rec₀ a ω) y) ∨
        ∃ n, a ≤ n ∧ n < b ∧ lab (blockPrestate M blocks rec₀ b ω) y = label n ∧
          blockStart M blocks rec₀ n ω ≠ ⊤ ∧ ω ∈ globalFirstFail M blocks rec₀ n ∧
          extra n y := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _ y hy; exact Or.inl ⟨hy, rfl⟩
  | succ b hab ih =>
    intro hb y hy
    obtain ⟨q, hq1, hq2, hhalt, hexit, hreach, hbn⟩ :=
      prestate_succ M blocks rec₀ orderSet auxSet hdisj horders haux b ω hb
    rw [hexit] at hy ⊢
    rcases hblock b _ _ hreach hhalt y hy with ⟨hy', hl⟩ | ⟨hl, hff, hex⟩
    · rcases ih hbn y hy' with ⟨h1, h2⟩ | ⟨n, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨h1, hl.trans h2⟩
      · exact Or.inr ⟨n, h1, Nat.lt_succ_of_lt h2, hl.trans h3, h4, h5, h6⟩
    · exact Or.inr ⟨b, hab, Nat.lt_succ_self b, hl, hbn, ⟨q, hq1, hff⟩, hex⟩

open AndersonAC.S78 in
/-- **The status rule `step` of `BlockRun`** from the per-block marking discipline.
`e j` is the first block of stage `j+1` (so `pending j` is read at the end of stage `j`),
`label n` the birth label of block `n` (`slot (label n) = n` for marking blocks, scale
`j+1` inside stage `j+1`), and `hloc` is the localization clause of
`blockComposition_proof`. -/
theorem step_of_marking {d m : ℕ} (blocks : ℕ → Block (Torus d m) Rec St) (rec₀ : Rec)
    (orderSet auxSet : ℕ → Set ℕ) (M : ℕ → ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (pend : Rec → Finset (Torus d m)) (lab : Rec → Torus d m → BirthLabel (Torus d m))
    (label : ℕ → BirthLabel (Torus d m)) (slot : BirthLabel (Torus d m) → ℕ) (Ch : ℝ)
    (e : ℕ → ℕ) (n₀ : ℕ) (he : ∀ j, e j ≤ e (j + 1))
    (hslot : ∀ j n, n₀ ≤ j → e j ≤ n → n < e (j + 1) → (label n).scale = j + 1)
    (hblock : ∀ n x s, BlockReach (blocks n) x s → (blocks n).halted s = true →
      ∀ y ∈ pend ((blocks n).exit s),
        (y ∈ pend x ∧ lab ((blocks n).exit s) y = lab x y) ∨
        (lab ((blocks n).exit s) y = label n ∧ (blocks n).firstFail s = true ∧
          (physicalDistance d m y (label n).anchor ≤
            Ch * (4 : ℝ) ^ ((8 + nu d) * ((label n).scale : ℝ)) ∧ slot (label n) = n)))
    (hloc : ∀ n ω, blockStart M blocks rec₀ n ω ≠ ⊤ →
      (ω ∈ globalFirstFail M blocks rec₀ n ↔
        ω ∈ localFirstFail M (blocks n) (blockPrestate M blocks rec₀ n ω))) :
    let pending := fun j (x : Torus d m) => {ω : RandomSources (Torus d m) M |
      blockStart M blocks rec₀ (e j) ω ≠ ⊤ ∧ x ∈ pend (blockPrestate M blocks rec₀ (e j) ω)}
    let latest := fun j (x : Torus d m) (ω : RandomSources (Torus d m) M) =>
      lab (blockPrestate M blocks rec₀ (e j) ω) x
    ∀ j x ω, n₀ ≤ j → ω ∈ pending (j + 1) x →
      (ω ∈ pending j x ∧ latest (j + 1) x ω = latest j x ω) ∨
      ((latest (j + 1) x ω).scale = j + 1 ∧
        (blockStart M blocks rec₀ (slot (latest (j + 1) x ω)) ω ≠ ⊤ ∧
          ω ∈ localFirstFail M (blocks (slot (latest (j + 1) x ω)))
            (blockPrestate M blocks rec₀ (slot (latest (j + 1) x ω)) ω)) ∧
        physicalDistance d m x (latest (j + 1) x ω).anchor ≤
          Ch * (4 : ℝ) ^ ((8 + nu d) * (((j + 1 : ℕ) : ℝ)))) := by
  intro pending latest j x ω hj hω
  obtain ⟨hstart, hx⟩ := hω
  -- strengthen the per-block rule with the distance, then run `marking_along_run`
  have hmark := marking_along_run M blocks rec₀ orderSet auxSet hdisj horders haux
    (fun r => {y | y ∈ pend r}) lab label
    (fun n y => physicalDistance d m y (label n).anchor ≤
      Ch * (4 : ℝ) ^ ((8 + nu d) * ((label n).scale : ℝ)) ∧ slot (label n) = n)
    hblock (e j) ω (e (j + 1)) (he j) hstart x hx
  rcases hmark with ⟨h1, h2⟩ | ⟨n, hn1, hn2, hlab, hns, hfail, hdist⟩
  · -- untouched: block e j was reached since e j ≤ e (j+1)
    have hej : blockStart M blocks rec₀ (e j) ω ≠ ⊤ := by
      have key : ∀ k, blockStart M blocks rec₀ (e j + k) ω ≠ ⊤ →
          blockStart M blocks rec₀ (e j) ω ≠ ⊤ := by
        intro k
        induction k with
        | zero => exact id
        | succ k ih =>
          intro hk
          obtain ⟨_, -, -, -, -, -, hprev⟩ :=
            prestate_succ M blocks rec₀ orderSet auxSet hdisj horders haux _ ω hk
          exact ih hprev
      have := key (e (j + 1) - e j)
      rw [Nat.add_sub_cancel' (he j)] at this
      exact this hstart
    exact Or.inl ⟨⟨hej, h1⟩, h2⟩
  · obtain ⟨hdist, hsl⟩ := hdist
    have hsc := hslot j n hj hn1 hn2
    refine Or.inr ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · show (lab _ x).scale = j + 1
      rw [hlab, hsc]
    · show blockStart M blocks rec₀ (slot (lab _ x)) ω ≠ ⊤
      rw [hlab, hsl]; exact hns
    · show ω ∈ localFirstFail M (blocks (slot (lab _ x))) (blockPrestate M blocks rec₀ (slot (lab _ x)) ω)
      rw [hlab, hsl]; exact (hloc n ω hns).mp hfail
    · show physicalDistance d m x (lab _ x).anchor ≤ _
      rw [hlab]; rw [hsc] at hdist; exact hdist

end AndersonAC.AgentS78
