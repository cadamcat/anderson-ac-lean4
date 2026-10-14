import AndersonAC.AgentS78.Construction.MarkingRule

/-!
# WP10 construction, C5a glue: read patterns are unqueried when a block starts

02-state.tex:96–113 (at a coupled site the remaining true suffix is unqueried; a pending
mark is conservative) and 05-local-sweeps.tex:470–496 ("ordinary trials preserve the
invariant at every coupled site"). For the block run: the committed record declares a set
`freshSet x` of sign coordinates it claims unqueried (e.g. the true suffixes of the
coupled active sites from their prefix lengths, and the auxiliary signs of later blocks).
If every block, run from `x` until it halts, queries no sign of the declared set of its
exit record and only shrinks the declared set, then at every block start no declared sign
has been queried (`declared_unqueried`); orders of block `n` are unexposed because
earlier blocks use disjoint order indices. Together: the `fresh` field of `BlockRun`
(`fresh_of_declared`), pathwise.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources Query Answer querySigns queriedSigns orderCount SignIndex)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
variable (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (orderSet auxSet : ℕ → Set ℕ)

/-- If block `n+1` is reached, block `n` halted: its entering time, record and first
halting local step. -/
theorem halting_step
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    {n s : ℕ} {x : Rec} {ω : RandomSources ι M}
    (hE : BlocksProof.Entered M blocks rec₀ orderSet auxSet n s x ω)
    (h : blockStart M blocks rec₀ (n + 1) ω ≠ ⊤) :
    ∃ k, (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) ∧
      (blocks n).halted (localState M (blocks n) x k ω) = true ∧
      blockStart M blocks rec₀ (n + 1) ω = ((s + k + 1 : ℕ) : WithTop ℕ) ∧
      blockPrestate M blocks rec₀ (n + 1) ω = (blocks n).exit (localState M (blocks n) x k ω) := by
  classical
  obtain ⟨s', x', hE'⟩ := BlocksProof.entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet
    hdisj horders haux h
  by_cases hh : ∃ k, (blocks n).halted (localState M (blocks n) x k ω) = true
  · refine ⟨Nat.find hh, fun k' hk' => by simpa using Nat.find_min hh hk', Nat.find_spec hh, ?_⟩
    have hEs := BlocksProof.entered_succ M blocks rec₀ orderSet auxSet hdisj horders haux hE
      (Nat.find hh) (fun k' hk' => by simpa using Nat.find_min hh hk') (Nat.find_spec hh)
    exact ⟨BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet hEs,
      BlocksProof.blockPrestate_eq M blocks rec₀ orderSet auxSet hEs⟩
  · exfalso
    push_neg at hh
    have hall : ∀ k, (blocks n).halted (localState M (blocks n) x k ω) = false :=
      fun k => by simpa using hh k
    have hidx : (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) s' ω).1.1 =
        n + 1 := by rw [hE'.1]
    rcases le_or_gt s s' with hle | hlt
    · have := BlocksProof.seg_index M blocks rec₀ orderSet auxSet hdisj horders hE (s' - s)
        (fun k' _ => hall k')
      rw [Nat.add_sub_cancel' hle] at this
      rw [this] at hidx
      simp at hidx
    · have := hE.2.2 s' hlt
      omega

/-- **Declared-fresh signs are unqueried at every block start.** -/
theorem declared_unqueried
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (freshSet : Rec → Set (SignIndex ι))
    (hblock : ∀ n x k (ω : RandomSources ι M),
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      freshSet ((blocks n).exit (localState M (blocks n) x k ω)) ⊆ freshSet x ∧
      ∀ k' < k, ∀ z ∈ freshSet ((blocks n).exit (localState M (blocks n) x k ω)),
        z ∉ querySigns ι ((blocks n).next (localState M (blocks n) x k' ω)))
    (ω : RandomSources ι M) :
    ∀ n s x, BlocksProof.Entered M blocks rec₀ orderSet auxSet n s x ω →
      ∀ z ∈ freshSet x, z ∉ queriedSigns ι (runQ M blocks rec₀) s ω := by
  intro n
  induction n with
  | zero =>
    intro s x hE z _ hz
    have h0 := BlocksProof.entered_unique M blocks rec₀ orderSet auxSet hE
      (BlocksProof.entered_zero M blocks rec₀ orderSet auxSet ω)
    rw [h0.1] at hz
    simp [queriedSigns] at hz
  | succ n ih =>
    intro s' x' hE' z hz hq
    have hstart' : blockStart M blocks rec₀ (n + 1) ω ≠ ⊤ := by
      rw [BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet hE']; exact WithTop.coe_ne_top
    obtain ⟨q, hq1, -, -, -, -, hstn⟩ :=
      prestate_succ M blocks rec₀ orderSet auxSet hdisj horders haux n ω hstart'
    obtain ⟨s, x, hE⟩ := BlocksProof.entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet
      hdisj horders haux hstn
    obtain ⟨k, hk, hhalt, hst, hpre⟩ :=
      halting_step M blocks rec₀ orderSet auxSet hdisj horders haux hE hstart'
    have hs' : s' = s + k + 1 := by
      have := BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet hE'
      rw [hst] at this
      exact_mod_cast this.symm
    have hx' : x' = (blocks n).exit (localState M (blocks n) x k ω) := by
      rw [← hpre]; exact (BlocksProof.blockPrestate_eq M blocks rec₀ orderSet auxSet hE').symm
    rw [hx'] at hz
    obtain ⟨hsub, hnot⟩ := hblock n x k ω hk hhalt
    -- a queried sign before s' was queried before s or in block n
    simp only [queriedSigns, Set.mem_iUnion, Finset.mem_range] at hq
    obtain ⟨j, hj, hzj⟩ := hq
    rw [hs'] at hj
    rcases lt_or_ge j s with hjs | hjs
    · exact ih s x hE z (hsub hz) (by
        simp only [queriedSigns, Set.mem_iUnion, Finset.mem_range]; exact ⟨j, hjs, hzj⟩)
    · obtain ⟨k', rfl⟩ : ∃ k', j = s + k' := ⟨j - s, by omega⟩
      have hk'le : k' ≤ k := by omega
      have hidx := BlocksProof.seg_index M blocks rec₀ orderSet auxSet hdisj horders hE k'
        (fun k'' hk'' => hk k'' (by omega))
      have hQ : runQ M blocks rec₀ (s + k') ω =
          gnext blocks (n, x, localState M (blocks n) x k' ω) := by
        rw [BlocksProof.runQ_eq, hidx]
      rw [hQ] at hzj
      rcases lt_or_eq_of_le hk'le with hlt | rfl
      · rw [gnext, if_neg (by rw [hk k' hlt]; decide)] at hzj
        exact hnot k' hlt z hz hzj
      · rw [gnext, if_pos (by exact hhalt)] at hzj
        simp [querySigns] at hzj

/-- **The `fresh` field of `BlockRun`**, pathwise: the read pattern of block `n` is
unqueried at its start. -/
theorem fresh_of_declared
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (freshSet : Rec → Set (SignIndex ι))
    (hblock : ∀ n x k (ω : RandomSources ι M),
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      freshSet ((blocks n).exit (localState M (blocks n) x k ω)) ⊆ freshSet x ∧
      ∀ k' < k, ∀ z ∈ freshSet ((blocks n).exit (localState M (blocks n) x k ω)),
        z ∉ querySigns ι ((blocks n).next (localState M (blocks n) x k' ω)))
    (pattern : ℕ → Rec → FreshPattern ι)
    (hpat : ∀ n x, (pattern n x).signs ⊆ freshSet x ∧ ∀ o ∈ (pattern n x).orders, o ∈ orderSet n)
    (n : ℕ) (ω : RandomSources ι M) (hn : blockStart M blocks rec₀ n ω ≠ ⊤) :
    UnqueriedAt ι (runQ M blocks rec₀) ((blockStart M blocks rec₀ n ω).untopD 0)
      (pattern n (blockPrestate M blocks rec₀ n ω)) ω := by
  classical
  obtain ⟨s, x, hE⟩ := BlocksProof.entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet
    hdisj horders haux hn
  rw [BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet hE,
    BlocksProof.blockPrestate_eq M blocks rec₀ orderSet auxSet hE]
  refine ⟨fun z hz => declared_unqueried M blocks rec₀ orderSet auxSet hdisj horders haux
    freshSet hblock ω n s x hE z ((hpat n x).1 hz), fun o ho => ?_⟩
  -- earlier blocks use other order indices
  unfold orderCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj hQj
  have hmem : runQ M blocks rec₀ j ω ∈
      (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) s ω).2 := by
    rw [BlocksProof.global_list]
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr (Finset.mem_range.mp hj), rfl⟩
  obtain ⟨n', hn', ho'⟩ := (hE.2.1 _ hmem).1 o hQj
  exact Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hn')) ho' ((hpat n x).2 o ho)

/-- An auxiliary sign of block `n` is unqueried when block `n` starts: earlier blocks query
only auxiliary signs of their own, disjoint, index sets. -/
theorem aux_unqueried
    (hauxdisj : Pairwise fun n n' => Disjoint (auxSet n) (auxSet n'))
    {n s : ℕ} {x : Rec} {ω : RandomSources ι M}
    (hE : BlocksProof.Entered M blocks rec₀ orderSet auxSet n s x ω)
    (a : ℕ) (ha : a ∈ auxSet n) :
    (Sum.inr a : SignIndex ι) ∉ queriedSigns ι (runQ M blocks rec₀) s ω := by
  intro hq
  simp only [queriedSigns, Set.mem_iUnion, Finset.mem_range] at hq
  obtain ⟨j, hj, hz⟩ := hq
  have hQa : runQ M blocks rec₀ j ω = Query.auxiliary a := by
    cases hc : runQ M blocks rec₀ j ω with
    | trueDigit i k => rw [hc] at hz; simp [querySigns] at hz
    | auxiliary k => rw [hc] at hz; simp [querySigns] at hz; rw [hz]
    | trueSuffix i h => rw [hc] at hz; simp [querySigns] at hz
    | nextOrder o => rw [hc] at hz; simp [querySigns] at hz
    | decision => rw [hc] at hz; simp [querySigns] at hz
  have hmem : runQ M blocks rec₀ j ω ∈
      (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) s ω).2 := by
    rw [BlocksProof.global_list]
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  obtain ⟨n', hn', ha'⟩ := (hE.2.1 _ hmem).2 a hQa
  exact Set.disjoint_left.mp (hauxdisj (Nat.ne_of_lt hn')) ha' ha

/-- **The `fresh` field of `BlockRun`, with auxiliary signs by index sets.** The declared
set only needs to cover the true signs of the pattern; its auxiliary signs lie in the
block's own `auxSet`. -/
theorem fresh_of_declared_aux
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (hauxdisj : Pairwise fun n n' => Disjoint (auxSet n) (auxSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (freshSet : Rec → Set (SignIndex ι))
    (hblock : ∀ n x k (ω : RandomSources ι M),
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      freshSet ((blocks n).exit (localState M (blocks n) x k ω)) ⊆ freshSet x ∧
      ∀ k' < k, ∀ z ∈ freshSet ((blocks n).exit (localState M (blocks n) x k ω)),
        z ∉ querySigns ι ((blocks n).next (localState M (blocks n) x k' ω)))
    (pattern : ℕ → Rec → FreshPattern ι)
    (hpat : ∀ n x, (∀ z ∈ (pattern n x).signs, z ∈ freshSet x ∨ ∃ a ∈ auxSet n, z = Sum.inr a) ∧
      ∀ o ∈ (pattern n x).orders, o ∈ orderSet n)
    (n : ℕ) (ω : RandomSources ι M) (hn : blockStart M blocks rec₀ n ω ≠ ⊤) :
    UnqueriedAt ι (runQ M blocks rec₀) ((blockStart M blocks rec₀ n ω).untopD 0)
      (pattern n (blockPrestate M blocks rec₀ n ω)) ω := by
  classical
  obtain ⟨s, x, hE⟩ := BlocksProof.entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet
    hdisj horders haux hn
  rw [BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet hE,
    BlocksProof.blockPrestate_eq M blocks rec₀ orderSet auxSet hE]
  refine ⟨fun z hz => ?_, fun o ho => ?_⟩
  · rcases (hpat n x).1 z hz with hf | ⟨a, ha, rfl⟩
    · exact declared_unqueried M blocks rec₀ orderSet auxSet hdisj horders haux
        freshSet hblock ω n s x hE z hf
    · exact aux_unqueried M blocks rec₀ orderSet auxSet hauxdisj hE a ha
  · unfold orderCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hQj
    have hmem : runQ M blocks rec₀ j ω ∈
        (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) s ω).2 := by
      rw [BlocksProof.global_list]
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr (Finset.mem_range.mp hj), rfl⟩
    obtain ⟨n', hn', ho'⟩ := (hE.2.1 _ hmem).1 o hQj
    exact Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hn')) ho' ((hpat n x).2 o ho)

end AndersonAC.AgentS78
