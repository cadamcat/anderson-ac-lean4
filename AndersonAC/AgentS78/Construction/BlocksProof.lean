import AndersonAC.AgentS78.Construction.Blocks

/-!
# WP10 random construction, C3c proved: the run as a composition of blocks

`blockComposition_proof : MachineRunStatement → BlockCompositionStatement` (agent-s78blocks).

Route. The global run `machineRun` of `(gInit, gnext, gupdate)` is analysed by the
predicate `Entered n s x ω`: at operation `s` the run enters block `n` with record `x`,
every earlier order query lies in `orderSet n'` and every earlier auxiliary query in
`auxSet n'` for some `n' < n`, and every earlier operation has block index `< n`.
Inside the block (`seg`) the global state is the block-local state and the global query list
is the entering list followed by the local list: sign answers agree trivially and order
answers agree because the entering list contains no order query of `orderSet n`
(disjointness). Every operation lies in some entered block (`cover`), so the block starts
are the hitting times of the (retained-measurable) block index, the entering records are
the stopped values of the adapted state, and the global first failure of block `n` is the
block-local one.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2

namespace BlocksProof

/-! ### Generic facts on explicit machine runs -/

section MachineFacts
variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ)

theorem machineRun_succ {St : Type} (init : St) (next : St → Query ι)
    (update : St → Answer ι → St) (q : ℕ) (ω : RandomSources ι M) :
    machineRun ι M init next update (q + 1) ω =
      (update (machineRun ι M init next update q ω).1
        (localAnswer ι M (machineRun ι M init next update q ω).2
          (next (machineRun ι M init next update q ω).1) ω),
       (machineRun ι M init next update q ω).2 ++
        [next (machineRun ι M init next update q ω).1]) := rfl

theorem machineRun_snd {St : Type} (init : St) (next : St → Query ι)
    (update : St → Answer ι → St) (q : ℕ) (ω : RandomSources ι M) :
    (machineRun ι M init next update q ω).2 =
      (List.range q).map (fun j => machineQ ι M init next update j ω) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [machineRun_succ, List.range_succ, List.map_append, ← ih]
    rfl

theorem localAnswer_append (L L' : List (Query ι)) (c : Query ι) (ω : RandomSources ι M)
    (h : ∀ o, c = Query.nextOrder o → L.count (Query.nextOrder o) = 0) :
    localAnswer ι M (L ++ L') c ω = localAnswer ι M L' c ω := by
  cases c with
  | nextOrder o =>
    have h0 := h o rfl
    simp only [localAnswer, List.count_append, h0, zero_add]
  | trueDigit i k => rfl
  | auxiliary k => rfl
  | trueSuffix i k => rfl
  | decision => rfl

theorem card_filter_range_eq_count {α : Type} [DecidableEq α] (f : ℕ → α) (c : α) (q : ℕ) :
    ((Finset.range q).filter (fun j => f j = c)).card = ((List.range q).map f).count c := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.map_append,
      List.count_append, ← ih]
    by_cases hq : f q = c
    · rw [if_pos hq, Finset.card_insert_of_notMem (by simp)]
      simp [hq]
    · rw [if_neg hq]
      simp [hq]

end MachineFacts

/-! ### Stopped σ-fields for `ℕ`-indexed filtrations -/

section Stopped
variable {Ω : Type} {m : MeasurableSpace Ω} {f : Filtration ℕ m} {τ : Ω → WithTop ℕ}

theorem measurableSet_eq_top_iSup (hτ : IsStoppingTime f τ) :
    MeasurableSet[⨆ t, f t] {ω | τ ω = ⊤} := by
  have h : {ω | τ ω = ⊤} = (⋃ i : ℕ, {ω | τ ω ≤ i})ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    cases τ ω with
    | top => simp
    | coe t => simpa using ⟨t, le_rfl⟩
  rw [h]
  exact (MeasurableSet.iUnion fun i => le_iSup (fun t => f t) i _ (hτ i)).compl

theorem measurableSet_stopped_of (hτ : IsStoppingTime f τ) (S : Set Ω)
    (hfin : ∀ q : ℕ, MeasurableSet[f q] (S ∩ {ω | τ ω = q}))
    (htop : MeasurableSet[⨆ t, f t] (S ∩ {ω | τ ω = ⊤})) :
    MeasurableSet[hτ.measurableSpace] S := by
  have hS : S = (⋃ q : ℕ, S ∩ {ω | τ ω = q}) ∪ (S ∩ {ω | τ ω = ⊤}) := by
    ext ω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      cases hτω : τ ω with
      | top => exact Or.inr ⟨h, rfl⟩
      | coe q => exact Or.inl ⟨q, h, rfl⟩
    · rintro (⟨q, h, _⟩ | ⟨h, _⟩) <;> exact h
  rw [hS]
  refine MeasurableSet.union (MeasurableSet.iUnion fun q => ?_) ?_
  · exact (hτ.measurableSet_inter_eq_iff S q).2 (hfin q)
  · refine ⟨htop, fun i => ?_⟩
    have h0 : S ∩ {ω | τ ω = ⊤} ∩ {ω | τ ω ≤ i} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h1⟩, h2⟩
      rw [h1] at h2
      exact absurd h2 (by simp)
    convert (@MeasurableSet.empty _ (f i)) using 1

end Stopped

/-! ### The composed run -/

section Run
variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
  (blocks : ℕ → Block ι Rec St) (rec₀ : Rec) (orderSet auxSet : ℕ → Set ℕ)

/-- The global run (state and query list). -/
local notation "G" => machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks)


/-- Local order discipline (the hypothesis `_horders` of the frozen statement). -/
def HOrders : Prop :=
  ∀ n x k ω o, (blocks n).halted (localState M (blocks n) x k ω) = false →
    (blocks n).next (localState M (blocks n) x k ω) = Query.nextOrder o →
    o ∈ orderSet n ∧
    ((List.range k).filter fun k' =>
      (blocks n).halted (localState M (blocks n) x k' ω) = false ∧
      (blocks n).next (localState M (blocks n) x k' ω) = Query.nextOrder o).length < M o

/-- Local auxiliary discipline (the hypothesis `_haux` of the frozen statement). -/
def HAux : Prop :=
  ∀ n x k ω a, (blocks n).halted (localState M (blocks n) x k ω) = false →
    (blocks n).next (localState M (blocks n) x k ω) = Query.auxiliary a →
    a ∈ auxSet n ∧ ∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false →
      (blocks n).next (localState M (blocks n) x k' ω) ≠ Query.auxiliary a

/-- The run enters block `n` at operation `s` with record `x`. -/
def Entered (n s : ℕ) (x : Rec) (ω : RandomSources ι M) : Prop :=
  (G s ω).1 = (n, x, (blocks n).enter x) ∧
  (∀ c ∈ (G s ω).2,
    (∀ o, c = Query.nextOrder o → ∃ n' < n, o ∈ orderSet n') ∧
    (∀ a, c = Query.auxiliary a → ∃ n' < n, a ∈ auxSet n')) ∧
  ∀ q < s, (G q ω).1.1 < n

theorem localState_eq (n : ℕ) (x : Rec) (k : ℕ) (ω : RandomSources ι M) :
    localState M (blocks n) x k ω = (machineRun ι M ((blocks n).enter x) (blocks n).next (blocks n).update k ω).1 := rfl

theorem local_list (n : ℕ) (x : Rec) (k : ℕ) (ω : RandomSources ι M) :
    (machineRun ι M ((blocks n).enter x) (blocks n).next (blocks n).update k ω).2 = (List.range k).map (fun j => (blocks n).next (localState M (blocks n) x j ω)) :=
  machineRun_snd M _ _ _ k ω

theorem global_list (q : ℕ) (ω : RandomSources ι M) :
    (G q ω).2 = (List.range q).map (fun j => runQ M blocks rec₀ j ω) :=
  machineRun_snd M _ _ _ q ω

theorem runState_eq (q : ℕ) (ω : RandomSources ι M) :
    runState M blocks rec₀ q ω = (G q ω).1 := rfl

theorem runQ_eq (q : ℕ) (ω : RandomSources ι M) :
    runQ M blocks rec₀ q ω = gnext blocks (G q ω).1 := rfl

theorem gnext_of_not_halted (g : GState Rec St) (h : (blocks g.1).halted g.2.2 = false) :
    gnext blocks g = (blocks g.1).next g.2.2 := by
  simp [gnext, h]

theorem gnext_of_halted (g : GState Rec St) (h : (blocks g.1).halted g.2.2 = true) :
    gnext blocks g = Query.decision := by
  simp [gnext, h]

theorem gupdate_of_not_halted (g : GState Rec St) (a : Answer ι)
    (h : (blocks g.1).halted g.2.2 = false) :
    gupdate blocks g a = (g.1, g.2.1, (blocks g.1).update g.2.2 a) := by
  simp [gupdate, h]

theorem gupdate_of_halted (g : GState Rec St) (a : Answer ι)
    (h : (blocks g.1).halted g.2.2 = true) :
    gupdate blocks g a = (g.1 + 1, (blocks g.1).exit g.2.2,
      (blocks (g.1 + 1)).enter ((blocks g.1).exit g.2.2)) := by
  simp [gupdate, h]

/-- The block index grows by at most one per operation. -/
theorem index_succ (q : ℕ) (ω : RandomSources ι M) :
    (G (q + 1) ω).1.1 = (G q ω).1.1 ∨ (G (q + 1) ω).1.1 = (G q ω).1.1 + 1 := by
  rw [machineRun_succ]
  cases h : (blocks (G q ω).1.1).halted (G q ω).1.2.2
  · left; rw [gupdate_of_not_halted blocks _ _ h]
  · right; rw [gupdate_of_halted blocks _ _ h]

theorem index_mono (ω : RandomSources ι M) : Monotone fun q => (G q ω).1.1 := by
  refine monotone_nat_of_le_succ fun q => ?_
  rcases index_succ M blocks rec₀ q ω with h | h <;> simp only [h] <;> omega

theorem index_zero (ω : RandomSources ι M) : (G 0 ω).1.1 = 0 := rfl

/-- Inside an entered block, the global run is the block-local run. -/
theorem seg (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : HOrders M blocks orderSet) {n s : ℕ} {x : Rec} {ω : RandomSources ι M}
    (hE : Entered M blocks rec₀ orderSet auxSet n s x ω) :
    ∀ k, (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      G (s + k) ω = ((n, x, localState M (blocks n) x k ω), (G s ω).2 ++ (machineRun ι M ((blocks n).enter x) (blocks n).next (blocks n).update k ω).2) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Prod.ext_iff]
    exact ⟨hE.1, by simp [machineRun]⟩
  | succ k ih =>
    intro hk
    have ih' := ih (fun k' hk' => hk k' (by omega))
    have hk0 : (blocks n).halted (localState M (blocks n) x k ω) = false := hk k (by omega)
    have hcount : ∀ o, (blocks n).next (localState M (blocks n) x k ω) = Query.nextOrder o →
        (G s ω).2.count (Query.nextOrder o) = 0 := by
      intro o ho
      have hon := (horders n x k ω o hk0 ho).1
      refine List.count_eq_zero.2 fun hmem => ?_
      obtain ⟨n', hn', ho'⟩ := (hE.2.1 _ hmem).1 o rfl
      exact Set.disjoint_left.1 (hdisj hn'.ne) ho' hon
    show G ((s + k) + 1) ω = _
    rw [machineRun_succ, ih']
    have hg : (blocks (n, x, localState M (blocks n) x k ω).1).halted
        (n, x, localState M (blocks n) x k ω).2.2 = false := hk0
    rw [gnext_of_not_halted blocks _ hg, gupdate_of_not_halted blocks _ _ hg,
      localAnswer_append M _ _ _ ω hcount]
    rw [machineRun_succ (init := (blocks n).enter x), List.append_assoc]
    rfl

/-- The index at an operation inside an entered block. -/
theorem seg_index (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : HOrders M blocks orderSet) {n s : ℕ} {x : Rec} {ω : RandomSources ι M}
    (hE : Entered M blocks rec₀ orderSet auxSet n s x ω) (k : ℕ)
    (hk : ∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) :
    (G (s + k) ω).1 = (n, x, localState M (blocks n) x k ω) := by
  rw [seg M blocks rec₀ orderSet auxSet hdisj horders hE k hk]

/-- Entering the next block when block `n` halts. -/
theorem entered_succ (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : HOrders M blocks orderSet) (haux : HAux M blocks auxSet)
    {n s : ℕ} {x : Rec} {ω : RandomSources ι M}
    (hE : Entered M blocks rec₀ orderSet auxSet n s x ω) (k : ℕ)
    (hk : ∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false)
    (hh : (blocks n).halted (localState M (blocks n) x k ω) = true) :
    Entered M blocks rec₀ orderSet auxSet (n + 1) (s + k + 1)
      ((blocks n).exit (localState M (blocks n) x k ω)) ω := by
  have hseg := seg M blocks rec₀ orderSet auxSet hdisj horders hE k hk
  have hg : (blocks (n, x, localState M (blocks n) x k ω).1).halted
      (n, x, localState M (blocks n) x k ω).2.2 = true := hh
  have hrun : G (s + k + 1) ω =
      ((n + 1, (blocks n).exit (localState M (blocks n) x k ω),
        (blocks (n + 1)).enter ((blocks n).exit (localState M (blocks n) x k ω))),
       (G s ω).2 ++ (machineRun ι M ((blocks n).enter x) (blocks n).next (blocks n).update k ω).2 ++ [Query.decision]) := by
    rw [machineRun_succ, hseg, gnext_of_halted blocks _ hg, gupdate_of_halted blocks _ _ hg]
  refine ⟨by rw [hrun], ?_, ?_⟩
  · intro c hc
    rw [hrun] at hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨h1, h2⟩ := hE.2.1 c hc
      exact ⟨fun o ho => by obtain ⟨n', hn', h⟩ := h1 o ho; exact ⟨n', by omega, h⟩,
        fun a ha => by obtain ⟨n', hn', h⟩ := h2 a ha; exact ⟨n', by omega, h⟩⟩
    · rw [local_list] at hc
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
      have hj' : j < k := List.mem_range.1 hj
      refine ⟨fun o ho => ⟨n, by omega, (horders n x j ω o (hk j hj') ho).1⟩,
        fun a ha => ⟨n, by omega, (haux n x j ω a (hk j hj') ha).1⟩⟩
    · subst hc
      exact ⟨fun o ho => (nomatch ho), fun a ha => (nomatch ha)⟩
  · intro q hq
    by_cases hqs : q < s
    · have := hE.2.2 q hqs
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, q = s + j := ⟨q - s, by omega⟩
      rw [seg_index M blocks rec₀ orderSet auxSet hdisj horders hE j
        (fun k' hk' => hk k' (by omega))]
      simp

/-- The initial block is entered at time `0`. -/
theorem entered_zero (ω : RandomSources ι M) :
    Entered M blocks rec₀ orderSet auxSet 0 0 rec₀ ω :=
  ⟨rfl, fun c hc => by simp [machineRun] at hc, fun q hq => absurd hq (Nat.not_lt_zero q)⟩

/-- Every operation lies in an entered block. -/
theorem cover (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : HOrders M blocks orderSet) (haux : HAux M blocks auxSet)
    (ω : RandomSources ι M) (q : ℕ) :
    ∃ n s x, s ≤ q ∧ Entered M blocks rec₀ orderSet auxSet n s x ω ∧
      ∀ k' < q - s, (blocks n).halted (localState M (blocks n) x k' ω) = false := by
  induction q with
  | zero => exact ⟨0, 0, rec₀, le_rfl, entered_zero M blocks rec₀ orderSet auxSet ω,
      fun k' hk' => absurd hk' (Nat.not_lt_zero k')⟩
  | succ q ih =>
    obtain ⟨n, s, x, hsq, hE, hk⟩ := ih
    cases hh : (blocks n).halted (localState M (blocks n) x (q - s) ω)
    · refine ⟨n, s, x, by omega, hE, fun k' hk' => ?_⟩
      rcases Nat.lt_or_ge k' (q - s) with h | h
      · exact hk k' h
      · obtain rfl : k' = q - s := by omega
        exact hh
    · have hE' := entered_succ M blocks rec₀ orderSet auxSet hdisj horders haux hE (q - s) hk hh
      refine ⟨n + 1, s + (q - s) + 1, _, by omega, hE', fun k' hk' => ?_⟩
      omega

/-- The entering time and record of a block are unique. -/
theorem entered_unique {n s s' : ℕ} {x x' : Rec} {ω : RandomSources ι M}
    (hE : Entered M blocks rec₀ orderSet auxSet n s x ω)
    (hE' : Entered M blocks rec₀ orderSet auxSet n s' x' ω) : s = s' ∧ x = x' := by
  have hs : s = s' := by
    rcases lt_trichotomy s s' with h | h | h
    · have h1 := hE'.2.2 s h
      rw [hE.1] at h1
      exact absurd h1 (lt_irrefl _)
    · exact h
    · have h1 := hE.2.2 s' h
      rw [hE'.1] at h1
      exact absurd h1 (lt_irrefl _)
  subst hs
  have h := hE.1.symm.trans hE'.1
  simp only [Prod.mk.injEq] at h
  exact ⟨rfl, h.2.1⟩

/-- Where the run is at operation `q`: inside the block it last entered. -/
theorem at_time (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : HOrders M blocks orderSet) (haux : HAux M blocks auxSet)
    (ω : RandomSources ι M) (q : ℕ) :
    ∃ n s x, s ≤ q ∧ Entered M blocks rec₀ orderSet auxSet n s x ω ∧
      (∀ k' < q - s, (blocks n).halted (localState M (blocks n) x k' ω) = false) ∧
      G q ω = ((n, x, localState M (blocks n) x (q - s) ω), (G s ω).2 ++ (machineRun ι M ((blocks n).enter x) (blocks n).next (blocks n).update (q - s) ω).2) := by
  obtain ⟨n, s, x, hsq, hE, hk⟩ := cover M blocks rec₀ orderSet auxSet hdisj horders haux ω q
  refine ⟨n, s, x, hsq, hE, hk, ?_⟩
  have := seg M blocks rec₀ orderSet auxSet hdisj horders hE (q - s) hk
  rwa [Nat.add_sub_cancel' hsq] at this

theorem blockStart_le_iff (n : ℕ) (ω : RandomSources ι M) (i : ℕ) :
    blockStart M blocks rec₀ n ω ≤ (i : WithTop ℕ) ↔ ∃ q ≤ i, (G q ω).1.1 = n := by
  classical
  unfold blockStart
  by_cases h : ∃ q, (runState M blocks rec₀ q ω).1 = n
  · rw [dif_pos h]
    norm_cast
    rw [Nat.find_le_iff]
    rfl
  · rw [dif_neg h]
    constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨q, _, hq⟩
      exact absurd ⟨q, hq⟩ h

theorem blockStart_eq {n s : ℕ} {x : Rec} {ω : RandomSources ι M}
    (hE : Entered M blocks rec₀ orderSet auxSet n s x ω) :
    blockStart M blocks rec₀ n ω = s := by
  classical
  have h : ∃ q, (runState M blocks rec₀ q ω).1 = n := ⟨s, by rw [runState_eq, hE.1]⟩
  unfold blockStart
  rw [dif_pos h]
  norm_cast
  rw [Nat.find_eq_iff]
  refine ⟨by rw [runState_eq, hE.1], fun q hq h' => ?_⟩
  have := hE.2.2 q hq
  rw [runState_eq] at h'
  omega

theorem blockPrestate_eq {n s : ℕ} {x : Rec} {ω : RandomSources ι M}
    (hE : Entered M blocks rec₀ orderSet auxSet n s x ω) :
    blockPrestate M blocks rec₀ n ω = x := by
  unfold blockPrestate
  rw [blockStart_eq M blocks rec₀ orderSet auxSet hE]
  show (runState M blocks rec₀ s ω).2.1 = x
  rw [runState_eq, hE.1]

theorem blockPrestate_of_eq {n q : ℕ} {ω : RandomSources ι M}
    (h : blockStart M blocks rec₀ n ω = (q : WithTop ℕ)) :
    blockPrestate M blocks rec₀ n ω = (G q ω).1.2.1 := by
  unfold blockPrestate
  rw [h]
  rfl

theorem blockPrestate_of_top {n : ℕ} {ω : RandomSources ι M}
    (h : blockStart M blocks rec₀ n ω = ⊤) :
    blockPrestate M blocks rec₀ n ω = (G 0 ω).1.2.1 := by
  unfold blockPrestate
  rw [h]
  rfl

theorem entered_of_blockStart_ne_top
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : HOrders M blocks orderSet) (haux : HAux M blocks auxSet)
    {n : ℕ} {ω : RandomSources ι M} (h : blockStart M blocks rec₀ n ω ≠ ⊤) :
    ∃ s x, Entered M blocks rec₀ orderSet auxSet n s x ω := by
  classical
  have hex : ∃ q, (runState M blocks rec₀ q ω).1 = n := by
    by_contra hne
    apply h
    unfold blockStart
    rw [dif_neg hne]
  obtain ⟨q, hq⟩ := hex
  obtain ⟨n', s, x, _, hE, _, hG⟩ := at_time M blocks rec₀ orderSet auxSet hdisj horders haux ω q
  rw [runState_eq, hG] at hq
  subst hq
  exact ⟨s, x, hE⟩

end Run

/-! ### Measurability of the composed machine -/

section Meas
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Rec St : Type} [MeasurableSpace Rec]
  [MeasurableSpace St] (blocks : ℕ → Block ι Rec St)

theorem measurable_gnext (hmeas : ∀ n, (blocks n).IsMeasurable) : Measurable (gnext blocks) := by
  refine measurable_from_prod_countable_right fun n => ?_
  show Measurable fun y : Rec × St =>
    if (blocks n).halted y.2 = true then Query.decision else (blocks n).next y.2
  refine Measurable.ite ?_ measurable_const ((hmeas n).next.comp measurable_snd)
  exact (hmeas n).halted.comp measurable_snd (measurableSet_singleton true)

theorem measurable_gupdate (hmeas : ∀ n, (blocks n).IsMeasurable) :
    Measurable (fun p : GState Rec St × Answer ι => gupdate blocks p.1 p.2) := by
  have hF : Measurable (fun z : ℕ × ((Rec × St) × Answer ι) =>
      gupdate blocks (z.1, z.2.1) z.2.2) := by
    refine measurable_from_prod_countable_right fun n => ?_
    show Measurable fun y : (Rec × St) × Answer ι =>
      if (blocks n).halted y.1.2 = true then
        (n + 1, (blocks n).exit y.1.2, (blocks (n + 1)).enter ((blocks n).exit y.1.2))
      else (n, y.1.1, (blocks n).update y.1.2 y.2)
    have hex : Measurable fun y : (Rec × St) × Answer ι => (blocks n).exit y.1.2 :=
      (hmeas n).exit.comp measurable_fst.snd
    refine Measurable.ite ?_ ?_ ?_
    · exact (hmeas n).halted.comp measurable_fst.snd (measurableSet_singleton true)
    · exact measurable_const.prodMk (hex.prodMk ((hmeas (n + 1)).enter.comp hex))
    · exact measurable_const.prodMk (measurable_fst.fst.prodMk
        ((hmeas n).update.comp (measurable_fst.snd.prodMk measurable_snd)))
  exact hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

end Meas

end BlocksProof

open BlocksProof in
/-- **C3c proved.** Composition of blocks: the skeleton of a `QueryRun`, from the explicit
machine-run contract `MachineRunStatement`. -/
theorem blockComposition_proof (hrun : MachineRunStatement) : BlockCompositionStatement := by
  intro ι _ _ M Rec St _ _ blocks rec₀ hmeas orderSet hdisj auxSet hauxdisj horders haux
  have horders' : HOrders M blocks orderSet := horders
  have haux' : HAux M blocks auxSet := haux
  have hstate : ∀ q, Measurable[retained ι (runQ M blocks rec₀) q]
      (runState M blocks rec₀ q) :=
    fun q => (hrun ι M (GState Rec St) (gnext blocks) (measurable_gnext blocks hmeas)
      (gupdate blocks) (measurable_gupdate blocks hmeas)).2.1 (gInit blocks rec₀) q
  -- a running block is not halted when it issues a non-decision query
  have hnothalt : ∀ (n : ℕ) (x : Rec) (k : ℕ) (ω : RandomSources ι M) (c : Query ι),
      c ≠ Query.decision →
      gnext blocks (n, x, localState M (blocks n) x k ω) = c →
      (blocks n).halted (localState M (blocks n) x k ω) = false := by
    intro n x k ω c hc hq
    cases hb : (blocks n).halted (localState M (blocks n) x k ω)
    · rfl
    · rw [gnext_of_halted blocks _ hb] at hq
      exact absurd hq.symm hc
  -- clause 1: admissibility of the global strategy
  have hQ : ObeysQueryRules ι (runQ M blocks rec₀) := by
    refine ⟨fun q => (measurable_gnext blocks hmeas).comp (hstate q), ?_, ?_⟩
    · intro q ω a hq hmem
      simp only [queriedSigns, Set.mem_iUnion, Finset.mem_range] at hmem
      obtain ⟨j, hj, hjmem⟩ := hmem
      have hja : runQ M blocks rec₀ j ω = Query.auxiliary a := by
        revert hjmem
        cases runQ M blocks rec₀ j ω <;> simp [querySigns] <;> exact fun h => h.symm
      have hmemL : Query.auxiliary a ∈
          (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).2 := by
        rw [global_list]
        exact List.mem_map.2 ⟨j, List.mem_range.2 hj, hja⟩
      obtain ⟨n, s, x, _, hE, hk, hG⟩ :=
        at_time M blocks rec₀ orderSet auxSet hdisj horders' haux' ω q
      rw [runQ_eq, hG] at hq
      have hh := hnothalt n x (q - s) ω _ (by simp) hq
      rw [gnext_of_not_halted blocks _ hh] at hq
      obtain ⟨haS, hfresh⟩ := haux' n x (q - s) ω a hh hq
      rw [hG] at hmemL
      rcases List.mem_append.1 hmemL with h1 | h1
      · obtain ⟨n', hn', ha'⟩ := (hE.2.1 _ h1).2 a rfl
        exact Set.disjoint_left.1 (hauxdisj hn'.ne) ha' haS
      · rw [local_list] at h1
        obtain ⟨j', hj', hj'eq⟩ := List.mem_map.1 h1
        have hj'' := List.mem_range.1 hj'
        exact hfresh j' hj'' (hk j' hj'') hj'eq
    · intro q ω o hq
      obtain ⟨n, s, x, _, hE, hk, hG⟩ :=
        at_time M blocks rec₀ orderSet auxSet hdisj horders' haux' ω q
      rw [runQ_eq, hG] at hq
      have hh := hnothalt n x (q - s) ω _ (by simp) hq
      rw [gnext_of_not_halted blocks _ hh] at hq
      obtain ⟨hoS, hbound⟩ := horders' n x (q - s) ω o hh hq
      have h0 : (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) s ω).2.count
          (Query.nextOrder o) = 0 := by
        refine List.count_eq_zero.2 fun hmem => ?_
        obtain ⟨n', hn', ho'⟩ := (hE.2.1 _ hmem).1 o rfl
        exact Set.disjoint_left.1 (hdisj hn'.ne) ho' hoS
      unfold orderCount
      rw [card_filter_range_eq_count (fun j => runQ M blocks rec₀ j ω), ← global_list, hG,
        List.count_append, h0, zero_add, local_list]
      refine lt_of_eq_of_lt ?_ hbound
      rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
      congr 1
      apply List.filter_congr
      intro j hj
      have := hk j (List.mem_range.1 hj)
      simp only [this, Function.comp_apply, true_and]
      exact Bool.beq_eq_decide_eq _ _
  have hidx : ∀ q n, MeasurableSet[retained ι (runQ M blocks rec₀) q]
      {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.1 = n} :=
    fun q n => hstate q (measurable_fst (measurableSet_singleton n))
  -- clause 2: block starts are retained stopping times
  have hstart : ∀ n, IsStoppingTime (retainedFiltration ι hQ) (blockStart M blocks rec₀ n) := by
    intro n i
    show MeasurableSet[retained ι (runQ M blocks rec₀) i]
      {ω | blockStart M blocks rec₀ n ω ≤ (i : WithTop ℕ)}
    have hset : {ω | blockStart M blocks rec₀ n ω ≤ (i : WithTop ℕ)} = ⋃ q ∈ Finset.range (i + 1),
        {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.1 = n} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
      rw [blockStart_le_iff]
      constructor <;> rintro ⟨q, hq, h⟩ <;> exact ⟨q, by omega, h⟩
    rw [hset]
    exact MeasurableSet.biUnion (Finset.countable_toSet _) fun q hq =>
      (retainedFiltration ι hQ).mono (by have := Finset.mem_range.1 hq; omega) _ (hidx q n)
  refine ⟨hQ, hstart, ?_, ?_, ?_, ?_⟩
  -- monotonicity of block starts
  · intro n ω
    by_cases htop : blockStart M blocks rec₀ (n + 1) ω = ⊤
    · rw [htop]
      exact le_top
    obtain ⟨s, x, hE⟩ :=
      entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet hdisj horders' haux' htop
    rw [blockStart_eq M blocks rec₀ orderSet auxSet hE]
    have hs0 : s ≠ 0 := by
      rintro rfl
      have h0 := index_zero M blocks rec₀ ω
      rw [hE.1] at h0
      simp at h0
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have hlt := hE.2.2 t (by omega)
    have hidx' := index_succ M blocks rec₀ t ω
    rw [hE.1] at hidx'
    have ht : (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) t ω).1.1 = n := by
      simp only at hidx'
      omega
    have hle : blockStart M blocks rec₀ n ω ≤ (t : WithTop ℕ) :=
      (blockStart_le_iff M blocks rec₀ n ω t).2 ⟨t, le_rfl, ht⟩
    exact hle.trans (by exact_mod_cast Nat.le_succ t)
  -- the entering record is known at the block start
  · intro n A hA
    refine measurableSet_stopped_of (hstart n) _ (fun q => ?_) ?_
    · have hset : blockPrestate M blocks rec₀ n ⁻¹' A ∩ {ω | blockStart M blocks rec₀ n ω = q} =
          {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.2.1 ∈ A}
            ∩ {ω | blockStart M blocks rec₀ n ω = q} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
        · rwa [← blockPrestate_of_eq M blocks rec₀ h2]
        · rwa [blockPrestate_of_eq M blocks rec₀ h2]
      rw [hset]
      exact (hstate q (measurable_fst.comp measurable_snd hA)).inter
        ((hstart n).measurableSet_eq_of_countable q)
    · have hset : blockPrestate M blocks rec₀ n ⁻¹' A ∩ {ω | blockStart M blocks rec₀ n ω = ⊤} =
          {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) 0 ω).1.2.1 ∈ A}
            ∩ {ω | blockStart M blocks rec₀ n ω = ⊤} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
        · rwa [← blockPrestate_of_top M blocks rec₀ h2]
        · rwa [blockPrestate_of_top M blocks rec₀ h2]
      rw [hset]
      exact (le_iSup (fun t => retainedFiltration ι hQ t) 0 _
        (hstate 0 (measurable_fst.comp measurable_snd hA))).inter
        (measurableSet_eq_top_iSup (hstart n))
  -- localization of the first failure
  · intro n ω hne
    obtain ⟨s, x, hE⟩ :=
      entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet hdisj horders' haux' hne
    rw [blockPrestate_eq M blocks rec₀ orderSet auxSet hE]
    constructor
    · rintro ⟨q, hq1, hq2⟩
      obtain ⟨n', s', x', _, hE', hk, hG⟩ :=
        at_time M blocks rec₀ orderSet auxSet hdisj horders' haux' ω q
      rw [runState_eq, hG] at hq1 hq2
      have hn : n' = n := hq1
      subst hn
      obtain ⟨rfl, rfl⟩ := entered_unique M blocks rec₀ orderSet auxSet hE hE'
      exact ⟨q - s, hk, hq2⟩
    · rintro ⟨k, hk, hff⟩
      refine ⟨s + k, ?_, ?_⟩ <;>
        rw [runState_eq, seg_index M blocks rec₀ orderSet auxSet hdisj horders' hE k hk]
      exact hff
  -- the global first failure is known at the next block start
  · intro n
    have hA : ∀ q, MeasurableSet[retained ι (runQ M blocks rec₀) q]
        {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.1 = n ∧
          (blocks n).firstFail
            (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.2.2 = true} :=
      fun q => hstate q ((measurable_fst (measurableSet_singleton n)).inter
        ((hmeas n).firstFail.comp (measurable_snd.comp measurable_snd)
          (measurableSet_singleton true)))
    have hS : globalFirstFail M blocks rec₀ n ∩ {ω | blockStart M blocks rec₀ n ω ≠ ⊤} =
        ⋃ q, {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.1 = n ∧
          (blocks n).firstFail
            (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks) q ω).1.2.2 = true} := by
      ext ω
      simp only [globalFirstFail, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion,
        runState_eq]
      constructor
      · rintro ⟨h, _⟩
        exact h
      · rintro ⟨q, h1, h2⟩
        refine ⟨⟨q, h1, h2⟩, fun htop => ?_⟩
        have := (blockStart_le_iff M blocks rec₀ n ω q).2 ⟨q, le_rfl, h1⟩
        rw [htop] at this
        exact absurd this (by simp)
    rw [hS]
    refine measurableSet_stopped_of (hstart (n + 1)) _ (fun i => ?_) ?_
    · have hset : (⋃ q, {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks) (gupdate blocks)
            q ω).1.1 = n ∧ (blocks n).firstFail (machineRun ι M (gInit blocks rec₀) (gnext blocks)
              (gupdate blocks) q ω).1.2.2 = true}) ∩
            {ω | blockStart M blocks rec₀ (n + 1) ω = i} =
          (⋃ q ∈ Finset.range i, {ω | (machineRun ι M (gInit blocks rec₀) (gnext blocks)
            (gupdate blocks) q ω).1.1 = n ∧ (blocks n).firstFail (machineRun ι M (gInit blocks rec₀)
              (gnext blocks) (gupdate blocks) q ω).1.2.2 = true}) ∩
            {ω | blockStart M blocks rec₀ (n + 1) ω = i} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range,
          exists_prop]
        constructor
        · rintro ⟨⟨q, h1, h2⟩, hi⟩
          refine ⟨⟨q, ?_, h1, h2⟩, hi⟩
          have hne : blockStart M blocks rec₀ (n + 1) ω ≠ ⊤ := by
            rw [hi]
            exact WithTop.natCast_ne_top i
          obtain ⟨s, x, hE⟩ :=
            entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet hdisj horders' haux' hne
          rw [blockStart_eq M blocks rec₀ orderSet auxSet hE] at hi
          have hsi : s = i := by exact_mod_cast hi
          subst hsi
          by_contra hcon
          have hmono := index_mono M blocks rec₀ ω (not_lt.1 hcon)
          simp only [hE.1, h1] at hmono
          omega
        · rintro ⟨⟨q, _, h1, h2⟩, hi⟩
          exact ⟨⟨q, h1, h2⟩, hi⟩
      rw [hset]
      exact MeasurableSet.inter (MeasurableSet.biUnion (Finset.countable_toSet _) fun q hq =>
        (retainedFiltration ι hQ).mono (Finset.mem_range.1 hq).le _ (hA q))
        ((hstart (n + 1)).measurableSet_eq_of_countable i)
    · exact (MeasurableSet.iUnion fun q => le_iSup (fun t => retainedFiltration ι hQ t) q _
        (hA q)).inter (measurableSet_eq_top_iSup (hstart (n + 1)))

end AndersonAC.AgentS78
