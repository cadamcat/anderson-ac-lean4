import AndersonAC.AgentS78.Construction.TileBlock

/-!
# query discipline and locality of the tile block

* `tileBlock_orders`, `tileBlock_aux`: the `orders` / `aux` fields of `BlockRun` for the
  index sets `tileOrderSet j T`, `tileAuxSet d m j T` (each order `π_{j,T,a}` is read at most
  `M = |T|` times, each auxiliary sign at most once);
* `tileOrderSet_disjoint`, `tileAuxSet_disjoint`: different tiles or sweeps use disjoint
  index sets;
* `tileBlock_fail_local`: the first-trial failure depends only on `tilePattern`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer querySigns)

/-! ## Generic facts on block-local runs -/

section Generic
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Rec St : Type} (M : ℕ → ℕ)

theorem localState_zero (B : Block ι Rec St) (x : Rec) (ω : RandomSources ι M) :
    localState M B x 0 ω = B.enter x := rfl

theorem machineRun_succ {S : Type} (init : S) (next : S → Query ι)
    (update : S → Answer ι → S) (q : ℕ) (ω : RandomSources ι M) :
    machineRun ι M init next update (q + 1) ω =
      (update (machineRun ι M init next update q ω).1
        (localAnswer ι M (machineRun ι M init next update q ω).2
          (next (machineRun ι M init next update q ω).1) ω),
       (machineRun ι M init next update q ω).2 ++
        [next (machineRun ι M init next update q ω).1]) := rfl

theorem localState_succ (B : Block ι Rec St) (x : Rec) (k : ℕ) (ω : RandomSources ι M) :
    localState M B x (k + 1) ω = B.update (localState M B x k ω)
      (localAnswer ι M (machineRun ι M (B.enter x) B.next B.update k ω).2
        (B.next (localState M B x k ω)) ω) := rfl

/-- Inductive invariants hold along every block-local run. -/
theorem localState_induct (B : Block ι Rec St) (x : Rec) (Inv : St → Prop)
    (h0 : Inv (B.enter x)) (hstep : ∀ s a, Inv s → Inv (B.update s a)) (k : ℕ)
    (ω : RandomSources ι M) : Inv (localState M B x k ω) := by
  induction k with
  | zero => exact h0
  | succ k ih => rw [localState_succ]; exact hstep _ _ ih

/-- The answer to a query reading only pattern coordinates is decided by them. -/
theorem localAnswer_congr (L : List (Query ι)) (c : Query ι) (π : FreshPattern ι)
    (hsigns : ∀ z ∈ querySigns ι c, z ∈ π.signs)
    (horders : ∀ o, c = Query.nextOrder o → o ∈ π.orders)
    (ω ω' : RandomSources ι M) (h1 : ∀ z ∈ π.signs, ω.1 z = ω'.1 z)
    (h2 : ∀ o ∈ π.orders, ω.2 o = ω'.2 o) :
    localAnswer ι M L c ω = localAnswer ι M L c ω' := by
  unfold localAnswer
  refine Prod.ext ?_ ?_
  · funext z
    by_cases hz : z ∈ querySigns ι c
    · simp only [hz, if_true, h1 z (hsigns z hz)]
    · simp only [hz, if_false]
  · cases c with
    | nextOrder o => simp only [h2 o (horders o rfl)]
    | _ => rfl

end Generic

/-! ## Structure of one step of the tile block -/

section Steps
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)

/-- Bookkeeping fields untouched by a trial step. -/
structure KeepsLog (s s' : RunRecord d m × TileScratch d m) : Prop where
  orderCount : s'.2.orderCount = s.2.orderCount
  auxUsed : s'.2.auxUsed = s.2.auxUsed

/-- The three possible outcomes of one step: an ordinary step inside the current trial, a
halt (acceptance or abort), or a retry. -/
def StepShape (s s' : RunRecord d m × TileScratch d m) : Prop :=
  (s'.1 = s.1 ∧ s'.2.attempt = s.2.attempt ∧ s'.2.firstFail = s.2.firstFail ∧
      s'.2.halted = s.2.halted) ∨
    (s'.2.halted = true ∧ s'.2.attempt = s.2.attempt ∧
      (s.2.firstFail = true → s'.2.firstFail = true)) ∨
    (s'.2.attempt = s.2.attempt + 1 ∧ s'.2.firstFail = true ∧ s'.2.halted = s.2.halted)

theorem failTrial_keeps (s : RunRecord d m × TileScratch d m) :
    KeepsLog s (failTrial P j T s) ∧ StepShape s (failTrial P j T s) := by
  unfold failTrial StepShape
  split_ifs <;> simp [KeepsLog.mk, trialScratch]

theorem scalarStep_keeps (s : RunRecord d m × TileScratch d m) (i : Torus d m) (ζ : ℝ) :
    KeepsLog s (scalarStep P j T s i ζ) ∧ StepShape s (scalarStep P j T s i ζ) := by
  unfold scalarStep
  dsimp only
  split_ifs
  · exact ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact failTrial_keeps P j T s

theorem tileStep_keeps (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (a : Answer (Torus d m)) :
    KeepsLog s (tileStep P j T s q a) ∧ StepShape s (tileStep P j T s q a) := by
  unfold tileStep
  rcases q with ⟨i, h⟩ | k | ⟨i, h⟩ | o | _
  · rcases hs : s.2.site with _ | i'
    · exact ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact scalarStep_keeps P j T s i' _
  · rcases hs : s.2.site with _ | i'
    · exact ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact scalarStep_keeps P j T s i' _
  · rcases hs : s.2.site with _ | i'
    · exact ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact scalarStep_keeps P j T s i' _
  · exact ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · rcases hs : s.2.site with _ | i'
    · exact ⟨⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl, fun h => h⟩)⟩
    · exact ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Shape of the issued queries. -/
theorem tileQuery_nextOrder (s : RunRecord d m × TileScratch d m) (o : ℕ)
    (h : tileQuery P j T s = Query.nextOrder o) :
    o = tileOrderIndex j T s.2.attempt ∧
      s.2.orderCount o < (tileSites (P.cover j) T).card := by
  unfold tileQuery at h
  rcases hs : s.2.site with _ | i <;> rw [hs] at h <;> simp only at h
  · split_ifs at h with hlt
    · cases h; exact ⟨rfl, hlt⟩
  · split_ifs at h

theorem tileQuery_auxiliary (s : RunRecord d m × TileScratch d m) (k : ℕ)
    (h : tileQuery P j T s = Query.auxiliary k) :
    (∃ i : Torus d m, k = tileAuxIndex j T s.2.attempt i) ∧ s.2.auxUsed k = false := by
  unfold tileQuery at h
  rcases hs : s.2.site with _ | i <;> rw [hs] at h <;> simp only at h
  · split_ifs at h
  · split_ifs at h with h1 h2 h3 h4
    · cases h; exact ⟨⟨i, rfl⟩, by simpa using h4⟩

end Steps

/-! ## Query discipline -/

section Discipline
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

theorem tileBlock_halted (s : RunRecord d m × TileScratch d m) :
    (tileBlock P j T).halted s = s.2.halted := rfl

theorem tileBlock_update_halted (s : RunRecord d m × TileScratch d m) (a : Answer (Torus d m))
    (h : s.2.halted = true) : (tileBlock P j T).update s a = s := by
  simp [tileBlock, h]

theorem tileBlock_update_running (s : RunRecord d m × TileScratch d m) (a : Answer (Torus d m))
    (h : s.2.halted = false) : (tileBlock P j T).update s a =
      tileStep P j T (s.1, logQuery (tileQuery P j T s) s.2) (tileQuery P j T s) a := by
  simp [tileBlock, h]

theorem tileBlock_next_running (s : RunRecord d m × TileScratch d m)
    (h : s.2.halted = false) : (tileBlock P j T).next s = tileQuery P j T s := by
  simp [tileBlock, h]

/-- The block's order counts are the counts of the issued (non-halted) order queries. -/
theorem tileBlock_orderCount (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (o : ℕ) : (localState M (tileBlock P j T) x k ω).2.orderCount o =
      ((List.range k).filter fun k' =>
        (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false ∧
        (tileBlock P j T).next (localState M (tileBlock P j T) x k' ω) =
          Query.nextOrder o).length := by
  induction k with
  | zero =>
    simp only [localState_zero, List.range_zero, List.filter_nil, List.length_nil]
    simp only [tileBlock]; split_ifs <;> rfl
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ← ih, localState_succ]
    set s := localState M (tileBlock P j T) x k ω with hs
    by_cases hh : s.2.halted = true
    · rw [tileBlock_update_halted P j T s _ hh]
      simp [hh, tileBlock_halted, ← hs]
    · have hf : s.2.halted = false := by simpa using hh
      rw [tileBlock_update_running P j T s _ hf,
        (tileStep_keeps P j T _ _ _).1.orderCount]
      by_cases hq : tileQuery P j T s = Query.nextOrder o
      · simp [hq, logQuery, hf, tileBlock_halted, tileBlock_next_running P j T s hf, ← hs]
      · simp [hq, logQuery, hf, tileBlock_halted, tileBlock_next_running P j T s hf, ← hs]

/-- The block's auxiliary log records exactly the issued (non-halted) auxiliary queries. -/
theorem tileBlock_auxUsed (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (a : ℕ) : (localState M (tileBlock P j T) x k ω).2.auxUsed a = true ↔
      ∃ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false ∧
        (tileBlock P j T).next (localState M (tileBlock P j T) x k' ω) = Query.auxiliary a := by
  induction k with
  | zero =>
    simp only [localState_zero, Nat.not_lt_zero, false_and, exists_false, iff_false]
    simp only [tileBlock]; split_ifs <;> simp [initScratch]
  | succ k ih =>
    rw [localState_succ]
    set s := localState M (tileBlock P j T) x k ω with hs
    have hsplit : (∃ k' < k + 1, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω)
        = false ∧ (tileBlock P j T).next (localState M (tileBlock P j T) x k' ω) =
          Query.auxiliary a) ↔
        (∃ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false ∧
          (tileBlock P j T).next (localState M (tileBlock P j T) x k' ω) = Query.auxiliary a) ∨
        ((tileBlock P j T).halted s = false ∧ (tileBlock P j T).next s = Query.auxiliary a) := by
      constructor
      · rintro ⟨k', hk', hh⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hlt | rfl
        · exact Or.inl ⟨k', hlt, hh⟩
        · exact Or.inr hh
      · rintro (⟨k', hk', hh⟩ | hh)
        · exact ⟨k', Nat.lt_succ_of_lt hk', hh⟩
        · exact ⟨k, Nat.lt_succ_self k, hh⟩
    rw [hsplit, ← ih]
    by_cases hh : s.2.halted = true
    · rw [tileBlock_update_halted P j T s _ hh]
      simp [hh, tileBlock_halted]
    · have hf : s.2.halted = false := by simpa using hh
      rw [tileBlock_update_running P j T s _ hf, (tileStep_keeps P j T _ _ _).1.auxUsed]
      simp [logQuery, hf, tileBlock_halted, tileBlock_next_running P j T s hf]

/-- **Order discipline** (`BlockRun.orders`) of the tile block. -/
theorem tileBlock_orders
    (hM : ∀ a, M (tileOrderIndex j T a) = (tileSites (P.cover j) T).card) :
    ∀ x k ω o, (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = false →
    (tileBlock P j T).next (localState M (tileBlock P j T) x k ω) = Query.nextOrder o →
    o ∈ tileOrderSet j T ∧
    ((List.range k).filter fun k' =>
      (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false ∧
      (tileBlock P j T).next (localState M (tileBlock P j T) x k' ω) =
        Query.nextOrder o).length < M o := by
  intro x k ω o hh hq
  set s := localState M (tileBlock P j T) x k ω
  have hf : s.2.halted = false := hh
  rw [tileBlock_next_running P j T s hf] at hq
  obtain ⟨ho, hlt⟩ := tileQuery_nextOrder P j T s o hq
  refine ⟨⟨_, ho⟩, ?_⟩
  rw [← tileBlock_orderCount, ho, hM]
  rw [ho] at hlt
  exact hlt

/-- **Auxiliary discipline** (`BlockRun.aux`) of the tile block. -/
theorem tileBlock_aux :
    ∀ x k ω a, (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = false →
    (tileBlock P j T).next (localState M (tileBlock P j T) x k ω) = Query.auxiliary a →
    a ∈ tileAuxSet d m j T ∧ ∀ k' < k,
      (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false →
      (tileBlock P j T).next (localState M (tileBlock P j T) x k' ω) ≠ Query.auxiliary a := by
  intro x k ω a hh hq
  set s := localState M (tileBlock P j T) x k ω
  have hf : s.2.halted = false := hh
  rw [tileBlock_next_running P j T s hf] at hq
  obtain ⟨⟨i, hi⟩, hused⟩ := tileQuery_auxiliary P j T s a hq
  refine ⟨⟨_, i, hi⟩, fun k' hk' hh' hq' => ?_⟩
  have := (tileBlock_auxUsed P j T M x k ω a).mpr ⟨k', hk', hh', hq'⟩
  rw [hused] at this
  exact Bool.false_ne_true this

end Discipline

/-! ## Disjoint source indices -/

theorem tileOrderIndex_injective {j T a j' T' a' : ℕ}
    (h : tileOrderIndex j T a = tileOrderIndex j' T' a') : j = j' ∧ T = T' ∧ a = a' := by
  unfold tileOrderIndex at h
  have h1 := (Nat.pair_eq_pair.mp h).2
  have h2 := Nat.pair_eq_pair.mp h1
  have h3 := Nat.pair_eq_pair.mp h2.1
  exact ⟨h3.1, h3.2, h2.2⟩

theorem tileAuxIndex_injective {d m : ℕ} {j T a j' T' a' : ℕ} {i i' : Torus d m}
    (h : tileAuxIndex j T a i = tileAuxIndex j' T' a' i') :
    j = j' ∧ T = T' ∧ a = a' ∧ i = i' := by
  unfold tileAuxIndex at h
  have h1 := (Nat.pair_eq_pair.mp h).2
  have h2 := Nat.pair_eq_pair.mp h1
  have h3 := Nat.pair_eq_pair.mp h2.1
  have h4 := Nat.pair_eq_pair.mp h3.1
  exact ⟨h4.1, h4.2, h3.2, (siteRank d m).injective (Fin.ext h2.2)⟩

theorem tileOrderSet_disjoint {j T j' T' : ℕ} (h : (j, T) ≠ (j', T')) :
    Disjoint (tileOrderSet j T) (tileOrderSet j' T') := by
  rw [Set.disjoint_left]
  rintro o ⟨a, rfl⟩ ⟨a', ha⟩
  obtain ⟨h1, h2, -⟩ := tileOrderIndex_injective ha
  exact h (by rw [h1, h2])

theorem tileAuxSet_disjoint (d m : ℕ) {j T j' T' : ℕ} (h : (j, T) ≠ (j', T')) :
    Disjoint (tileAuxSet d m j T) (tileAuxSet d m j' T') := by
  rw [Set.disjoint_left]
  rintro k ⟨a, i, rfl⟩ ⟨a', i', ha⟩
  obtain ⟨h1, h2, -, -⟩ := tileAuxIndex_injective ha
  exact h (by rw [h1, h2])

/-! ## Locality of the first trial -/

section Local
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

/-- A running first-trial state with the entering record reads only pattern coordinates. -/
theorem tileQuery_reads_pattern (x : RunRecord d m) (s : RunRecord d m × TileScratch d m)
    (hx : s.1 = x) (hxaborted : x.aborted = false) (ha : s.2.attempt = 0) :
    (∀ z ∈ querySigns (Torus d m) (tileQuery P j T s), z ∈ (tilePattern P j T x).signs) ∧
    (∀ o, tileQuery P j T s = Query.nextOrder o → o ∈ (tilePattern P j T x).orders) := by
  subst hx
  unfold tileQuery
  rcases hs : s.2.site with _ | i
  · simp only
    split_ifs
    · refine ⟨fun z hz => by simp [querySigns] at hz, fun o ho => ?_⟩
      cases ho
      simp [tilePattern, hxaborted, ha]
    · exact ⟨fun z hz => by simp [querySigns] at hz, fun o ho => by cases ho⟩
  · simp only
    split_ifs with h1 h2 h3 h4
    · refine ⟨fun z hz => ?_, fun o ho => by cases ho⟩
      simp only [querySigns, Set.mem_setOf_eq] at hz
      obtain ⟨k, hk, rfl⟩ := hz
      have hmem : i ∈ (((TS P j T ∩ s.1.endpoint.active) \ s.1.pending) \ s.1.terminal) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨h1.1, h1.2.1⟩, h2.2⟩, h1.2.2⟩
      have hsite : i ∈ (tilePattern P j T s.1).sites := by
        simpa [tilePattern, hxaborted] using hmem
      have hheight : (tilePattern P j T s.1).height i ≤ k := by
        simpa [tilePattern, hxaborted] using hk
      exact Or.inl ⟨i, hsite, k, hheight, rfl⟩
    · refine ⟨fun z hz => ?_, fun o ho => by cases ho⟩
      simp only [querySigns, Set.mem_singleton_iff] at hz
      subst hz
      have hmem : i ∈ (((TS P j T ∩ s.1.endpoint.active) \ s.1.pending) \ s.1.terminal) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨h1.1, h1.2.1⟩, h2.2⟩, h1.2.2⟩
      have hsite : i ∈ (tilePattern P j T s.1).sites := by
        simpa [tilePattern, hxaborted] using hmem
      have hheight : (tilePattern P j T s.1).height i ≤ s.1.prefixLength i := by
        simp [tilePattern, hxaborted]
      exact Or.inl ⟨i, hsite, s.1.prefixLength i, hheight, rfl⟩
    · exact ⟨fun z hz => by simp [querySigns] at hz, fun o ho => by cases ho⟩
    · refine ⟨fun z hz => ?_, fun o ho => by cases ho⟩
      simp only [querySigns, Set.mem_singleton_iff] at hz
      subst hz
      refine Or.inr ⟨_, ?_, rfl⟩
      have hp : i ∈ s.1.pending := by
        by_contra hp; exact h2 ⟨ha, hp⟩
      have hmem : i ∈ (((TS P j T ∩ s.1.endpoint.active) ∩ s.1.pending) \ s.1.terminal) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨h1.1, h1.2.1⟩, hp⟩, h1.2.2⟩
      have haux : tileAuxIndex j T s.2.attempt i ∈ (tilePattern P j T s.1).aux := by
        have : tileAuxIndex j T s.2.attempt i ∈
            ((((TS P j T ∩ s.1.endpoint.active) ∩ s.1.pending) \ s.1.terminal).image
              (tileAuxIndex j T 0)) := by
          rw [Finset.mem_image]
          exact ⟨i, hmem, by rw [ha]⟩
        simpa [tilePattern, hxaborted] using this
      exact haux
    · exact ⟨fun z hz => by simp [querySigns] at hz, fun o ho => by cases ho⟩

/-- Invariant: a nonzero trial number implies a recorded first failure; a running first trial
still has the entering record. -/
def FirstTrialInv (x : RunRecord d m) (s : RunRecord d m × TileScratch d m) : Prop :=
  (s.2.attempt ≠ 0 → s.2.firstFail = true) ∧
    (s.2.attempt = 0 → s.2.halted = false → s.1 = x)

theorem firstTrialInv_enter (x : RunRecord d m) :
    FirstTrialInv x ((tileBlock P j T).enter x) := by
  simp only [FirstTrialInv, tileBlock]
  split_ifs <;> simp [initScratch]

theorem firstTrialInv_update (x : RunRecord d m) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) (h : FirstTrialInv x s) :
    FirstTrialInv x ((tileBlock P j T).update s a) := by
  by_cases hh : s.2.halted = true
  · rw [tileBlock_update_halted P j T s a hh]; exact h
  · have hf : s.2.halted = false := by simpa using hh
    rw [tileBlock_update_running P j T s a hf]
    set s₀ : RunRecord d m × TileScratch d m := (s.1, logQuery (tileQuery P j T s) s.2)
    have hs₀1 : s₀.1 = s.1 := rfl
    have hs₀a : s₀.2.attempt = s.2.attempt := rfl
    have hs₀f : s₀.2.firstFail = s.2.firstFail := rfl
    have hs₀h : s₀.2.halted = s.2.halted := rfl
    rcases (tileStep_keeps P j T s₀ (tileQuery P j T s) a).2 with
      ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · refine ⟨fun ha => ?_, fun ha hh' => ?_⟩
      · rw [e3, hs₀f]; exact h.1 (by rw [e2, hs₀a] at ha; exact ha)
      · rw [e1, hs₀1]; exact h.2 (by rw [e2, hs₀a] at ha; exact ha) hf
    · refine ⟨fun ha => ?_, fun _ hh' => ?_⟩
      · exact e3 (by rw [hs₀f]; exact h.1 (by rw [e2, hs₀a] at ha; exact ha))
      · rw [e1] at hh'; exact absurd hh' (by simp)
    · refine ⟨fun _ => e2, fun ha _ => ?_⟩
      rw [e1] at ha; exact absurd ha (Nat.succ_ne_zero _)

/-- **Locality of the first trial** (`BlockRun.fail_local`). -/
theorem tileBlock_fail_local (x : RunRecord d m) :
    DependsOnly (Torus d m) (M := M) (tilePattern P j T x)
      (localFirstFail M (tileBlock P j T) x) := by
  -- one direction for arbitrary agreeing samples, then symmetry
  suffices H : ∀ ω ω' : RandomSources (Torus d m) M,
      (∀ z ∈ (tilePattern P j T x).signs, ω.1 z = ω'.1 z) →
      (∀ o ∈ (tilePattern P j T x).orders, ω.2 o = ω'.2 o) →
      ω ∈ localFirstFail M (tileBlock P j T) x → ω' ∈ localFirstFail M (tileBlock P j T) x by
    intro ω ω' h1 h2
    exact ⟨H ω ω' h1 h2, H ω' ω (fun z hz => (h1 z hz).symm) (fun o ho => (h2 o ho).symm)⟩
  intro ω ω' h1 h2 hω
  have hxaborted : x.aborted = false := by
    cases hxb : x.aborted with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨k, _, hfk⟩ := hω
      have hno : ∀ n, (localState M (tileBlock P j T) x n ω).2.halted = true ∧
          (localState M (tileBlock P j T) x n ω).2.firstFail = false := by
        intro n
        exact localState_induct M (tileBlock P j T) x
          (fun s => s.2.halted = true ∧ s.2.firstFail = false)
          (by simp [tileBlock, hxb, initScratch])
          (fun s a hs => by
            rw [tileBlock_update_halted P j T s a hs.1]
            exact hs) n ω
      have hfk' : (localState M (tileBlock P j T) x k ω).2.firstFail = true := by
        simpa [tileBlock] using hfk
      rw [(hno k).2] at hfk'
      cases hfk'
  have hxaborted' : x.aborted = false := hxaborted
  obtain ⟨k, hk, hfk⟩ := hω
  classical
  have hex : ∃ n, (tileBlock P j T).firstFail (localState M (tileBlock P j T) x n ω) = true :=
    ⟨k, hfk⟩
  set k₀ := Nat.find hex
  have hk₀ : k₀ ≤ k := Nat.find_min' hex hfk
  have hinv : ∀ n, FirstTrialInv x (localState M (tileBlock P j T) x n ω) :=
    fun n => localState_induct M (tileBlock P j T) x (FirstTrialInv x)
      (firstTrialInv_enter P j T x) (fun s a hs => firstTrialInv_update P j T x s a hs) n ω
  -- before `k₀` the run is a running first trial with the entering record
  have hrun : ∀ n < k₀, (localState M (tileBlock P j T) x n ω).2.halted = false ∧
      (localState M (tileBlock P j T) x n ω).2.attempt = 0 ∧
      (localState M (tileBlock P j T) x n ω).1 = x := by
    intro n hn
    have hh : (localState M (tileBlock P j T) x n ω).2.halted = false := hk n (by omega)
    have hff : (localState M (tileBlock P j T) x n ω).2.firstFail = false := by
      have := Nat.find_min hex hn
      simpa [tileBlock] using this
    have ha : (localState M (tileBlock P j T) x n ω).2.attempt = 0 := by
      by_contra hne
      have := (hinv n).1 hne
      rw [hff] at this; exact Bool.false_ne_true this
    exact ⟨hh, ha, (hinv n).2 ha hh⟩
  have hagree : ∀ n ≤ k₀,
      machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update n ω =
      machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update n ω' := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have ihn := ih (by omega)
      obtain ⟨hh, ha, hx⟩ := hrun n (by omega)
      rw [machineRun_succ, machineRun_succ, ← ihn]
      set s := (machineRun (Torus d m) M ((tileBlock P j T).enter x) (tileBlock P j T).next
        (tileBlock P j T).update n ω).1
      have hs : s = localState M (tileBlock P j T) x n ω := rfl
      rw [← hs] at hh ha hx
      have hnext : (tileBlock P j T).next s = tileQuery P j T s :=
        tileBlock_next_running P j T s hh
      obtain ⟨hr1, hr2⟩ := tileQuery_reads_pattern P j T x s hx hxaborted' ha
      rw [localAnswer_congr M _ ((tileBlock P j T).next s) (tilePattern P j T x)
        (by rw [hnext]; exact hr1) (by rw [hnext]; exact hr2) ω ω' h1 h2]
  have hstate : ∀ n ≤ k₀, localState M (tileBlock P j T) x n ω =
      localState M (tileBlock P j T) x n ω' := fun n hn => by
    unfold localState machineState; rw [hagree n hn]
  refine ⟨k₀, fun n hn => ?_, ?_⟩
  · rw [← hstate n hn.le]; exact hk n (by omega)
  · rw [← hstate k₀ le_rfl]; exact Nat.find_spec hex

end Local

end AndersonAC.AgentS78

/-! ## Each accepted slot is one `S45.StepRel` step -/

namespace AndersonAC.AgentS78

section StepRel
variable {d m : ℕ}

/-- The update of an active slot is an `S45.StepRel` step (05:343–345, 04:230). -/
theorem stepLive_stepRel (t : ℝ) (r : Port d m → ℂ) (a : S45.LiveState (Port d m))
    (x : Port d m) (ξ : ℝ) (hx : x ∈ a.live) (hden : stepDen t r a x ξ ≠ 0) :
    S45.StepRel t r a (stepLive t r a x ξ) x ξ :=
  ⟨hx, rfl, rfl, hden⟩

theorem mask_mask {β : Type*} [Zero β] (S : Finset (Port d m)) (A : Matrix (Port d m) (Port d m) β) :
    S45.mask S (S45.mask S A) = S45.mask S A := by
  funext i j
  simp only [S45.mask, S45.pad, S45.restrict, Matrix.submatrix_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

/-- Appending a `StepRel` step keeps a sequence well formed. -/
theorem extendSeq_wellFormed (t : ℝ) (r : Port d m → ℂ) (q : S45.Sequence (Port d m))
    (hq : q.wellFormed t r) (x : Port d m) (ξ : ℝ)
    (hx : x ∈ (q.state q.length).live)
    (hden : stepDen t r (q.state q.length) x ξ ≠ 0) :
    (extendSeq q (stepLive t r (q.state q.length) x ξ) x ξ).wellFormed t r := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · simp only [extendSeq]
    split_ifs with h
    · simp only [stepLive]; exact (mask_mask _ _).symm
    · exact hq.1 k (by simp only [extendSeq] at hk; omega)
  · simp only [extendSeq] at hk ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · have h1 : k ≠ q.length := by omega
      have h2 : k ≠ q.length + 1 := by omega
      have h3 : k + 1 ≠ q.length + 1 := by omega
      simp only [h1, h2, h3, if_false]
      exact hq.2 k hlt
    · simp only [if_true, show q.length ≠ q.length + 1 by omega, if_false]
      exact stepLive_stepRel t r _ x ξ hx hden

end StepRel

end AndersonAC.AgentS78
