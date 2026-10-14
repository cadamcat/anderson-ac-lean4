import AndersonAC.AgentS78.Construction.Invariant

/-!
# WP10 construction: blocks on a common internal state

`BlockRun` needs one internal state type for all blocks, while the tile block runs on
`RunRecord × TileScratch` and the clearing block on `RunRecord × ClearScratch`. A block is
moved to a larger state type along a section `e` with retraction `p` (`p ∘ e = id`):
`Block.embed`. Its local run is the image of the original one (`localState_embed`), so
measurability, the order/auxiliary disciplines, the first-trial failure, reachable states and
hence every per-block discipline transfer unchanged.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources Query Answer querySigns)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Rec St St' : Type}

/-- A block moved to the state type `St'` along `e : St → St'` with retraction `p`. -/
def Block.embed (B : Block ι Rec St) (e : St → St') (p : St' → St) : Block ι Rec St' where
  enter x := e (B.enter x)
  next s := B.next (p s)
  update s a := e (B.update (p s) a)
  halted s := B.halted (p s)
  exit s := B.exit (p s)
  firstFail s := B.firstFail (p s)

variable (M : ℕ → ℕ) (B : Block ι Rec St) (e : St → St') (p : St' → St)

theorem machineRun_embed (hpe : ∀ s, p (e s) = s) (x : Rec) (k : ℕ) (ω : RandomSources ι M) :
    machineRun ι M ((B.embed e p).enter x) (B.embed e p).next (B.embed e p).update k ω =
      (e (machineRun ι M (B.enter x) B.next B.update k ω).1,
        (machineRun ι M (B.enter x) B.next B.update k ω).2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((B.embed e p).update
        (machineRun ι M ((B.embed e p).enter x) (B.embed e p).next (B.embed e p).update k ω).1
        (localAnswer ι M
          (machineRun ι M ((B.embed e p).enter x) (B.embed e p).next (B.embed e p).update k ω).2
          ((B.embed e p).next (machineRun ι M ((B.embed e p).enter x) (B.embed e p).next
            (B.embed e p).update k ω).1) ω),
      (machineRun ι M ((B.embed e p).enter x) (B.embed e p).next (B.embed e p).update k ω).2 ++
        [(B.embed e p).next (machineRun ι M ((B.embed e p).enter x) (B.embed e p).next
          (B.embed e p).update k ω).1]) = _
    rw [ih]
    simp only [Block.embed, hpe]
    rfl

theorem localState_embed (hpe : ∀ s, p (e s) = s) (x : Rec) (k : ℕ) (ω : RandomSources ι M) :
    localState M (B.embed e p) x k ω = e (localState M B x k ω) := by
  unfold localState machineState
  rw [machineRun_embed M B e p hpe]

theorem localFirstFail_embed (hpe : ∀ s, p (e s) = s) (x : Rec) :
    localFirstFail M (B.embed e p) x = localFirstFail M B x := by
  ext ω
  simp only [localFirstFail, Set.mem_ofPred_eq, localState_embed M B e p hpe]
  simp only [Block.embed, hpe]

theorem Block.IsMeasurable.embed [MeasurableSpace Rec] [MeasurableSpace St]
    [MeasurableSpace St'] {B : Block ι Rec St} (hB : B.IsMeasurable) {e : St → St'}
    {p : St' → St} (he : Measurable e) (hp : Measurable p) : (B.embed e p).IsMeasurable where
  enter := he.comp hB.enter
  next := hB.next.comp hp
  update := he.comp (hB.update.comp (hp.prodMap measurable_id))
  halted := hB.halted.comp hp
  exit := hB.exit.comp hp
  firstFail := hB.firstFail.comp hp

theorem blockReach_embed (hpe : ∀ s, p (e s) = s) (x : Rec) (s' : St')
    (h : BlockReach (B.embed e p) x s') : ∃ s, BlockReach B x s ∧ s' = e s := by
  induction h with
  | enter => exact ⟨B.enter x, BlockReach.enter, rfl⟩
  | step s' a _ hh ih =>
    obtain ⟨s, hs, rfl⟩ := ih
    refine ⟨B.update s a, BlockReach.step s a hs ?_, ?_⟩
    · simpa [Block.embed, hpe] using hh
    · simp [Block.embed, hpe]

/-- The order discipline transfers to the embedded block. -/
theorem embed_orders (hpe : ∀ s, p (e s) = s) (S : Set ℕ)
    (h : ∀ x k ω o, B.halted (localState M B x k ω) = false →
      B.next (localState M B x k ω) = Query.nextOrder o →
      o ∈ S ∧ ((List.range k).filter fun k' => B.halted (localState M B x k' ω) = false ∧
        B.next (localState M B x k' ω) = Query.nextOrder o).length < M o) :
    ∀ x k ω o, (B.embed e p).halted (localState M (B.embed e p) x k ω) = false →
      (B.embed e p).next (localState M (B.embed e p) x k ω) = Query.nextOrder o →
      o ∈ S ∧ ((List.range k).filter fun k' =>
        (B.embed e p).halted (localState M (B.embed e p) x k' ω) = false ∧
        (B.embed e p).next (localState M (B.embed e p) x k' ω) = Query.nextOrder o).length <
          M o := by
  simp only [localState_embed M B e p hpe]
  simp only [Block.embed, hpe]
  exact h

/-- The auxiliary discipline transfers to the embedded block. -/
theorem embed_aux (hpe : ∀ s, p (e s) = s) (S : Set ℕ)
    (h : ∀ x k ω a, B.halted (localState M B x k ω) = false →
      B.next (localState M B x k ω) = Query.auxiliary a →
      a ∈ S ∧ ∀ k' < k, B.halted (localState M B x k' ω) = false →
        B.next (localState M B x k' ω) ≠ Query.auxiliary a) :
    ∀ x k ω a, (B.embed e p).halted (localState M (B.embed e p) x k ω) = false →
      (B.embed e p).next (localState M (B.embed e p) x k ω) = Query.auxiliary a →
      a ∈ S ∧ ∀ k' < k, (B.embed e p).halted (localState M (B.embed e p) x k' ω) = false →
        (B.embed e p).next (localState M (B.embed e p) x k' ω) ≠ Query.auxiliary a := by
  simp only [localState_embed M B e p hpe]
  simp only [Block.embed, hpe]
  exact h

/-- A per-block invariant step transfers to the embedded block. -/
theorem embed_inv (hpe : ∀ s, p (e s) = s) (I I' : Set Rec)
    (h : ∀ x ∈ I, ∀ s, BlockReach B x s → B.halted s = true → B.exit s ∈ I') :
    ∀ x ∈ I, ∀ s', BlockReach (B.embed e p) x s' → (B.embed e p).halted s' = true →
      (B.embed e p).exit s' ∈ I' := by
  intro x hx s' hs' hh
  obtain ⟨s, hs, rfl⟩ := blockReach_embed B e p hpe x s' hs'
  simp only [Block.embed, hpe] at hh ⊢
  exact h x hx s hs hh

/-- A marking discipline (exit relation over reachable halted states) transfers. -/
theorem embed_reach_exit (hpe : ∀ s, p (e s) = s) (R : Rec → St → Rec → Prop)
    (h : ∀ x s, BlockReach B x s → B.halted s = true → R x s (B.exit s)) :
    ∀ x s', BlockReach (B.embed e p) x s' → (B.embed e p).halted s' = true →
      R x (p s') ((B.embed e p).exit s') := by
  intro x s' hs' hh
  obtain ⟨s, hs, rfl⟩ := blockReach_embed B e p hpe x s' hs'
  simp only [Block.embed, hpe] at hh ⊢
  exact h x s hs hh

/-- The query discipline of `fresh_of_declared` transfers to the embedded block. -/
theorem embed_query (hpe : ∀ s, p (e s) = s) {σ : Type} (freshSet : Rec → Set σ)
    (qs : Query ι → Set σ)
    (h : ∀ x k (ω : RandomSources ι M),
      (∀ k' < k, B.halted (localState M B x k' ω) = false) →
      B.halted (localState M B x k ω) = true →
      freshSet (B.exit (localState M B x k ω)) ⊆ freshSet x ∧
      ∀ k' < k, ∀ z ∈ freshSet (B.exit (localState M B x k ω)),
        z ∉ qs (B.next (localState M B x k' ω))) :
    ∀ x k (ω : RandomSources ι M),
      (∀ k' < k, (B.embed e p).halted (localState M (B.embed e p) x k' ω) = false) →
      (B.embed e p).halted (localState M (B.embed e p) x k ω) = true →
      freshSet ((B.embed e p).exit (localState M (B.embed e p) x k ω)) ⊆ freshSet x ∧
      ∀ k' < k, ∀ z ∈ freshSet ((B.embed e p).exit (localState M (B.embed e p) x k ω)),
        z ∉ qs ((B.embed e p).next (localState M (B.embed e p) x k' ω)) := by
  simp only [localState_embed M B e p hpe]
  simp only [Block.embed, hpe]
  exact h

end AndersonAC.AgentS78
