import AndersonAC.AgentS78.Construction.SimpleDisciplines
import AndersonAC.AgentS78.Construction.RecordFresh
import AndersonAC.AgentS78.Construction.ResetBlock

/-!
# WP10 construction: record-level disciplines of the stage transitions

The stage transitions (snapshot, sweep end, reset, cutoff; luna-s78reset's `sweepEndMap`,
`resetMap`) are query-free blocks `simpleBlock sc₀ f` (SimpleBlocks.lean). Their block
disciplines (`simpleBlock_marking`, `simpleBlock_query`, `simpleBlock_inv`) reduce to
record-level facts about `f`, proved here:

* `KeepsMarks f`: `f` keeps pending sites and their latest labels (marking discipline);
* `ShrinksFresh f`: `declaredFresh (f x) ⊆ declaredFresh x` (query discipline).

All transitions satisfy both outright (`declaredFresh` does not depend on the active set,
which the sweep end recomputes from the live reserve ports).
Both properties are closed under composition (`KeepsMarks.comp`, `ShrinksFresh.comp`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- `f` keeps the pending sites and their latest labels. -/
def KeepsMarks (f : RunRecord d m → RunRecord d m) : Prop :=
  ∀ x, (f x).pending = x.pending ∧ (f x).latest = x.latest

/-- `f` only shrinks the declared-fresh signs. -/
def ShrinksFresh (f : RunRecord d m → RunRecord d m) (I : Set (RunRecord d m)) : Prop :=
  ∀ x ∈ I, declaredFresh (f x) ⊆ declaredFresh x

theorem KeepsMarks.comp {f g : RunRecord d m → RunRecord d m} (hf : KeepsMarks f)
    (hg : KeepsMarks g) : KeepsMarks (f ∘ g) := fun x =>
  ⟨((hf (g x)).1.trans (hg x).1), ((hf (g x)).2.trans (hg x).2)⟩

theorem ShrinksFresh.comp {f g : RunRecord d m → RunRecord d m} {I J : Set (RunRecord d m)}
    (hf : ShrinksFresh f J) (hg : ShrinksFresh g I) (hgI : ∀ x ∈ I, g x ∈ J) :
    ShrinksFresh (f ∘ g) I := fun x hx =>
  (hf (g x) (hgI x hx)).trans (hg x hx)

theorem ShrinksFresh.mono {f : RunRecord d m → RunRecord d m} {I J : Set (RunRecord d m)}
    (hf : ShrinksFresh f J) (hIJ : I ⊆ J) : ShrinksFresh f I := fun x hx => hf x (hIJ hx)

/-- The marking discipline of a query-free block from `KeepsMarks`. -/
theorem KeepsMarks.marking {Sc : Type} {f : RunRecord d m → RunRecord d m} (hf : KeepsMarks f)
    (sc₀ : Sc) (P : Torus d m → Prop) :
    ∀ x s, BlockReach (simpleBlock sc₀ f) x s → (simpleBlock sc₀ f).halted s = true →
      ∀ y ∈ ((simpleBlock sc₀ f).exit s).pending,
        (y ∈ x.pending ∧ ((simpleBlock sc₀ f).exit s).latest y = x.latest y) ∨ P y :=
  simpleBlock_marking sc₀ f RunRecord.pending RunRecord.latest P
    (fun x => ⟨(hf x).1.subset, fun y _ => by rw [(hf x).2]⟩)

/-! ## The individual transitions -/

theorem keepsMarks_id : KeepsMarks (id : RunRecord d m → RunRecord d m) := fun _ => ⟨rfl, rfl⟩

theorem keepsMarks_snapshotMap (j : ℕ) : KeepsMarks (snapshotMap (d := d) (m := m) j) :=
  fun _ => ⟨rfl, rfl⟩

theorem keepsMarks_cutoffMap : KeepsMarks (cutoffMap (d := d) (m := m)) := fun _ => ⟨rfl, rfl⟩

theorem keepsMarks_sweepEndMap (j : ℕ) : KeepsMarks (sweepEndMap (d := d) (m := m) j) :=
  fun _ => ⟨rfl, rfl⟩

theorem keepsMarks_resetMap (t : ℝ) : KeepsMarks (resetMap (d := d) (m := m) t) :=
  fun _ => ⟨rfl, rfl⟩

theorem keepsMarks_sweepEndMapTheta (θ : ℝ) :
    KeepsMarks (sweepEndMapTheta (d := d) (m := m) θ) := fun _ => ⟨rfl, rfl⟩

theorem keepsMarks_sweepStartMap (θ t : ℝ) :
    KeepsMarks (sweepStartMap (d := d) (m := m) θ t) := fun _ => ⟨rfl, rfl⟩

theorem shrinksFresh_sweepStartMap (θ t : ℝ) (I : Set (RunRecord d m)) :
    ShrinksFresh (sweepStartMap θ t) I := fun _ _ => le_rfl

theorem shrinksFresh_id (I : Set (RunRecord d m)) : ShrinksFresh id I := fun _ _ => le_rfl

theorem shrinksFresh_snapshotMap (j : ℕ) (I : Set (RunRecord d m)) :
    ShrinksFresh (snapshotMap j) I := fun _ _ => le_rfl

theorem shrinksFresh_resetMap (t : ℝ) (I : Set (RunRecord d m)) :
    ShrinksFresh (resetMap t) I := fun _ _ => le_rfl

theorem shrinksFresh_cutoffMap (I : Set (RunRecord d m)) : ShrinksFresh cutoffMap I := by
  intro x _
  refine declaredFresh_mono x (cutoffMap x) (fun h => ?_) (fun _ i hp ht => ⟨hp, ht, le_rfl⟩)
  simp only [cutoffMap, Bool.or_eq_false_iff] at h
  exact h.1

theorem shrinksFresh_sweepEndMapTheta (θ : ℝ) (I : Set (RunRecord d m)) :
    ShrinksFresh (sweepEndMapTheta (d := d) (m := m) θ) I := fun _ _ => le_rfl

theorem shrinksFresh_sweepEndMap (j : ℕ) (I : Set (RunRecord d m)) :
    ShrinksFresh (sweepEndMap (d := d) (m := m) j) I := fun _ _ => le_rfl

end AndersonAC.AgentS78
