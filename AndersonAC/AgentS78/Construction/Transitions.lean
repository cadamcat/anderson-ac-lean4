import AndersonAC.AgentS78.Construction.SimpleBlocks

/-!
# WP10 construction, C3b-trans: snapshot and cutoff operations

07-assembly.tex:18–24 (snapshot): freeze the graph on the pending sites with edges at
physical distance ≤ R_j = 4^{8j}; its connected components are recorded in
`components`. 02-state.tex:357–360, 08-history.tex:299–305 (cutoff): after stage
J = ⌊m/2⌋ abort if any site is pending. Both are measurable maps of the committed record
(they change only discrete fields as functions of discrete fields), hence query-free blocks.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The code space of committed records. -/
abbrev CodeT (d m : ℕ) :=
  ℕ × ((Torus d m → Bool) × Matrix (Torus d m) (Torus d m) ℂ × Matrix (Torus d m) (Torus d m) ℂ ×
    (Torus d m → ℂ)) ×
  (ℕ × (ℕ → S45.initialPorts (Torus d m) → Bool) × (ℕ → S45.CMat (S45.initialPorts (Torus d m))) ×
    (ℕ → S45.initialPorts (Torus d m) → Bool) × (ℕ → ℝ)) ×
  ((Torus d m → ℝ) × (Torus d m → ℕ)) ×
  ((Torus d m → Bool) × (Torus d m → Bool) × (Torus d m → ℕ × Bool × (Torus d m → Bool))) ×
  (Finset (Torus d m) → Bool) × Bool

/-- A record map is measurable when its effect on the code is a measurable map of the code. -/
theorem RunRecord.measurable_of_code (f : RunRecord d m → RunRecord d m)
    (G : CodeT d m → CodeT d m)
    (hcode : ∀ x : RunRecord d m, RunRecord.code (f x) = G (RunRecord.code x))
    (hG : Measurable G) : Measurable f := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨G ⁻¹' t, hG ht, ?_⟩
  ext x
  simp only [Set.mem_preimage, hcode]

open Classical in
/-- The snapshot components of a pending set (07-assembly.tex:18–24). -/
def snapshotComponents (P : Finset (Torus d m)) (R : ℝ) : Finset (Finset (Torus d m)) :=
  P.attach.image fun x =>
    (P.attach.filter fun y => (snapshotGraph d m P R).Reachable x y).map
      (Function.Embedding.subtype _)

/-- The snapshot operation of stage `j`. -/
def snapshotMap (j : ℕ) (x : RunRecord d m) : RunRecord d m :=
  { x with components := snapshotComponents x.pending (separationRadius j) }

/-- The cutoff operation: abort if a site is pending. -/
def cutoffMap (x : RunRecord d m) : RunRecord d m :=
  { x with aborted := x.aborted || (x.pending.card != 0) }

theorem measurable_of_countable_dom {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (f : α → β) : Measurable f :=
  measurable_of_countable f

open Classical in
theorem snapshotMap_measurable (j : ℕ) : Measurable (snapshotMap (d := d) (m := m) j) := by
  let h : (Torus d m → Bool) → (Finset (Torus d m) → Bool) := fun c B =>
    decide (B ∈ snapshotComponents (Finset.univ.filter fun y => c y = true) (separationRadius j))
  have hh : Measurable h := measurable_of_countable h
  refine RunRecord.measurable_of_code _ (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2.1,
      t.2.2.2.2.1, h t.2.2.2.2.1.2.1, t.2.2.2.2.2.2)) ?_ (by fun_prop)
  intro x
  have hP : (Finset.univ.filter fun y => finsetCode x.pending y = true) = x.pending := by
    ext y; simp [finsetCode]
  simp only [RunRecord.code, snapshotMap, h, hP]
  congr

open Classical in
theorem cutoffMap_measurable : Measurable (cutoffMap (d := d) (m := m)) := by
  let h : (Torus d m → Bool) × Bool → Bool := fun p =>
    p.2 || ((Finset.univ.filter fun y => p.1 y = true).card != 0)
  have hh : Measurable h := measurable_of_countable h
  refine RunRecord.measurable_of_code _ (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2.1,
      t.2.2.2.2.1, t.2.2.2.2.2.1, h (t.2.2.2.2.1.2.1, t.2.2.2.2.2.2))) ?_ (by fun_prop)
  intro x
  have hP : (Finset.univ.filter fun y => finsetCode x.pending y = true) = x.pending := by
    ext y; simp [finsetCode]
  simp only [RunRecord.code, cutoffMap, h, hP]
  congr

end AndersonAC.AgentS78
