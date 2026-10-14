import AndersonAC.AgentS78.Construction.Transitions

/-!
# WP10 construction: the snapshot components partition the pending sites

`snapshotComponents P R` (Transitions.lean) lists the connected components of the snapshot
graph on the pending set `P` (07-assembly.tex:18–24). Here: the component of a pending site
(`snapComp`), membership, every listed component containing `y` is the component of `y`
(`eq_snapComp_of_mem`), and its cardinality is the one used by `stage_dichotomy`
(`snapComp_card`). Inputs for the clearing attempt/locality facts of `runOps_dich`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

open Classical in
/-- The snapshot component of a pending site. -/
def snapComp (P : Finset (Torus d m)) (R : ℝ) (y : Torus d m) (hy : y ∈ P) :
    Finset (Torus d m) :=
  (P.attach.filter fun z => (snapshotGraph d m P R).Reachable ⟨y, hy⟩ z).map
    (Function.Embedding.subtype _)

open Classical in
theorem mem_snapComp (P : Finset (Torus d m)) (R : ℝ) (y : Torus d m) (hy : y ∈ P)
    (z : Torus d m) :
    z ∈ snapComp P R y hy ↔ ∃ hz : z ∈ P, (snapshotGraph d m P R).Reachable ⟨y, hy⟩ ⟨z, hz⟩ := by
  unfold snapComp
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨⟨w, hw⟩, hr, rfl⟩; exact ⟨hw, hr⟩
  · rintro ⟨hz, hr⟩; exact ⟨⟨z, hz⟩, hr, rfl⟩

theorem self_mem_snapComp (P : Finset (Torus d m)) (R : ℝ) (y : Torus d m) (hy : y ∈ P) :
    y ∈ snapComp P R y hy :=
  (mem_snapComp P R y hy y).mpr ⟨hy, SimpleGraph.Reachable.refl _⟩

theorem snapComp_eq (P : Finset (Torus d m)) (R : ℝ) (y z : Torus d m) (hy : y ∈ P)
    (hz : z ∈ P) (h : z ∈ snapComp P R y hy) : snapComp P R z hz = snapComp P R y hy := by
  obtain ⟨_, hyz⟩ := (mem_snapComp P R y hy z).mp h
  ext w
  rw [mem_snapComp, mem_snapComp]
  constructor
  · rintro ⟨hw, hzw⟩; exact ⟨hw, hyz.trans hzw⟩
  · rintro ⟨hw, hyw⟩; exact ⟨hw, hyz.symm.trans hyw⟩

open Classical in
theorem mem_snapshotComponents (P : Finset (Torus d m)) (R : ℝ) (B : Finset (Torus d m)) :
    B ∈ snapshotComponents P R ↔ ∃ y, ∃ hy : y ∈ P, B = snapComp P R y hy := by
  unfold snapshotComponents
  simp only [Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩

/-- **A listed component containing `y` is the component of `y`.** -/
theorem eq_snapComp_of_mem (P : Finset (Torus d m)) (R : ℝ) (B : Finset (Torus d m))
    (hB : B ∈ snapshotComponents P R) (y : Torus d m) (hyB : y ∈ B) :
    ∃ hy : y ∈ P, B = snapComp P R y hy := by
  obtain ⟨z, hz, rfl⟩ := (mem_snapshotComponents P R B).mp hB
  obtain ⟨hy, _⟩ := (mem_snapComp P R z hz y).mp hyB
  exact ⟨hy, (snapComp_eq P R z y hz hy hyB).symm⟩

theorem snapComp_mem (P : Finset (Torus d m)) (R : ℝ) (y : Torus d m) (hy : y ∈ P) :
    snapComp P R y hy ∈ snapshotComponents P R :=
  (mem_snapshotComponents P R _).mpr ⟨y, hy, rfl⟩

open Classical in
/-- The cardinality of the component, as `stage_dichotomy` counts it. -/
theorem snapComp_card (P : Finset (Torus d m)) (R : ℝ) (y : Torus d m) (hy : y ∈ P) :
    (snapComp P R y hy).card =
      (Finset.univ.filter ((snapshotGraph d m P R).Reachable ⟨y, hy⟩)).card := by
  unfold snapComp
  rw [Finset.card_map]
  congr 1

end AndersonAC.AgentS78
