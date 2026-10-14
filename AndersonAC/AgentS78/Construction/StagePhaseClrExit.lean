import AndersonAC.AgentS78.Construction.StagePhaseClr

/-!
# The exits of the clearing block: damping, endpoint and the structural DONE facts

agent-s78phase2.

* `clr_exit_r`: every exit keeps the damping `r`;
* `clr_exit_trichotomy`: a halted reachable state exits by the empty exit (record unchanged),
  the FAIL exit (endpoint unchanged), or the DONE exit of a scheduled non-aborted attempt with a
  nonempty core, a non-failed DONE scratch, and `ClrInv`;
* `clr_done_physical`, `clr_done_nested`, `clr_done_removed`: the committed DONE endpoint is a
  damped endpoint for the frozen `x.r` (clause `physical` of `ClearingStepFacts`), lies in the
  entering active set, and removes exactly `core ∪ inspected ⊇ core ≠ ∅`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

section ClrExitSec
variable {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (y : Torus d m)

theorem clr_exit_r (s : RunRecord d m × ClearScratch d m) :
    (clearingExit (d := d) (m := m) j y s).r = s.1.r := by
  rcases clr_exit_cases j y s with h | h | h <;> rw [h] <;> rfl

theorem clr_failExit_endpoint (x : RunRecord d m) (sc : ClearScratch d m) :
    (clearingFailExit (d := d) (m := m) j y x sc).endpoint = x.endpoint := rfl

/-- **The three exits of a halted reachable state.** -/
theorem clr_exit_trichotomy (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (h : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) :
    clearingExit (d := d) (m := m) j y s = x ∨
      (s.2.core ≠ ∅ ∧
        clearingExit (d := d) (m := m) j y s = clearingFailExit (d := d) (m := m) j y x s.2) ∨
      (x.aborted = false ∧ clearingScheduled j m ∧ s.2.core ≠ ∅ ∧ s.2.failed = false ∧
        s.2.done = true ∧ clearingExit (d := d) (m := m) j y s = clearingDoneExit x s.2) := by
  have hx := (clr_reach n₀ j u y x s h).1
  subst hx
  unfold clearingExit
  by_cases h1 : s.1.aborted = true
  · rw [if_pos h1]; exact Or.inl rfl
  rw [if_neg h1]
  by_cases h2 : clearingScheduled j m
  · rw [if_neg (by simp [h2])]
    by_cases h3 : s.2.core = ∅
    · rw [if_pos h3]; exact Or.inl rfl
    rw [if_neg h3]
    by_cases h4 : s.2.failed = true
    · rw [if_pos h4]; exact Or.inr (Or.inl ⟨h3, rfl⟩)
    rw [if_neg h4]
    by_cases h5 : s.2.done = true
    · rw [if_pos h5]
      exact Or.inr (Or.inr ⟨by simpa using h1, h2, h3, by simpa using h4, h5, rfl⟩)
    · rw [if_neg h5]; exact Or.inl rfl
  · rw [if_pos (by simp [h2])]; exact Or.inl rfl

/-- At a DONE state the provisional active set has no core site. -/
theorem clr_done_active (x : RunRecord d m) (sc : ClearScratch d m) (hI : ClrInv j u x sc)
    (hab : x.aborted = false) (hsch : clearingScheduled j m) (hne : sc.core ≠ ∅)
    (hf : sc.failed = false) (hd : sc.done = true) :
    sc.active \ sc.core = sc.active ∧ sc.core ⊆ x.endpoint.active := by
  obtain ⟨hcp, hl⟩ := hI.done hd hf hab hsch hne
  obtain ⟨hpost, hcx⟩ := hI.post hcp
  refine ⟨Finset.sdiff_eq_self_of_disjoint ?_, hcx⟩
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm, hpost, hl]

/-- The committed DONE endpoint, with the core-free active set. -/
theorem clr_doneExit_endpoint (x : RunRecord d m) (sc : ClearScratch d m)
    (hA : sc.active \ sc.core = sc.active) :
    (clearingDoneExit x sc).endpoint =
      { active := sc.active, M := sc.Mnum.map Complex.ofReal,
        g := fun i k => if i ∈ sc.active ∧ k ∈ sc.active then sc.hatG i k else 0 } := by
  unfold clearingDoneExit
  simp only [hA]

/-- **The committed DONE endpoint is damped** for the frozen damping (clause `physical`). -/
theorem clr_done_physical (x : RunRecord d m) (sc : ClearScratch d m) (hI : ClrInv j u x sc)
    (hab : x.aborted = false) (hsch : clearingScheduled j m) (hne : sc.core ≠ ∅)
    (hf : sc.failed = false) (hd : sc.done = true) (ht : 0 < stageScale u j m)
    (hr : ∀ i ∈ x.endpoint.active, 0 < (x.r i).im) :
    IsDampedEndpoint (clearingDoneExit x sc).endpoint x.r (stageScale u j m) := by
  obtain ⟨hA, -⟩ := clr_done_active j u x sc hI hab hsch hne hf hd
  rw [clr_doneExit_endpoint x sc hA]
  set A := sc.active
  set t := stageScale u j m
  have hsym : (restrictM A sc.Mnum).IsSymm := by
    ext a b
    simp [restrictM, hI.symm b.val a.val]
  have hpos : ∀ a : {a // a ∈ A}, 0 < (x.r a.val).im := fun a => hr a.val (hI.sub a.2)
  have hunit := AndersonAC.SolS6.damped_det_unit (restrictM A sc.Mnum) hsym t ht
    (fun a : {a // a ∈ A} => x.r a.val) hpos
  have hB : (sc.Mnum.map Complex.ofReal).submatrix (fun a : {a // a ∈ A} => a.val)
        (fun a : {a // a ∈ A} => a.val) - (t : ℂ) • Matrix.diagonal (fun a : {a // a ∈ A} => x.r a.val) =
      AndersonAC.S6.dampedMatrix (restrictM A sc.Mnum) t (fun a : {a // a ∈ A} => x.r a.val) := by
    ext a b
    simp [AndersonAC.S6.dampedMatrix, restrictM]
  have hG : Matrix.submatrix
        (fun i k => if i ∈ A ∧ k ∈ A then sc.hatG i k else 0 : Matrix (Torus d m) (Torus d m) ℂ)
        (fun a : {a // a ∈ A} => a.val) (fun a : {a // a ∈ A} => a.val) =
      (AndersonAC.S6.dampedMatrix (restrictM A sc.Mnum) t (fun a : {a // a ∈ A} => x.r a.val))⁻¹ := by
    ext a b
    show (if a.val ∈ A ∧ b.val ∈ A then sc.hatG a.val b.val else 0) = _
    rw [if_pos ⟨a.2, b.2⟩, hI.inv a.val b.val a.2 b.2]
    unfold fullInv
    rw [dif_pos ⟨a.2, b.2⟩]
    rfl
  refine ⟨fun i k => ⟨by simp [hI.symm i k], by simp⟩, fun i k hik => ?_, ?_⟩
  · simp only
    rw [if_neg (by tauto)]
  · show _ ∧ _
    simp only
    rw [hB, hG]
    exact ⟨Matrix.mul_nonsing_inv _ hunit, Matrix.nonsing_inv_mul _ hunit⟩

/-- The removed set of a DONE exit lies in `core ∪ inspected` and contains the core. -/
theorem clr_done_removed (x : RunRecord d m) (sc : ClearScratch d m) (hI : ClrInv j u x sc)
    (hab : x.aborted = false) (hsch : clearingScheduled j m) (hne : sc.core ≠ ∅)
    (hf : sc.failed = false) (hd : sc.done = true) :
    (clearingDoneExit x sc).endpoint.active ⊆ x.endpoint.active ∧
      x.endpoint.active \ (clearingDoneExit x sc).endpoint.active ⊆ sc.core ∪ sc.inspected ∧
      sc.core ⊆ x.endpoint.active \ (clearingDoneExit x sc).endpoint.active := by
  obtain ⟨hA, hcx⟩ := clr_done_active j u x sc hI hab hsch hne hf hd
  rw [clr_doneExit_endpoint x sc hA]
  refine ⟨hI.sub, hI.removed, fun z hz => Finset.mem_sdiff.mpr ⟨hcx hz, fun hza => ?_⟩⟩
  have : z ∈ sc.active \ sc.core := hA.symm ▸ hza
  exact (Finset.mem_sdiff.mp this).2 hz

end ClrExitSec

end AndersonAC.AgentS78
