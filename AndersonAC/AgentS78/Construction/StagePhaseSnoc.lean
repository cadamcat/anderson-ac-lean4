import AndersonAC.AgentS78.Construction.StagePhase

/-!
# The clearing-phase invariant along clearing blocks: the logical part

* `ClearPhaseData.transfer`: a block whose exit keeps the endpoint and the damping (FAIL:
  numerical rollback, 07-assembly.tex:18–34; an empty block) keeps the clearing-phase data.
* `ClearingStepFacts I s' y`: the facts of one committed clearing with anchor `y` and new
  endpoint `s'` on top of the assembly prefix `I` (the per-operation fields of `AssemblyInput`,
  07-assembly.tex §7.3; on DONE they come from the §6 DONE outputs, `clearing_locality`,
  `uniform_clearing_geometry` and `successful_clearing_distortions`).
* `assemblySnoc`: the prefix extended by that clearing; `ClearPhaseData.snoc`: a DONE
  exit with these facts keeps the clearing-phase data (with `k + 1`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- **The facts of one committed clearing** with anchor `y` and new endpoint `s'`. -/
structure ClearingStepFacts {k : ℕ} {t b : ℝ} {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r)
    (s' : Endpoint (Torus d m)) (y : Torus d m) : Prop where
  physical : IsDampedEndpoint s' r t
  nested : s'.active ⊆ (I.state (Fin.last k)).active
  activeCount : Fintype.card (Torus d m) ≤ 2 * s'.active.card
  fresh : ∀ a, I.anchor a ≠ y
  removedNonempty : ((I.state (Fin.last k)).active \ s'.active).Nonempty
  removedSize : ((((I.state (Fin.last k)).active \ s'.active).card : ℝ) ≤ I.C * (heatLimit t : ℝ))
  removedLocal : ∀ i ∈ (I.state (Fin.last k)).active \ s'.active, physicalDistance d m i y ≤ I.Ds
  haloOverlap : ∀ x, (overlap (fun a : Fin (k + 1) =>
    cube d m (Fin.snoc (α := fun _ => Torus d m) I.anchor y a) (200 * I.Ds)) x : ℝ) ≤
      I.C * t ^ (-(d : ℝ) * nu d)
  metric : ∀ u v, physicalDistance d m u v / 2 - t ^ (-1.03 : ℝ) ≤
    terminalDistance (nnGraph d m) (Finset.univ \ s'.active) u v
  resolventDecay : ∀ i j, ‖normalizedInverse s' t i j‖ ≤
    I.C / Real.sqrt t * Real.exp (-I.c * t * max (physicalDistance d m i j / 2 - t ^ (-1.03 : ℝ)) 0)
  entryChange : ∀ i j, ‖survivorDifference (I.state (Fin.last k)) s' t i j‖ ≤
    I.C * Real.sqrt t * t ^ (0.42 * delta)
  rowChange : ∀ i, rowTwo (survivorDifference (I.state (Fin.last k)) s' t) i ≤ I.C * t ^ (0.25 * delta)
  totalChange : frobeniusSq (survivorDifference (I.state (Fin.last k)) s' t) ≤
    I.C * t ^ (-1 - 0.47 * delta)
  decay : ∀ i j,
    ‖survivorDifference (I.state (Fin.last k)) s' t i j‖ ≤ t ^ (-I.P) * Real.exp (-I.c * t *
      (max (distanceTo (physicalDistance d m) ((I.state (Fin.last k)).active \ s'.active) i -
          I.C * t ^ (-1.03 : ℝ)) 0 +
       max (distanceTo (physicalDistance d m) ((I.state (Fin.last k)).active \ s'.active) j -
          I.C * t ^ (-1.03 : ℝ)) 0))

/-- **The assembly prefix extended by one committed clearing.** -/
def assemblySnoc {k : ℕ} {t b : ℝ} {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r)
    (s' : Endpoint (Torus d m)) (y : Torus d m) (h : ClearingStepFacts I s' y) :
    AssemblyInput d m (k + 1) t b r where
  state := Fin.snoc (α := fun _ => Endpoint (Torus d m)) I.state s'
  anchor := Fin.snoc (α := fun _ => Torus d m) I.anchor y
  C := I.C
  c := I.c
  P := I.P
  Ds := I.Ds
  positive := I.positive
  scaleRadius := I.scaleRadius
  embedded := I.embedded
  damping := I.damping
  physical := fun a => by
    induction a using Fin.lastCases with
    | last => simpa using h.physical
    | cast a => simpa using I.physical a
  nested := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.nested
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.nested a
  activeCount := fun a => by
    induction a using Fin.lastCases with
    | last => simpa using h.activeCount
    | cast a => simpa using I.activeCount a
  distinct := by
    intro a a' haa
    induction a using Fin.lastCases with
    | last =>
      induction a' using Fin.lastCases with
      | last => rfl
      | cast a' => simp at haa; exact absurd haa.symm (h.fresh a')
    | cast a =>
      induction a' using Fin.lastCases with
      | last => simp at haa; exact absurd haa (h.fresh a)
      | cast a' => simp at haa; rw [I.distinct haa]
  removedNonempty := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.removedNonempty
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.removedNonempty a
  removedSize := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.removedSize
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.removedSize a
  removedLocal := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.removedLocal
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.removedLocal a
  haloOverlap := h.haloOverlap
  metric := fun a => by
    induction a using Fin.lastCases with
    | last => simpa using h.metric
    | cast a => simpa using I.metric a
  resolventDecay := fun a => by
    induction a using Fin.lastCases with
    | last => simpa using h.resolventDecay
    | cast a => simpa using I.resolventDecay a
  initialComparison := by
    rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact I.initialComparison
  initialRows := by
    rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact I.initialRows
  initialLag := by
    rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact I.initialLag
  entryChange := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.entryChange
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.entryChange a
  rowChange := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.rowChange
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.rowChange a
  totalChange := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.totalChange
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.totalChange a
  decay := fun a => by
    induction a using Fin.lastCases with
    | last => simpa [Fin.succ_last] using h.decay
    | cast a => rw [Fin.succ_castSucc]; simp only [Fin.snoc_castSucc]; exact I.decay a

theorem assemblySnoc_state_zero {k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (s' : Endpoint (Torus d m)) (y : Torus d m)
    (h : ClearingStepFacts I s' y) : (assemblySnoc I s' y h).state 0 = I.state 0 := by
  show Fin.snoc (α := fun _ => Endpoint (Torus d m)) I.state s' 0 = I.state 0
  rw [← Fin.castSucc_zero, Fin.snoc_castSucc]

theorem assemblySnoc_state_last {k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (s' : Endpoint (Torus d m)) (y : Torus d m)
    (h : ClearingStepFacts I s' y) : (assemblySnoc I s' y h).state (Fin.last (k + 1)) = s' := by
  show Fin.snoc (α := fun _ => Endpoint (Torus d m)) I.state s' (Fin.last (k + 1)) = s'
  rw [Fin.snoc_last]

/-- **A block that keeps the endpoint and the damping keeps the clearing-phase data**
(FAIL exits restore the record; empty blocks). -/
def ClearPhaseData.transfer {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} {j : ℕ}
    {x : RunRecord d m} (D : ClearPhaseData n₀ u E ρ C CA cA PA j x) (y : RunRecord d m)
    (he : y.endpoint = x.endpoint) (hr : y.r = x.r) : ClearPhaseData n₀ u E ρ C CA cA PA j y where
  old := D.old
  rOld := D.rOld
  k := D.k
  I := D.I
  hist := D.hist
  sweep := D.sweep
  last := D.last.trans he.symm
  frozen := hr.trans D.frozen
  constC := D.constC
  constc := D.constc
  constP := D.constP

/-- **A committed clearing with its step facts keeps the clearing-phase data** (DONE). -/
def ClearPhaseData.snoc {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} {j : ℕ}
    {x : RunRecord d m} (D : ClearPhaseData n₀ u E ρ C CA cA PA j x) (y : RunRecord d m)
    (z : Torus d m) (h : ClearingStepFacts D.I y.endpoint z) (hr : y.r = x.r) :
    ClearPhaseData n₀ u E ρ C CA cA PA j y where
  old := D.old
  rOld := D.rOld
  k := D.k + 1
  I := assemblySnoc D.I y.endpoint z h
  hist := D.hist
  sweep := by rw [assemblySnoc_state_zero]; exact D.sweep
  last := assemblySnoc_state_last _ _ _ _
  frozen := hr.trans D.frozen
  constC := D.constC
  constc := D.constc
  constP := D.constP

/-- The predicate form for blocks keeping the endpoint and the damping. -/
theorem ClearPhase.transfer {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} {j : ℕ}
    {x y : RunRecord d m} (hx : ClearPhase n₀ u E ρ C CA cA PA j x)
    (habort : y.aborted = false → x.aborted = false)
    (he : y.aborted = false → y.endpoint = x.endpoint ∧ y.r = x.r) :
    ClearPhase n₀ u E ρ C CA cA PA j y := fun hy =>
  ⟨(hx (habort hy)).some.transfer y (he hy).1 (he hy).2⟩

/-- **A clearing exit keeps the clearing-phase invariant** when it keeps the damping and either
keeps the endpoint (FAIL, empty block) or commits one clearing with its step facts (DONE). -/
theorem ClearPhase.of_exit {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C CA cA PA : ℝ} {j : ℕ}
    {x y : RunRecord d m} (hx : ClearPhase n₀ u E ρ C CA cA PA j x)
    (habort : y.aborted = false → x.aborted = false)
    (hr : y.aborted = false → y.r = x.r)
    (hcase : y.aborted = false → ∀ D : ClearPhaseData n₀ u E ρ C CA cA PA j x,
      y.endpoint = x.endpoint ∨ ∃ z, ClearingStepFacts D.I y.endpoint z) :
    ClearPhase n₀ u E ρ C CA cA PA j y := fun hy => by
  obtain ⟨D⟩ := hx (habort hy)
  rcases hcase hy D with he | ⟨z, hz⟩
  · exact ⟨D.transfer y he (hr hy)⟩
  · exact ⟨D.snoc y z hz (hr hy)⟩

end AndersonAC.AgentS78
