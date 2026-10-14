import AndersonAC.AgentS78.Construction.StagePhaseReset

/-!
# measurability of the active-block reset

This module isolates active-block reset measurability from `StagePhaseOpMeas.lean`.

`resetMapA t x` is, definitionally, `resetFixedA t x.endpoint.active x`, where
`resetFixedA t A` performs the active-block reset on a *fixed* finset `A`. Each `resetFixedA t A`
is measurable through the record code (submatrix, the measurable Picard correction, the
measurable inverse, zero padding); the finitely many cases are glued along the measurable
fibers `{x | x.endpoint.active = A}`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Measurability by cases on a countable key with measurable fibers. -/
theorem measurable_of_countable_cases {α β κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable κ] (k : α → κ) (hk : ∀ i, MeasurableSet {x | k x = i}) (G : κ → α → β)
    (hG : ∀ i, Measurable (G i)) : Measurable (fun x => G (k x) x) := by
  intro s hs
  have hpre : (fun x => G (k x) x) ⁻¹' s = ⋃ i, {x | k x = i} ∩ G i ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨k x, rfl, h⟩
    · rintro ⟨i, rfl, h⟩; exact h
  rw [hpre]
  exact MeasurableSet.iUnion fun i => (hk i).inter (hG i hs)

section Pad

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurable_padM (A : Finset ι) : Measurable (padM (ι := ι) A) := by
  apply measurable_matrix_of_entries
  intro i j
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · simp only [padM, hi, hj, dite_true]
      exact measurable_matrix_entry id measurable_id _ _
    · simp only [padM, hi, hj, dite_true, dite_false]
      exact measurable_const
  · simp only [padM, hi, dite_false]
    exact measurable_const

omit [Fintype ι] in
theorem measurable_padV (A : Finset ι) : Measurable (padV (ι := ι) A) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ∈ A
  · simp only [padV, hi, dite_true]
    exact measurable_pi_apply _
  · simp only [padV, hi, dite_false]
    exact measurable_const

end Pad

variable {d m : ℕ}

/-- The active-block reset on a fixed finset `A` (`resetMapA` with `A` in place of the
record's own active set). -/
def resetFixedA (t : ℝ) (A : Finset (Torus d m)) (x : RunRecord d m) : RunRecord d m :=
  { x with
    r := x.r + padV A (resetCorrection t
      (x.endpoint.M.submatrix (fun a : A => a.val) (fun a : A => a.val),
        fun a : A => x.r a.val))
    endpoint :=
      { active := x.endpoint.active
        M := x.endpoint.M
        g := padM A (resetInverse (x.endpoint.M.submatrix (fun a : A => a.val)
          (fun a : A => a.val)) ((fun a : A => x.r a.val) + resetCorrection t
            (x.endpoint.M.submatrix (fun a : A => a.val) (fun a : A => a.val),
              fun a : A => x.r a.val)) t) } }

theorem resetMapA_eq_resetFixedA (t : ℝ) (x : RunRecord d m) :
    resetMapA t x = resetFixedA t x.endpoint.active x := rfl

/-- Code transformation for `resetFixedA t A`. -/
def resetFixedACode (t : ℝ) (A : Finset (Torus d m)) (c : ResetRecordCode d m) :
    ResetRecordCode d m :=
  (c.1, (c.2.1.1, c.2.1.2.1,
    padM A (resetInverse (c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val))
      ((fun a : A => c.2.1.2.2.2 a.val) + resetCorrection t
        (c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val),
          fun a : A => c.2.1.2.2.2 a.val)) t),
    c.2.1.2.2.2 + padV A (resetCorrection t
      (c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val),
        fun a : A => c.2.1.2.2.2 a.val))),
    c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2)

theorem resetFixedA_code (t : ℝ) (A : Finset (Torus d m)) (x : RunRecord d m) :
    RunRecord.code (resetFixedA t A x) = resetFixedACode t A (RunRecord.code x) := rfl

theorem measurable_resetFixedACode (t : ℝ) (A : Finset (Torus d m)) :
    Measurable (resetFixedACode (d := d) (m := m) t A) := by
  have hM : Measurable (fun c : ResetRecordCode d m => c.2.1.2.1) := by fun_prop
  have hr : Measurable (fun c : ResetRecordCode d m => c.2.1.2.2.2) := by fun_prop
  have hMA : Measurable (fun c : ResetRecordCode d m =>
      c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val)) := by
    apply measurable_matrix_of_entries
    intro a b
    exact measurable_matrix_entry _ hM a.val b.val
  have hrA : Measurable (fun c : ResetRecordCode d m => fun a : A => c.2.1.2.2.2 a.val) := by
    rw [measurable_pi_iff]
    intro a
    exact (measurable_pi_apply a.val).comp hr
  have hζ : Measurable (fun c : ResetRecordCode d m => resetCorrection t
      (c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val),
        fun a : A => c.2.1.2.2.2 a.val)) :=
    (measurable_resetCorrection (ι := A) t).comp (hMA.prodMk hrA)
  have hg : Measurable (fun c : ResetRecordCode d m =>
      padM A (resetInverse (c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val))
        ((fun a : A => c.2.1.2.2.2 a.val) + resetCorrection t
          (c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val),
            fun a : A => c.2.1.2.2.2 a.val)) t)) :=
    (measurable_padM A).comp (measurable_resetInverse_map t _ _ hMA (hrA.add hζ))
  have hr' : Measurable (fun c : ResetRecordCode d m =>
      c.2.1.2.2.2 + padV A (resetCorrection t
        (c.2.1.2.1.submatrix (fun a : A => a.val) (fun a : A => a.val),
          fun a : A => c.2.1.2.2.2 a.val))) :=
    hr.add ((measurable_padV A).comp hζ)
  exact measurable_fst.prodMk
    (((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
      (hM.prodMk (hg.prodMk hr'))).prodMk (measurable_snd.comp measurable_snd))

theorem measurable_resetFixedA (t : ℝ) (A : Finset (Torus d m)) :
    Measurable (resetFixedA (d := d) (m := m) t A) :=
  RunRecord.measurable_reset_of_code (resetFixedA t A) (resetFixedACode t A)
    (resetFixedA_code t A) (measurable_resetFixedACode t A)

theorem measurableSet_active_eq (A : Finset (Torus d m)) :
    MeasurableSet {x : RunRecord d m | x.endpoint.active = A} := by
  have hc : Measurable (fun x : RunRecord d m => finsetCode x.endpoint.active) := by
    have hp : Measurable (fun c : ResetRecordCode d m => c.2.1.1) := by fun_prop
    exact hp.comp (measurable_runRecordCode d m)
  have hset : {x : RunRecord d m | x.endpoint.active = A} =
      (fun x : RunRecord d m => finsetCode x.endpoint.active) ⁻¹' {finsetCode A} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h ▸ rfl, fun h => finsetCode_injective h⟩
  rw [hset]
  exact hc (measurableSet_singleton _)

/-- **The active-block reset is measurable.** -/
theorem resetMapA_measurable (t : ℝ) : Measurable (resetMapA (d := d) (m := m) t) := by
  have h : resetMapA (d := d) (m := m) t =
      fun x => resetFixedA t x.endpoint.active x := rfl
  rw [h]
  exact measurable_of_countable_cases (fun x : RunRecord d m => x.endpoint.active)
    measurableSet_active_eq (resetFixedA t) (measurable_resetFixedA t)

end AndersonAC.AgentS78
