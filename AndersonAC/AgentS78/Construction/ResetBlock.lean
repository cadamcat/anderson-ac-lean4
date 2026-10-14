import AndersonAC.AgentS78.Construction.Record
import AndersonAC.S78.MeasurableReset
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable stage-end updates for the committed record

The ordinary sweep is committed by restricting its final live state to the
reserve ports. A reset uses the fixed point of the Taylor map, selected as
the limit of its Picard iterates when that limit exists and as zero otherwise.
-/

open MeasureTheory
open Filter
open scoped Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S45

variable {d m : ℕ}

/-- The code type used by `RunRecord.code` (kept local to avoid a dependency cycle with
`Transitions`). -/
abbrev ResetRecordCode (d m : ℕ) :=
  ℕ × ((Torus d m → Bool) × Matrix (Torus d m) (Torus d m) ℂ × Matrix (Torus d m) (Torus d m) ℂ ×
    (Torus d m → ℂ)) ×
  (ℕ × (ℕ → initialPorts (Torus d m) → Bool) × (ℕ → CMat (initialPorts (Torus d m))) ×
    (ℕ → initialPorts (Torus d m) → Bool) × (ℕ → ℝ)) ×
  ((Torus d m → ℝ) × (Torus d m → ℕ)) ×
  ((Torus d m → Bool) × (Torus d m → Bool) × (Torus d m → ℕ × Bool × (Torus d m → Bool))) ×
  (Finset (Torus d m) → Bool) × Bool

/-- Measurability follows directly from the record's coordinate encoding. -/
theorem RunRecord.measurable_reset_of_code (f : RunRecord d m → RunRecord d m)
    (G : ResetRecordCode d m → ResetRecordCode d m)
    (hcode : ∀ x, RunRecord.code (f x) = G (RunRecord.code x))
    (hG : Measurable G) : Measurable f := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨G ⁻¹' t, hG ht, ?_⟩
  ext x
  simp only [Set.mem_preimage, hcode]

theorem measurable_runRecordCode (d m : ℕ) :
    Measurable (RunRecord.code (d := d) (m := m)) := RunRecord.measurable_code d m

theorem measurable_runRecord_stage : Measurable (fun x : RunRecord d m => x.stage) := by
  exact measurable_fst.comp (measurable_runRecordCode d m)

theorem measurable_runRecord_endpointM :
    Measurable (fun x : RunRecord d m => x.endpoint.M) := by
  have hp : Measurable (fun c : ResetRecordCode d m => c.2.1.2.1) := by fun_prop
  exact hp.comp (measurable_runRecordCode d m)

theorem measurable_runRecord_endpointG :
    Measurable (fun x : RunRecord d m => x.endpoint.g) := by
  have hp : Measurable (fun c : ResetRecordCode d m => c.2.1.2.2.1) := by fun_prop
  exact hp.comp (measurable_runRecordCode d m)

theorem measurable_runRecord_r : Measurable (fun x : RunRecord d m => x.r) := by
  have hp : Measurable (fun c : ResetRecordCode d m => c.2.1.2.2.2) := by fun_prop
  exact hp.comp (measurable_runRecordCode d m)

theorem measurable_runRecord_sweepLength :
    Measurable (fun x : RunRecord d m => x.sweep.length) := by
  have hp : Measurable (fun c : ResetRecordCode d m => c.2.2.1.1) := by fun_prop
  exact hp.comp (measurable_runRecordCode d m)

theorem measurable_runRecord_sweepG (k : ℕ) :
    Measurable (fun x : RunRecord d m => (x.sweep.state k).g) := by
  have hp : Measurable (fun c : ResetRecordCode d m => c.2.2.1.2.2.1 k) := by fun_prop
  exact hp.comp (measurable_runRecordCode d m)

/-- Parameters on which the reset fixed point depends. -/
abbrev ResetParameters (ι : Type) := Matrix ι ι ℂ × (ι → ℂ)

/-- The Taylor fixed-point map used by Proposition 7.4. -/
def resetTransform {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (p : ResetParameters ι) (z : ι → ℂ) : ι → ℂ :=
  let K : Matrix ι ι ℂ := squareKernel ((Real.sqrt t : ℂ) • resetInverse (ι := ι) p.1 p.2 t)
  ((1 - K)⁻¹).mulVec (fun i : ι =>
    resetInverse (ι := ι) p.1 (p.2 + z) t i i - p.2 i - (K.mulVec z) i)

theorem measurable_matrixInverse {α : Type*} [MeasurableSpace α]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : α → Matrix ι ι ℂ) (hA : Measurable A) :
    Measurable (fun x => (A x)⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  fun_prop

theorem measurable_matrix_entry {α : Type*} [MeasurableSpace α]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : α → Matrix ι ι ℂ) (hA : Measurable A) (i j : ι) :
    Measurable (fun x => A x i j) := by
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)

theorem measurable_matrix_of_entries {α : Type*} [MeasurableSpace α]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : α → Matrix ι ι ℂ)
    (hA : ∀ i j, Measurable (fun x => A x i j)) : Measurable A := by
  exact Measurable.of_eval_matrix A hA

theorem measurable_resetInverse_map {α : Type*} [MeasurableSpace α]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (M : α → Matrix ι ι ℂ) (r : α → ι → ℂ)
    (hM : Measurable M) (hr : Measurable r) :
    Measurable (fun x => resetInverse (ι := ι) (M x) (r x) t) := by
  have hA : Measurable (fun x => M x - (t : ℂ) • Matrix.diagonal (r x)) := by
    apply measurable_matrix_of_entries
    intro i j
    have hMij := measurable_matrix_entry M hM i j
    have hri := (measurable_pi_apply i).comp hr
    by_cases hij : i = j
    · subst j
      have hscale : Measurable (fun x : α => (t : ℂ) * r x i) :=
        (measurable_const : Measurable (fun _ : α => (t : ℂ))).mul hri
      have hentry : Measurable (fun x : α => M x i i - (t : ℂ) * r x i) := hMij.sub hscale
      convert hentry using 1
      ext x
      simp [Matrix.diagonal_apply]
    · have hentry : Measurable (fun x : α => M x i j) := hMij
      convert hentry using 1
      ext x
      simp [Matrix.diagonal_apply, hij]
  exact measurable_matrixInverse _ hA

theorem measurable_resetTransform_joint {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) : Measurable (fun q : ResetParameters ι × (ι → ℂ) => resetTransform t q.1 q.2) := by
  let A : ResetParameters ι × (ι → ℂ) → Matrix ι ι ℂ := fun q =>
    resetInverse (ι := ι) q.1.1 q.1.2 t
  let B : ResetParameters ι × (ι → ℂ) → Matrix ι ι ℂ := fun q =>
    resetInverse (ι := ι) q.1.1 (q.1.2 + q.2) t
  let K : ResetParameters ι × (ι → ℂ) → Matrix ι ι ℂ := fun q =>
    squareKernel ((Real.sqrt t : ℂ) • A q)
  let P : ResetParameters ι × (ι → ℂ) → Matrix ι ι ℂ := fun q => (1 - K q)⁻¹
  let v : ResetParameters ι × (ι → ℂ) → (ι → ℂ) := fun q i =>
    B q i i - q.1.2 i - (Matrix.mulVec (K q) q.2) i
  have hM : Measurable (fun q : ResetParameters ι × (ι → ℂ) => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hr : Measurable (fun q : ResetParameters ι × (ι → ℂ) => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hz : Measurable (fun q : ResetParameters ι × (ι → ℂ) => q.2) := measurable_snd
  have hrz : Measurable (fun q : ResetParameters ι × (ι → ℂ) => q.1.2 + q.2) := hr.add hz
  have hA : Measurable A := measurable_resetInverse_map t _ _ hM hr
  have hB : Measurable B := measurable_resetInverse_map t _ _ hM hrz
  have hscaled : Measurable (fun q => (Real.sqrt t : ℂ) • A q) := by
    apply measurable_matrix_of_entries
    intro i j
    have hAij := measurable_matrix_entry A hA i j
    change Measurable (fun q => (Real.sqrt t : ℂ) * A q i j)
    exact (measurable_const : Measurable (fun _ : ResetParameters ι × (ι → ℂ) =>
      (Real.sqrt t : ℂ))).mul hAij
  have hsquare : Continuous (fun M : Matrix ι ι ℂ => squareKernel M) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun M : Matrix ι ι ℂ => (M i j) ^ 2)
    fun_prop
  have hK : Measurable K := by
    dsimp [K]
    exact hsquare.measurable.comp hscaled
  have hPm : Measurable (fun q => (1 : Matrix ι ι ℂ) - K q) := by
    apply measurable_matrix_of_entries
    intro i j
    have hKij := measurable_matrix_entry K hK i j
    by_cases hij : i = j
    · subst j
      have hentry : Measurable (fun q : ResetParameters ι × (ι → ℂ) => (1 : ℂ) - K q i i) :=
        (measurable_const : Measurable (fun _ : ResetParameters ι × (ι → ℂ) => (1 : ℂ))).sub hKij
      convert hentry using 1
      ext q
      simp [Matrix.one_apply]
    · have hentry : Measurable (fun q : ResetParameters ι × (ι → ℂ) => (0 : ℂ) - K q i j) :=
        (measurable_const : Measurable (fun _ : ResetParameters ι × (ι → ℂ) => (0 : ℂ))).sub hKij
      convert hentry using 1
      ext q
      simp [Matrix.one_apply, hij]
  have hP : Measurable P := by
    dsimp [P]
    exact measurable_matrixInverse _ hPm
  have hdiag : Continuous (fun M : Matrix ι ι ℂ => fun i : ι => M i i) := by fun_prop
  have hdiagB : Measurable (fun q => fun i : ι => B q i i) := hdiag.measurable.comp hB
  have hKpair : Measurable (fun q => (K q, q.2)) := hK.prodMk hz
  have hmulVec : Continuous (fun q : Matrix ι ι ℂ × (ι → ℂ) => q.1.mulVec q.2) := by fun_prop
  have hKz : Measurable (fun q => Matrix.mulVec (K q) q.2) := hmulVec.measurable.comp hKpair
  have hv : Measurable v := by
    rw [measurable_pi_iff]
    intro i
    have hBii := (measurable_pi_apply i).comp hdiagB
    have hri := (measurable_pi_apply i).comp hr
    have hKzi := (measurable_pi_apply i).comp hKz
    dsimp [v]
    exact (hBii.sub hri).sub hKzi
  have hpair : Measurable (fun q => (P q, v q)) := hP.prodMk hv
  have hmul : Continuous (fun q : Matrix ι ι ℂ × (ι → ℂ) => q.1.mulVec q.2) := by fun_prop
  change Measurable (fun q => (P q).mulVec (v q))
  exact hmul.measurable.comp hpair

/-- The `n`th Picard iterate from zero. -/
def resetPicard {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (p : ResetParameters ι) (n : ℕ) : ι → ℂ :=
  (resetTransform t p)^[n] 0

theorem measurable_resetPicard {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (n : ℕ) : Measurable (fun p : ResetParameters ι => resetPicard t p n) := by
  induction n with
  | zero => simp [resetPicard]
  | succ n ih =>
      simpa only [resetPicard, Function.iterate_succ_apply', Function.comp_def,
        Function.uncurry, id_eq] using
        (measurable_resetTransform_joint t).comp (measurable_id.prodMk ih)

/-- The correction is the Picard limit when it exists, and zero otherwise. -/
def resetPicardConverges {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (p : ResetParameters ι) : Prop :=
  ∃ z, Tendsto (fun n => resetPicard t p n) atTop (𝓝 z)

def resetCorrection {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (p : ResetParameters ι) : ι → ℂ := by
  classical
  exact if h : resetPicardConverges t p
    then Classical.choose h else 0

theorem resetCorrection_tendsto {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (p : ResetParameters ι)
    (h : resetPicardConverges t p) :
    Tendsto (fun n => resetPicard t p n) atTop (𝓝 (resetCorrection t p)) := by
  simp only [resetCorrection, dif_pos h]
  exact Classical.choose_spec h

theorem measurable_resetCorrection {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) : Measurable (resetCorrection (ι := ι) t) := by
  classical
  let C : Set (ResetParameters ι) := {p | resetPicardConverges t p}
  have hC : MeasurableSet C := by
    dsimp [C]
    exact measurableSet_exists_tendsto (fun n => measurable_resetPicard t n)
  let f : ℕ → ResetParameters ι → (ι → ℂ) := fun n p =>
    if p ∈ C then resetPicard t p n else 0
  have hf : ∀ n, Measurable (f n) := by
    intro n
    exact Measurable.ite hC (measurable_resetPicard t n) measurable_const
  have hlim : Tendsto f atTop (𝓝 (resetCorrection t)) := by
    rw [tendsto_pi_nhds]
    intro p
    by_cases hp : resetPicardConverges t p
    · have hseq := resetCorrection_tendsto t p hp
      have hf' : (fun n => f n p) = fun n => resetPicard t p n := by
        funext n
        simp [f, C, hp]
      rw [hf']
      simpa [resetCorrection, hp] using hseq
    · have hf' : (fun n => f n p) = fun _ => (0 : ι → ℂ) := by
        funext n
        simp [f, C, hp]
      rw [hf']
      simp [resetCorrection, hp]
  exact measurable_of_tendsto_metrizable hf hlim

/-- Under the ball and contraction hypotheses, the selected Picard limit is the fixed point. -/
theorem resetCorrection_fixedPoint {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (ht : 0 ≤ t) (p : ResetParameters ι)
    (hball : ∀ z, ‖z‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) →
    ‖resetTransform t p z‖ ≤ t ^ (0.35 * AndersonAC.S78.delta))
    (hcontract : ∀ z w, ‖z‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) → ‖w‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) →
      ‖resetTransform t p z - resetTransform t p w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖) :
    ‖resetCorrection t p‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) ∧
      resetTransform t p (resetCorrection t p) = resetCorrection t p := by
  have hρ : 0 ≤ t ^ (0.35 * AndersonAC.S78.delta) :=
    Real.rpow_nonneg ht _
  obtain ⟨z, hz, hfix, hlim⟩ :=
    AndersonAC.SolS78.fixedPoint_closedBall_with_iterates (resetTransform t p) 0
      (t ^ (0.35 * AndersonAC.S78.delta)) hρ (by simpa using hball) (by simpa using hcontract)
  have hhas : resetPicardConverges t p := by
    exact ⟨z, hlim⟩
  have hζlim := resetCorrection_tendsto t p hhas
  have hζ : resetCorrection t p = z := tendsto_nhds_unique hζlim hlim
  constructor
  · simpa [hζ] using hz
  · rw [hζ]
    exact hfix


/-- Measurable evaluation when the index is a countable discrete coordinate. -/
theorem measurable_eval_countable {α β : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] [MeasurableSpace β] :
    Measurable (fun p : α × (α → β) => p.2 p.1) := by
  intro s hs
  have heq : {p : α × (α → β) | p.2 p.1 ∈ s} =
      ⋃ a, {p : α × (α → β) | p.1 = a} ∩ {p | p.2 a ∈ s} := by
    ext ⟨a, f⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨a, rfl, h⟩
    · rintro ⟨b, hab, hb⟩
      cases hab
      exact hb
  change MeasurableSet {p : α × (α → β) | p.2 p.1 ∈ s}
  rw [heq]
  exact MeasurableSet.iUnion fun a =>
    (MeasurableSet.preimage (measurableSet_singleton a) measurable_fst).inter
      (hs.preimage ((measurable_pi_apply a).comp measurable_snd))

/-- The ratio of adjacent stage scales; the common base scale cancels. -/
def resetSweepTheta (j m : ℕ) : ℝ :=
  stageScale 1 (j + 1) m / stageScale 1 j m

/-- The ordinary sweep's final live ports, encoded as a physical active set. -/
def sweepEndActive {d m : ℕ} (x : RunRecord d m) : Finset (Torus d m) :=
  by
    classical
    exact Finset.univ.filter fun i => (i, true) ∈ (x.sweep.state x.sweep.length).live

/-- The reserve restriction and S45 normalization for an explicit split ratio. -/
def sweepEndMatrixTheta {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  fun i k =>
    if i ∈ sweepEndActive x ∧ k ∈ sweepEndActive x then
      (x.sweep.state x.sweep.length).g (i, true) (k, true) /
        (Real.sqrt θ : ℂ)
    else 0

/-- The digit-sweep split ratio is the ratio of adjacent stage scales. -/
def sweepEndMatrix {d m : ℕ} (j : ℕ) (x : RunRecord d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  sweepEndMatrixTheta (resetSweepTheta j m) x

open Classical in
/-- The physical increment installed at site `i` by a sweep (04:198–228): deleting the bit
port `(i, false)` with port scalar `ξ` installs `ζ = √w ξ`, `w = 1 − θ` (TileBlock.scalarStep
stores `ξ = ζ / √w`). Summed over the steps of the sweep whose pivot is that bit port.
The sweep records this increment in `endpoint.M`. -/
def sweepIncrement {d m : ℕ} (θ : ℝ) (q : Sequence (initialPorts (Torus d m)))
    (i : Torus d m) : ℝ :=
  Real.sqrt (1 - θ) *
    ∑ k ∈ Finset.range q.length, if q.pivot k = some ((i, false) : initialPorts (Torus d m)) then q.scalar k else 0

/-- The committed Schur matrix after a sweep: the stage-start `M` plus the diagonal of the
physical increments installed during the sweep, so that `g_new = (M_new − θ t r)⁻¹` on the
active sites (04:198–228, 02-state.tex:231–247) and `PhysicalIdentity` is kept. -/
def sweepEndMTheta {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  x.endpoint.M + Matrix.diagonal (fun i => ((sweepIncrement θ x.sweep i : ℝ) : ℂ))

/-- The empty sequence installed after its endpoint has been committed. -/
def emptyRunSweep {d m : ℕ} : Sequence (initialPorts (Torus d m)) where
  length := 0
  state := fun _ => ⟨∅, 0⟩
  pivot := fun _ => none
  scalar := fun _ => 0

/-- Commit a completed sweep at an explicit split ratio and clear the sweep buffer. -/
def sweepEndMapTheta {d m : ℕ} (θ : ℝ) (x : RunRecord d m) : RunRecord d m :=
  { x with
    endpoint := { active := sweepEndActive x
                  M := sweepEndMTheta θ x
                  g := sweepEndMatrixTheta θ x }
    sweep := emptyRunSweep }

/-- Digit-sweep endpoint commit using the adjacent stage-scale ratio. -/
def sweepEndMap {d m : ℕ} (j : ℕ) (x : RunRecord d m) : RunRecord d m :=
  sweepEndMapTheta (resetSweepTheta j m) x

theorem sweepEndMap_eq_sweepEndMapTheta {d m : ℕ} (j : ℕ) (x : RunRecord d m) :
    sweepEndMap j x = sweepEndMapTheta (resetSweepTheta j m) x := rfl

/-- The reserve-port live state in a RunRecord.code, evaluated at the encoded length. -/
def sweepCodeFinalLive {d m : ℕ} (c : ResetRecordCode d m) :
    initialPorts (Torus d m) → Bool :=
  (c.2.2.1.2.1) c.2.2.1.1

/-- The final sweep matrix in the record code. -/
def sweepCodeFinalMatrix {d m : ℕ} (c : ResetRecordCode d m) :
    Matrix (initialPorts (Torus d m)) (initialPorts (Torus d m)) ℂ :=
  (c.2.2.1.2.2.1) c.2.2.1.1

/-- Code for the active physical sites after restricting to the true reserve port. -/
def sweepCodeActive {d m : ℕ} (c : ResetRecordCode d m) : Torus d m → Bool :=
  fun i => sweepCodeFinalLive c (i, true)

/-- Code for the endpoint Green matrix after reserve restriction at explicit θ. -/
def sweepCodeMatrixTheta {d m : ℕ} (θ : ℝ) (c : ResetRecordCode d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  fun i k => if sweepCodeFinalLive c (i, true) = true ∧ sweepCodeFinalLive c (k, true) = true then
    sweepCodeFinalMatrix c (i, true) (k, true) /
      (Real.sqrt θ : ℂ) else 0

/-- Code for the digit-sweep endpoint matrix. -/
def sweepCodeMatrix {d m : ℕ} (j : ℕ) (c : ResetRecordCode d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  sweepCodeMatrixTheta (resetSweepTheta j m) c

/-- The sweep increment read from the record code (length, pivot code, scalars). -/
def sweepCodeIncrementLen {d m : ℕ} (θ : ℝ) (c : ResetRecordCode d m) (n : ℕ)
    (i : Torus d m) : ℝ :=
  Real.sqrt (1 - θ) *
    ∑ k ∈ Finset.range n, if c.2.2.1.2.2.2.1 k ((i, false) : initialPorts (Torus d m)) = true then c.2.2.1.2.2.2.2 k else 0

/-- The sweep increment at the encoded length. -/
def sweepCodeIncrement {d m : ℕ} (θ : ℝ) (c : ResetRecordCode d m) (i : Torus d m) : ℝ :=
  sweepCodeIncrementLen θ c c.2.2.1.1 i

/-- The committed Schur matrix after the sweep, from the record code. -/
def sweepCodeMTheta {d m : ℕ} (θ : ℝ) (c : ResetRecordCode d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  c.2.1.2.1 + Matrix.diagonal (fun i => ((sweepCodeIncrement θ c i : ℝ) : ℂ))

/-- Code transformation for the sweep-end map at explicit θ. -/
def sweepEndCodeMapTheta {d m : ℕ} (θ : ℝ) (c : ResetRecordCode d m) : ResetRecordCode d m :=
  (c.1,
    (sweepCodeActive c, sweepCodeMTheta θ c, sweepCodeMatrixTheta θ c, c.2.1.2.2.2),
    (0, fun _ _ => false, fun _ => 0, fun _ _ => false, fun _ => 0),
    c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2)

/-- Code transformation for the digit-sweep endpoint commit. -/
def sweepEndCodeMap {d m : ℕ} (j : ℕ) (c : ResetRecordCode d m) : ResetRecordCode d m :=
  sweepEndCodeMapTheta (resetSweepTheta j m) c

theorem measurable_sweepCodeFinalLive {d m : ℕ} :
    Measurable (sweepCodeFinalLive (d := d) (m := m)) := by
  have hinput : Measurable (fun c : ResetRecordCode d m =>
      (c.2.2.1.1, c.2.2.1.2.1)) := by fun_prop
  exact measurable_eval_countable.comp hinput

theorem measurable_sweepCodeFinalMatrix {d m : ℕ} :
    Measurable (sweepCodeFinalMatrix (d := d) (m := m)) := by
  have hinput : Measurable (fun c : ResetRecordCode d m =>
      (c.2.2.1.1, c.2.2.1.2.2.1)) := by fun_prop
  exact measurable_eval_countable.comp hinput

theorem measurable_sweepCodeActive {d m : ℕ} :
    Measurable (sweepCodeActive (d := d) (m := m)) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply (i, true)).comp measurable_sweepCodeFinalLive

theorem measurable_sweepCodeMatrixTheta {d m : ℕ} (θ : ℝ) :
    Measurable (sweepCodeMatrixTheta (d := d) (m := m) θ) := by
  apply Measurable.of_eval_matrix
  intro i k
  have hLive := measurable_sweepCodeFinalLive (d := d) (m := m)
  have hLiveI : Measurable (fun c : ResetRecordCode d m => sweepCodeFinalLive c (i, true)) :=
    (measurable_pi_apply (i, true)).comp hLive
  have hLiveK : Measurable (fun c : ResetRecordCode d m => sweepCodeFinalLive c (k, true)) :=
    (measurable_pi_apply (k, true)).comp hLive
  have hcond : MeasurableSet {c : ResetRecordCode d m |
      sweepCodeFinalLive c (i, true) = true ∧ sweepCodeFinalLive c (k, true) = true} := by
    exact ((measurable_pi_apply (i, true)).comp hLive
      (measurableSet_singleton true)).inter
      ((measurable_pi_apply (k, true)).comp hLive (measurableSet_singleton true))
  have hentry : Measurable (fun c : ResetRecordCode d m =>
      sweepCodeFinalMatrix c (i, true) (k, true) /
        (Real.sqrt θ : ℂ)) := by
    have hmatrix := measurable_sweepCodeFinalMatrix (d := d) (m := m)
    have hij := measurable_matrix_entry _ hmatrix (i, true) (k, true)
    exact hij.div_const _
  exact Measurable.ite hcond hentry measurable_const

theorem measurable_sweepCodeMatrix {d m : ℕ} (j : ℕ) :
    Measurable (sweepCodeMatrix (d := d) (m := m) j) := by
  exact measurable_sweepCodeMatrixTheta (resetSweepTheta j m)

theorem measurable_sweepCodeIncrement {d m : ℕ} (θ : ℝ) (i : Torus d m) :
    Measurable (fun c : ResetRecordCode d m => sweepCodeIncrement θ c i) := by
  have hlen : ∀ n, Measurable (fun c : ResetRecordCode d m => sweepCodeIncrementLen θ c n i) := by
    intro n
    unfold sweepCodeIncrementLen
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    have hpiv : Measurable (fun c : ResetRecordCode d m => c.2.2.1.2.2.2.1 k (i, false)) :=
      (measurable_pi_apply (i, false)).comp ((measurable_pi_apply k).comp (by fun_prop))
    have hsc : Measurable (fun c : ResetRecordCode d m => c.2.2.1.2.2.2.2 k) :=
      (measurable_pi_apply k).comp (by fun_prop)
    exact Measurable.ite (hpiv (measurableSet_singleton true)) hsc measurable_const
  have hfun : Measurable (fun c : ResetRecordCode d m =>
      (c.2.2.1.1, fun n : ℕ => sweepCodeIncrementLen θ c n i)) :=
    (by fun_prop : Measurable (fun c : ResetRecordCode d m => c.2.2.1.1)).prodMk
      (Measurable.of_eval hlen)
  exact (measurable_eval_countable (α := ℕ) (β := ℝ)).comp hfun

theorem measurable_sweepCodeMTheta {d m : ℕ} (θ : ℝ) :
    Measurable (sweepCodeMTheta (d := d) (m := m) θ) := by
  apply Measurable.of_eval_matrix
  intro i k
  have hM : Measurable (fun c : ResetRecordCode d m => c.2.1.2.1 i k) :=
    measurable_matrix_entry _ (by fun_prop) i k
  by_cases hik : i = k
  · subst k
    have hinc : Measurable (fun c : ResetRecordCode d m => ((sweepCodeIncrement θ c i : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_sweepCodeIncrement θ i)
    convert hM.add hinc using 1
    ext c
    simp [sweepCodeMTheta]
  · convert hM using 1
    ext c
    simp [sweepCodeMTheta, hik]

theorem sweepIncrement_code {d m : ℕ} (θ : ℝ) (x : RunRecord d m) (i : Torus d m) :
    sweepIncrement θ x.sweep i = sweepCodeIncrement θ (RunRecord.code x) i := by
  classical
  simp only [sweepIncrement, sweepCodeIncrement, sweepCodeIncrementLen, RunRecord.code,
    optionCode, decide_eq_true_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem sweepEndMTheta_code {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    sweepEndMTheta θ x = sweepCodeMTheta θ (RunRecord.code x) := by
  unfold sweepEndMTheta sweepCodeMTheta
  congr 2
  funext i
  rw [sweepIncrement_code]

theorem measurable_sweepEndCodeMapTheta {d m : ℕ} (θ : ℝ) :
    Measurable (sweepEndCodeMapTheta (d := d) (m := m) θ) := by
  have hactive := measurable_sweepCodeActive (d := d) (m := m)
  have hmatrix := measurable_sweepCodeMatrixTheta (d := d) (m := m) θ
  have hM := measurable_sweepCodeMTheta (d := d) (m := m) θ
  change Measurable (fun c : ResetRecordCode d m =>
    (c.1,
      (sweepCodeActive c, sweepCodeMTheta θ c, sweepCodeMatrixTheta θ c, c.2.1.2.2.2),
      (0, fun _ _ => false, fun _ => 0, fun _ _ => false, fun _ => 0),
      c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2))
  fun_prop

theorem measurable_sweepEndCodeMap {d m : ℕ} (j : ℕ) :
    Measurable (sweepEndCodeMap (d := d) (m := m) j) := by
  exact measurable_sweepEndCodeMapTheta (resetSweepTheta j m)

theorem sweepEndActive_code {d m : ℕ} (x : RunRecord d m) :
    finsetCode (sweepEndActive x) = sweepCodeActive (RunRecord.code x) := by
  classical
  funext i
  by_cases h : (i, true) ∈ (x.sweep.state x.sweep.length).live
  · simp [sweepEndActive, sweepCodeActive, sweepCodeFinalLive, RunRecord.code, finsetCode, h] <;> exact h
  · simp [sweepEndActive, sweepCodeActive, sweepCodeFinalLive, RunRecord.code, finsetCode, h] <;> exact h

theorem sweepEndMatrixTheta_code {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    sweepEndMatrixTheta θ x = sweepCodeMatrixTheta θ (RunRecord.code x) := by
  classical
  ext i k
  have hG : sweepCodeFinalMatrix (RunRecord.code x) =
      (x.sweep.state x.sweep.length).g := rfl
  have hmem (y : Torus d m) : y ∈ sweepEndActive x ↔
      sweepCodeFinalLive (RunRecord.code x) (y, true) = true := by
    change y ∈ sweepEndActive x ↔
      finsetCode ((x.sweep.state x.sweep.length).live) (y, true) = true
    simp [sweepEndActive, finsetCode, Finset.mem_filter, Finset.mem_univ] <;> rfl
  by_cases hi : i ∈ sweepEndActive x
  · have hbi : sweepCodeFinalLive (RunRecord.code x) (i, true) = true := (hmem i).mp hi
    by_cases hk : k ∈ sweepEndActive x
    · have hbk : sweepCodeFinalLive (RunRecord.code x) (k, true) = true := (hmem k).mp hk
      simp [sweepEndMatrixTheta, sweepCodeMatrixTheta, hG, hi, hk, hbi, hbk]
    · have hbk : sweepCodeFinalLive (RunRecord.code x) (k, true) ≠ true := by
        intro h
        exact hk ((hmem k).mpr h)
      simp [sweepEndMatrixTheta, sweepCodeMatrixTheta, hG, hi, hk, hbi, hbk]
  · have hbi : sweepCodeFinalLive (RunRecord.code x) (i, true) ≠ true := by
      intro h
      exact hi ((hmem i).mpr h)
    by_cases hk : k ∈ sweepEndActive x
    · have hbk : sweepCodeFinalLive (RunRecord.code x) (k, true) = true := (hmem k).mp hk
      simp [sweepEndMatrixTheta, sweepCodeMatrixTheta, hG, hi, hk, hbi, hbk]
    · have hbk : sweepCodeFinalLive (RunRecord.code x) (k, true) ≠ true := by
        intro h
        exact hk ((hmem k).mpr h)
      simp [sweepEndMatrixTheta, sweepCodeMatrixTheta, hG, hi, hk, hbi, hbk]

theorem sweepEndMatrix_code {d m : ℕ} (j : ℕ) (x : RunRecord d m) :
    sweepEndMatrix j x = sweepCodeMatrix j (RunRecord.code x) :=
  sweepEndMatrixTheta_code (resetSweepTheta j m) x

theorem sweepEndMapTheta_code {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    RunRecord.code (sweepEndMapTheta θ x) =
      sweepEndCodeMapTheta (d := d) (m := m) θ (RunRecord.code x) := by
  have hLive : (fun _ : ℕ => finsetCode (∅ : Finset (initialPorts (Torus d m)))) =
      (fun _ _ => false) := by
    funext k p
    simp [finsetCode]
  have hpivot : (fun _ : ℕ => optionCode (none : Option (initialPorts (Torus d m)))) =
      (fun _ _ => false) := by
    funext k p
    simp [optionCode, emptyRunSweep]
  simp [RunRecord.code, sweepEndMapTheta, sweepEndCodeMapTheta, sweepEndActive_code,
    sweepEndMatrixTheta_code, sweepEndMTheta_code,
    emptyRunSweep, finsetCode, optionCode, hLive, hpivot]

theorem sweepEndMapTheta_endpoint {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    (sweepEndMapTheta θ x).endpoint =
      { active := sweepEndActive x, M := sweepEndMTheta θ x, g := sweepEndMatrixTheta θ x } :=
  rfl

theorem sweepEndMapTheta_M {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    (sweepEndMapTheta θ x).endpoint.M =
      x.endpoint.M + Matrix.diagonal (fun i => ((sweepIncrement θ x.sweep i : ℝ) : ℂ)) :=
  rfl

theorem sweepIncrement_of_length_zero {d m : ℕ} (θ : ℝ)
    (q : Sequence (initialPorts (Torus d m))) (hq : q.length = 0) (i : Torus d m) :
    sweepIncrement θ q i = 0 := by
  simp [sweepIncrement, hq]

theorem sweepEndMap_code {d m : ℕ} (j : ℕ) (x : RunRecord d m) :
    RunRecord.code (sweepEndMap j x) =
      sweepEndCodeMap (d := d) (m := m) j (RunRecord.code x) :=
  sweepEndMapTheta_code (resetSweepTheta j m) x

theorem sweepEndMapTheta_measurable {d m : ℕ} (θ : ℝ) :
    Measurable (sweepEndMapTheta (d := d) (m := m) θ) := by
  apply RunRecord.measurable_reset_of_code (sweepEndMapTheta θ)
    (sweepEndCodeMapTheta (d := d) (m := m) θ) (sweepEndMapTheta_code θ)
  exact measurable_sweepEndCodeMapTheta (d := d) (m := m) θ

theorem sweepEndMap_measurable {d m : ℕ} (j : ℕ) :
    Measurable (sweepEndMap (d := d) (m := m) j) := by
  change Measurable (sweepEndMapTheta (resetSweepTheta j m))
  exact sweepEndMapTheta_measurable (resetSweepTheta j m)



/-- The duplicated live state at the start of a sweep. -/
def sweepStartLiveState {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    LiveState (initialPorts (Torus d m)) := by
  classical
  let physical : State (Torus d m) := ⟨x.endpoint.g, x.r⟩
  exact
    ⟨Finset.univ.filter (fun p : initialPorts (Torus d m) => p.1 ∈ x.endpoint.active),
      ((splitPorts (Torus d m) θ).liftState physical).g⟩

/-- The active-site indicator copied to both ports at sweep start. -/
def sweepStartCodeLive {d m : ℕ} (c : ResetRecordCode d m) :
    initialPorts (Torus d m) → Bool :=
  fun p => c.2.1.1 p.1

/-- The split-port Green matrix at sweep start. -/
def sweepStartCodeMatrix {d m : ℕ} (θ : ℝ) (c : ResetRecordCode d m) :
    Matrix (initialPorts (Torus d m)) (initialPorts (Torus d m)) ℂ :=
  fun p q =>
    ((splitPorts (Torus d m) θ).weight p : ℂ) *
      ((splitPorts (Torus d m) θ).weight q : ℂ) *
        c.2.1.2.2.1 p.1 q.1

/-- Start a sweep with the duplicated physical endpoint and no accepted steps yet.
The t parameter identifies the physical stage scale; the endpoint already stores its
Green matrix at that scale. -/
def sweepStartMap {d m : ℕ} (θ t : ℝ) (x : RunRecord d m) : RunRecord d m :=
  { x with
    sweep :=
      { length := 0
        state := fun _ => sweepStartLiveState θ x
        pivot := fun _ => none
        scalar := fun _ => 0 } }

/-- Code transformation for the stage-start lift. -/
def sweepStartCodeMap {d m : ℕ} (θ t : ℝ) (c : ResetRecordCode d m) :
    ResetRecordCode d m :=
  (c.1, c.2.1,
    (0, fun _ => sweepStartCodeLive c, fun _ => sweepStartCodeMatrix θ c,
      fun _ _ => false, fun _ => 0),
    c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2)

theorem measurable_sweepStartCodeLive {d m : ℕ} :
    Measurable (sweepStartCodeLive (d := d) (m := m)) := by
  have hactive : Measurable (fun c : ResetRecordCode d m => c.2.1.1) := by fun_prop
  apply Measurable.of_eval
  intro p
  exact (measurable_pi_apply p.1).comp hactive

theorem measurable_sweepStartCodeMatrix {d m : ℕ} (θ : ℝ) :
    Measurable (sweepStartCodeMatrix (d := d) (m := m) θ) := by
  have hphysical : Measurable (fun c : ResetRecordCode d m => c.2.1.2.2.1) := by fun_prop
  apply Measurable.of_eval_matrix
  intro p q
  have hentry := measurable_matrix_entry _ hphysical p.1 q.1
  let w : ℂ :=
    ((splitPorts (Torus d m) θ).weight p : ℂ) *
      ((splitPorts (Torus d m) θ).weight q : ℂ)
  exact (measurable_const : Measurable (fun _ : ResetRecordCode d m => w)).mul hentry

theorem measurable_sweepStartCodeMap {d m : ℕ} (θ t : ℝ) :
    Measurable (sweepStartCodeMap (d := d) (m := m) θ t) := by
  have hLive := measurable_sweepStartCodeLive (d := d) (m := m)
  have hMatrix := measurable_sweepStartCodeMatrix (d := d) (m := m) θ
  change Measurable (fun c : ResetRecordCode d m =>
    (c.1, c.2.1,
      (0, fun _ => sweepStartCodeLive c, fun _ => sweepStartCodeMatrix θ c,
        fun _ _ => false, fun _ => 0),
      c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2))
  fun_prop

theorem sweepStartLiveState_code {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    finsetCode (sweepStartLiveState θ x).live =
      sweepStartCodeLive (RunRecord.code x) := by
  funext p
  classical
  by_cases h : p.1 ∈ x.endpoint.active
  · simp [sweepStartLiveState, sweepStartCodeLive, RunRecord.code, finsetCode, h] <;> exact h
  · simp [sweepStartLiveState, sweepStartCodeLive, RunRecord.code, finsetCode, h] <;> exact h

theorem sweepStartLiveState_matrix_code {d m : ℕ} (θ : ℝ) (x : RunRecord d m) :
    (sweepStartLiveState θ x).g = sweepStartCodeMatrix θ (RunRecord.code x) := by
  rfl

theorem sweepStartMap_code {d m : ℕ} (θ t : ℝ) (x : RunRecord d m) :
    RunRecord.code (sweepStartMap θ t x) =
      sweepStartCodeMap θ t (RunRecord.code x) := by
  have hLive : (fun _ : ℕ => finsetCode (sweepStartLiveState θ x).live) =
      (fun _ => sweepStartCodeLive (RunRecord.code x)) := by
    funext _
    exact sweepStartLiveState_code θ x
  have hMatrix : (fun _ : ℕ => (sweepStartLiveState θ x).g) =
      (fun _ => sweepStartCodeMatrix θ (RunRecord.code x)) := by
    funext _
    exact sweepStartLiveState_matrix_code θ x
  have hPivot : (fun _ : ℕ => optionCode (none : Option (initialPorts (Torus d m)))) =
      (fun _ _ => false) := by
    funext _ p
    simp [optionCode]
  simp [RunRecord.code, sweepStartMap, sweepStartCodeMap, sweepStartLiveState_code,
    sweepStartLiveState_matrix_code, hLive, hMatrix, hPivot] <;> rfl

theorem sweepStartMap_measurable {d m : ℕ} (θ t : ℝ) :
    Measurable (sweepStartMap (d := d) (m := m) θ t) := by
  apply RunRecord.measurable_reset_of_code (sweepStartMap θ t)
    (sweepStartCodeMap (d := d) (m := m) θ t) (sweepStartMap_code θ t)
  exact measurable_sweepStartCodeMap (d := d) (m := m) θ t

theorem sweepStartMap_preserves {d m : ℕ} (θ t : ℝ) (x : RunRecord d m) :
    (sweepStartMap θ t x).stage = x.stage ∧
    (sweepStartMap θ t x).endpoint = x.endpoint ∧
    (sweepStartMap θ t x).r = x.r ∧
    (sweepStartMap θ t x).installed = x.installed ∧
    (sweepStartMap θ t x).prefixLength = x.prefixLength ∧
    (sweepStartMap θ t x).terminal = x.terminal ∧
    (sweepStartMap θ t x).pending = x.pending ∧
    (sweepStartMap θ t x).latest = x.latest ∧
    (sweepStartMap θ t x).components = x.components ∧
    (sweepStartMap θ t x).aborted = x.aborted := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sweepStartMap_length_zero {d m : ℕ} (θ t : ℝ) (x : RunRecord d m) :
    (sweepStartMap θ t x).sweep.length = 0 := rfl

theorem sweepStartMap_state_zero {d m : ℕ} (θ t : ℝ) (x : RunRecord d m) :
    (sweepStartMap θ t x).sweep.state 0 = sweepStartLiveState θ x := rfl

/-- Apply the measurable Picard correction and reset the endpoint Green matrix. -/
def resetMap {d m : ℕ} (t : ℝ) (x : RunRecord d m) : RunRecord d m :=
  let ζ := resetCorrection t (x.endpoint.M, x.r)
  let r' := x.r + ζ
  { x with
    r := r'
    endpoint := { x.endpoint with g := resetInverse x.endpoint.M r' t } }

/-- Code transformation for resetMap. -/
def resetEndCodeMap {d m : ℕ} (t : ℝ) (c : ResetRecordCode d m) : ResetRecordCode d m :=
  let M := c.2.1.2.1
  let r := c.2.1.2.2.2
  let ζ := resetCorrection t (M, r)
  let r' := r + ζ
  (c.1, (c.2.1.1, M, resetInverse M r' t, r'),
    c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2)

theorem measurable_resetEndCodeMap {d m : ℕ} (t : ℝ) :
    Measurable (resetEndCodeMap (d := d) (m := m) t) := by
  have hM : Measurable (fun c : ResetRecordCode d m => c.2.1.2.1) := by fun_prop
  have hr : Measurable (fun c : ResetRecordCode d m => c.2.1.2.2.2) := by fun_prop
  have hζ : Measurable (fun c : ResetRecordCode d m =>
      resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)) :=
    (measurable_resetCorrection (ι := Torus d m) t).comp (hM.prodMk hr)
  have hr' : Measurable (fun c : ResetRecordCode d m =>
      c.2.1.2.2.2 + resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)) := by
    fun_prop
  have hg' : Measurable (fun c : ResetRecordCode d m =>
      resetInverse (c.2.1.2.1)
        (c.2.1.2.2.2 + resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)) t) :=
    measurable_resetInverse_map t (fun c : ResetRecordCode d m => c.2.1.2.1)
      (fun c => c.2.1.2.2.2 + resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)) hM hr'
  have hG : Measurable (fun c : ResetRecordCode d m =>
      (c.1, (c.2.1.1, c.2.1.2.1,
        resetInverse (c.2.1.2.1)
          (c.2.1.2.2.2 + resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)) t,
        c.2.1.2.2.2 + resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)),
        c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2)) := by
    fun_prop
  change Measurable (fun c : ResetRecordCode d m =>
      (c.1, (c.2.1.1, c.2.1.2.1,
        resetInverse (c.2.1.2.1)
          (c.2.1.2.2.2 + resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)) t,
        c.2.1.2.2.2 + resetCorrection t (c.2.1.2.1, c.2.1.2.2.2)),
        c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2))
  exact hG

theorem resetMap_code {d m : ℕ} (t : ℝ) (x : RunRecord d m) :
    RunRecord.code (resetMap t x) =
      resetEndCodeMap (d := d) (m := m) t (RunRecord.code x) := by
  simp [RunRecord.code, resetMap, resetEndCodeMap] <;> rfl

theorem resetMap_measurable {d m : ℕ} (t : ℝ) :
    Measurable (resetMap (d := d) (m := m) t) := by
  apply RunRecord.measurable_reset_of_code (resetMap t)
    (resetEndCodeMap (d := d) (m := m) t) (resetMap_code t)
  exact measurable_resetEndCodeMap (d := d) (m := m) t

/-- On a good record, the correction obeys the stated radius and fixed-point equation. -/
theorem resetMap_correction_fixedPoint {d m : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (x : RunRecord d m)
    (hball : ∀ z, ‖z‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) →
      ‖resetTransform t (x.endpoint.M, x.r) z‖ ≤ t ^ (0.35 * AndersonAC.S78.delta))
    (hcontract : ∀ z w, ‖z‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) →
      ‖w‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) →
      ‖resetTransform t (x.endpoint.M, x.r) z - resetTransform t (x.endpoint.M, x.r) w‖ ≤
        (1 / 2 : ℝ) * ‖z - w‖) :
    ‖resetCorrection t (x.endpoint.M, x.r)‖ ≤ t ^ (0.35 * AndersonAC.S78.delta) ∧
      resetTransform t (x.endpoint.M, x.r) (resetCorrection t (x.endpoint.M, x.r)) =
        resetCorrection t (x.endpoint.M, x.r) := by
  exact resetCorrection_fixedPoint t ht (x.endpoint.M, x.r) hball hcontract

theorem resetMap_endpoint_g {d m : ℕ} (t : ℝ) (x : RunRecord d m) :
    (resetMap t x).endpoint.g =
      resetInverse x.endpoint.M (x.r + resetCorrection t (x.endpoint.M, x.r)) t := rfl

end AndersonAC.AgentS78

