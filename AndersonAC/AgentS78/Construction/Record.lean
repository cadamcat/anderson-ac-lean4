import AndersonAC.AgentS78.Construction.BlockRun
import AndersonAC.S45.Definitions

/-!
# The committed record of the run

The committed record passed from block to block
(02-state.tex:96–125, 05-local-sweeps.tex:338–420, 07-assembly.tex:18–34):

* `stage` — the stage whose operations are under way;
* `endpoint`, `r` — the committed physical S78 endpoint (active set, Schur matrix `M`,
  inverse `g`) and the frozen damping of the stage;
* `sweep` — the accepted prefix of the current ordinary sweep on the duplicated ports
  `S45.initialPorts` (states, pivots, scalars); its S45 records `Jrecord`, `Lrecord`,
  `lagRecord`, `rowRecord` give the accumulated sweep records of 05:399–409 and the
  validity test `S45.Sequence.valid`;
* `installed`, `prefixLength` — partial potential values and their binary prefix lengths;
  `terminal`, `pending`, `latest` — site states and latest birth labels;
* `components` — the snapshot components of the current clearing stage;
* `aborted`.

The measurable structure is the comap of an encoding into real/complex/Boolean
coordinates (finite sets as indicator functions); every field is discrete or a finite
array, so measurable decisions are the expected ones. Schedule operations update the
record according to the block rules.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The committed record of the run. -/
structure RunRecord (d m : ℕ) where
  stage : ℕ
  endpoint : Endpoint (Torus d m)
  r : Torus d m → ℂ
  sweep : S45.Sequence (S45.initialPorts (Torus d m))
  installed : Torus d m → ℝ
  prefixLength : Torus d m → ℕ
  terminal : Finset (Torus d m)
  pending : Finset (Torus d m)
  latest : Torus d m → BirthLabel (Torus d m)
  components : Finset (Finset (Torus d m))
  aborted : Bool

open Classical in
/-- Indicator encoding of a finite set. -/
def finsetCode {α : Type} (s : Finset α) : α → Bool := fun a => decide (a ∈ s)

theorem finsetCode_injective {α : Type} : Function.Injective (finsetCode (α := α)) := by
  intro s t h
  ext a
  have := congrFun h a
  simp only [finsetCode, decide_eq_decide] at this
  exact this

open Classical in
/-- Encoding of a birth label. -/
def labelCode {ι : Type} (a : BirthLabel ι) : ℕ × Bool × (ι → Bool) :=
  (a.scale, decide (a.kind = .tile), fun x => decide (x = a.anchor))

open Classical in
/-- Encoding of an optional pivot. -/
def optionCode {α : Type} (o : Option α) : α → Bool := fun a => decide (o = some a)

open Classical in
/-- The coordinate encoding of a committed record. -/
def RunRecord.code {d m : ℕ} (x : RunRecord d m) :=
  (x.stage,
   (finsetCode x.endpoint.active, x.endpoint.M, x.endpoint.g, x.r),
   (x.sweep.length, fun k => finsetCode (x.sweep.state k).live, fun k => (x.sweep.state k).g,
     fun k => optionCode (x.sweep.pivot k), x.sweep.scalar),
   (x.installed, x.prefixLength),
   (finsetCode x.terminal, finsetCode x.pending, fun y => labelCode (x.latest y)),
   (fun B : Finset (Torus d m) => decide (B ∈ x.components)),
   x.aborted)

instance (d m : ℕ) : MeasurableSpace (RunRecord d m) :=
  MeasurableSpace.comap RunRecord.code inferInstance

theorem RunRecord.measurable_code (d m : ℕ) :
    Measurable (RunRecord.code (d := d) (m := m)) := comap_measurable _

end AndersonAC.AgentS78
