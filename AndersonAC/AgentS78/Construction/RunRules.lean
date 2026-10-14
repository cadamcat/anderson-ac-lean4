import AndersonAC.AgentS78.Construction.SlotProcess
import AndersonAC.AgentS78.PendingFromRules

/-!
# runs described by their status and marking rules

`SlotRun` describes a finite-volume run of the construction at the level of
stage-end site records (02-state.tex:96–113, 08-history.tex:37–131, 296–400):

* the enlarged space and its true marginal (`TrueSpace.lean`);
* the chronological slot process with the conditional birth bound (history-birth);
* stage-end pending sets and latest labels obeying the status/marking rules and the
  clearing-stage dichotomy (the inputs of `pendingHistory_of_rules`), with births equal to
  the slot events of their labels;
* the late tile slots after the cutoff, the success event and its certificate.

`runLaw_of_slotRun` turns it into a `RunLaw`. With `uniformCertificateInput_of_slotRuns`,
this reduces `UniformCertificateInput` to constructing `SlotRun`s with uniform constants.
-/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- One finite-volume run, described by its slot process and its stage-end site records. -/
structure SlotRun (d m n₀ : ℕ) (u E Cr cp cg Ch c Clate : ℝ) (Ω : Type) [MeasurableSpace Ω] where
  μ : Measure Ω
  prob : IsProbabilityMeasure μ
  trueConfig : Ω → OAI.Anderson.TorusConfiguration d m
  trueConfig_measurable : Measurable trueConfig
  law : μ.map trueConfig = OAI.Anderson.torusLaw d m
  slots : SlotBirths d m c μ
  /-- pending at the end of stage `j` (after its clearings). -/
  pending : ℕ → Torus d m → Set Ω
  /-- the latest birth label of a site at the end of stage `j`. -/
  latest : ℕ → Torus d m → Ω → BirthLabel (Torus d m)
  pending_measurable : ∀ j x, MeasurableSet (pending j x)
  before : ∀ j x, j ≤ n₀ → pending j x = ∅
  /-- status rule (02-state.tex:96–113, 08-history.tex:44–50, mark radius 08:109–117). -/
  step : ∀ j x ω, n₀ ≤ j → ω ∈ pending (j + 1) x →
    (ω ∈ pending j x ∧ latest (j + 1) x ω = latest j x ω) ∨
    ((latest (j + 1) x ω).scale = j + 1 ∧
      ω ∈ slots.process.event (slots.slot (latest (j + 1) x ω)) ∧
      physicalDistance d m x (latest (j + 1) x ω).anchor ≤
        Ch * (4 : ℝ) ^ ((8 + nu d) * (((j + 1 : ℕ) : ℝ))))
  /-- clearing-stage dichotomy (08-history.tex:119–125). -/
  dichotomy : ∀ j x ω, n₀ < j → clearingScheduled j m → ω ∈ pending j x →
    ((latest j x ω).scale = j) ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
      stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, ω ∈ pending j y) ∧
      (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
  late : Finset ℕ
  late_card : (late.card : ℝ) ≤ Clate * ((m : ℝ) + 1) * (4 : ℝ) ^ (20 * d * m)
  late_scale : ∀ n ∈ late, m / 2 ≤ slots.process.scale n
  exceptional : Set Ω
  exceptional_null : μ exceptional = 0
  success : Set Ω
  failure_cover : successᶜ ⊆
    (⋃ x, pending (m / 2) x) ∪ (⋃ n ∈ late, slots.process.event n) ∪ exceptional
  certificate : success ⊆ trueConfig ⁻¹' boundedCertificateEvent d n₀ m u E Cr cp cg

/-- The pending history of a slot run. -/
def SlotRun.history {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (R : SlotRun d m n₀ u E Cr cp cg Ch c Clate Ω) : PendingHistory d m n₀ Ω :=
  pendingHistory_of_rules R.pending (fun a => R.slots.process.event (R.slots.slot a)) R.latest Ch
    R.before R.step R.dichotomy

theorem SlotRun.history_C {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ} {Ω : Type}
    [MeasurableSpace Ω] (R : SlotRun d m n₀ u E Cr cp cg Ch c Clate Ω) : R.history.C = Ch := rfl

/-- **Layer B′ glue.** A slot run is a run law. -/
def runLaw_of_slotRun {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ} (hc : 0 ≤ c) {Ω : Type}
    [MeasurableSpace Ω] (R : SlotRun d m n₀ u E Cr cp cg Ch c Clate Ω) :
    RunLaw d m n₀ u E Cr cp cg Ch c Clate Ω :=
  have := R.prob
  runLaw_of_slots hc R.μ R.trueConfig R.trueConfig_measurable R.law R.history R.history_C
    R.pending_measurable
    (fun a => R.slots.process.history.le _ _ (R.slots.process.adapted (R.slots.slot a)))
    R.slots (fun _ => subset_rfl) R.late R.late_card R.late_scale R.exceptional
    R.exceptional_null R.success R.failure_cover
    R.certificate

/-- **Reduction of `UniformCertificateInput` to slot runs with uniform constants.** -/
theorem uniformCertificateInput_of_slotRuns (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (Cr cp cg Ch c Clate : ℝ) (hcp : 0 < cp) (hcg : 0 < cg) (hCh : 1 ≤ Ch) (hc : 0 < c)
    (hClate : 0 ≤ Clate) (N₀ : ℕ)
    (hrun : ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω), Nonempty (SlotRun d m n₀ u E Cr cp cg Ch c Clate Ω)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_runLaw d hd e₂ Cr cp cg Ch c Clate hcp hcg hCh hc hClate N₀
    (fun n₀ m h1 h2 u hu E hE => by
      obtain ⟨Ω, _, ⟨R⟩⟩ := hrun n₀ m h1 h2 u hu E hE
      exact ⟨Ω, inferInstance, ⟨runLaw_of_slotRun hc.le R⟩⟩)

end AndersonAC.AgentS78
