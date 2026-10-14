import AndersonAC.AgentS78.Construction.RunRules
import AndersonAC.AgentS78.Construction.FreezingProof

/-!
# the run as an adaptive query strategy

`QueryRun` is the random multiscale construction on the §2 enlarged space
`RandomSources (Torus d m) M` (law `sourcesLaw`, 02-state.tex:126–170):

* `Q` is the single adaptive strategy of the whole run (queries of true digits, auxiliary
  signs, whole true suffixes, order entries, recorded decisions), admissible in the sense
  of `S2.ObeysQueryRules`; its retained σ-fields keep every answer, also after rollback;
* `start n` is the retained stopping time at which bookkeeping slot `n` is reached
  (08-history.tex:52–74: one slot per possible birth label, chronological; skipped slots
  have an empty trial);
* at its start the slot's *prestate* (committed numerical state, partition, marks, the
  whole schedule position) is known, and its first trial fails on `fail n (prestate)`,
  an event read off the pattern coordinates, which are still unqueried
  (coupled-site freshness, 02-state.tex:96–113);
* `product_bound` is the trial estimate with the prestate frozen (Propositions 5.x/6.6 via
  the deterministic induction, `good` = the prestate hypotheses);
* the stage-end pending sets, latest labels, late trials and success event are as in
  `SlotRun`, with births equal to the slot failures.

`slotRun_of_queryRun` (proved; the conditional slot bound uses
`freezing_proof : FreezingStatementNonneg`) gives a `SlotRun` and hence, with uniform constants,
`UniformCertificateInput` (`uniformCertificateInput_of_queryRuns`).
-/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query ObeysQueryRules sourcesLaw)

/-- One finite-volume run of the random construction as an adaptive query strategy. -/
structure QueryRun (d m n₀ : ℕ) (u E Cr cp cg Ch c Clate : ℝ) where
  M : ℕ → ℕ
  Q : ℕ → RandomSources (Torus d m) M → Query (Torus d m)
  rules : ObeysQueryRules (Torus d m) Q
  start : ℕ → RandomSources (Torus d m) M → WithTop ℕ
  start_stopping : ∀ n, IsStoppingTime (retainedFiltration (Torus d m) rules) (start n)
  start_mono : ∀ n, start n ≤ start (n + 1)
  start_finite : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) M, start n ω ≠ ⊤
  slotScale : ℕ → ℕ
  slot : BirthLabel (Torus d m) → ℕ
  slot_injective : Function.Injective slot
  slot_scale : ∀ a, slotScale (slot a) = a.scale
  S : Type
  [mS : MeasurableSpace S]
  prestate : ℕ → RandomSources (Torus d m) M → S
  prestate_measurable : ∀ n, Measurable[(start_stopping n).measurableSpace] (prestate n)
  pattern : ℕ → S → FreshPattern (Torus d m)
  pattern_measurable : ∀ n, Measurable (pattern n)
  fail : ℕ → S → Set (RandomSources (Torus d m) M)
  fail_measurable : ∀ n, MeasurableSet {p : S × RandomSources (Torus d m) M | p.2 ∈ fail n p.1}
  fail_local : ∀ n x, DependsOnly (Torus d m) (pattern n x) (fail n x)
  fresh : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) M,
    UnqueriedAt (Torus d m) Q ((start n ω).untopD 0) (pattern n (prestate n ω)) ω
  good : ℕ → Set S
  prestate_good : ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) M, prestate n ω ∈ good n
  product_bound : ∀ n, ∀ x ∈ good n,
    sourcesLaw (Torus d m) M (fail n x) ≤ ENNReal.ofReal (birthBound c (slotScale n))
  birth_adapted : ∀ n, MeasurableSet[(start_stopping (n + 1)).measurableSpace]
    {ω | start n ω ≠ ⊤ ∧ ω ∈ fail n (prestate n ω)}
  pending : ℕ → Torus d m → Set (RandomSources (Torus d m) M)
  latest : ℕ → Torus d m → RandomSources (Torus d m) M → BirthLabel (Torus d m)
  pending_measurable : ∀ j x, MeasurableSet (pending j x)
  before : ∀ j x, j ≤ n₀ → pending j x = ∅
  step : ∀ j x ω, n₀ ≤ j → ω ∈ pending (j + 1) x →
    (ω ∈ pending j x ∧ latest (j + 1) x ω = latest j x ω) ∨
    ((latest (j + 1) x ω).scale = j + 1 ∧
      (start (slot (latest (j + 1) x ω)) ω ≠ ⊤ ∧
        ω ∈ fail (slot (latest (j + 1) x ω)) (prestate (slot (latest (j + 1) x ω)) ω)) ∧
      physicalDistance d m x (latest (j + 1) x ω).anchor ≤
        Ch * (4 : ℝ) ^ ((8 + nu d) * (((j + 1 : ℕ) : ℝ))))
  dichotomy : ∀ j x ω, n₀ < j → clearingScheduled j m → ω ∈ pending j x →
    ((latest j x ω).scale = j) ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
      stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, ω ∈ pending j y) ∧
      (∀ y ∈ S, physicalDistance d m x y ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))
  late : Finset ℕ
  late_card : (late.card : ℝ) ≤ Clate * ((m : ℝ) + 1) * (4 : ℝ) ^ (20 * d * m)
  late_scale : ∀ n ∈ late, m / 2 ≤ slotScale n
  exceptional : Set (RandomSources (Torus d m) M)
  exceptional_null : sourcesLaw (Torus d m) M exceptional = 0
  success : Set (RandomSources (Torus d m) M)
  failure_cover : successᶜ ⊆ (⋃ x, pending (m / 2) x) ∪
    (⋃ n ∈ late, {ω | start n ω ≠ ⊤ ∧ ω ∈ fail n (prestate n ω)}) ∪ exceptional
  certificate : success ⊆ trueConfig ⁻¹' boundedCertificateEvent d n₀ m u E Cr cp cg

attribute [instance] QueryRun.mS

/-- The slot filtration: stopped retained σ-fields at the slot starts. -/
def QueryRun.slotFiltration {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ}
    (R : QueryRun d m n₀ u E Cr cp cg Ch c Clate) :
    Filtration ℕ (inferInstance : MeasurableSpace (RandomSources (Torus d m) R.M)) where
  seq n := (R.start_stopping n).measurableSpace
  mono' := monotone_nat_of_le_succ fun n =>
    IsStoppingTime.measurableSpace_mono _ _ (R.start_mono n)
  le' n := (R.start_stopping n).measurableSpace_le

/-- The chronological birth process of a query run. -/
def QueryRun.process {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ}
    (R : QueryRun d m n₀ u E Cr cp cg Ch c Clate) : BirthProcess (RandomSources (Torus d m) R.M) where
  history := R.slotFiltration
  event n := {ω | R.start n ω ≠ ⊤ ∧ ω ∈ R.fail n (R.prestate n ω)}
  scale := R.slotScale
  adapted n := R.birth_adapted n

/-- **Coupling (history-birth).** The conditional slot bound from the trial bound
(`freezing_proof`, Lemma 2.2 at the slot start). -/
theorem QueryRun.conditional {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ}
    (R : QueryRun d m n₀ u E Cr cp cg Ch c Clate) (n : ℕ) :
    ∀ᵐ ω ∂sourcesLaw (Torus d m) R.M,
      (sourcesLaw (Torus d m) R.M)[(R.process.event n).indicator (fun _ => (1 : ℝ)) |
        R.process.history n] ω ≤ birthBound c (R.process.scale n) := by
  have hfull := freezing_proof (Torus d m) R.M R.Q R.rules (R.start n) (R.start_stopping n)
    (R.start_finite n) R.S (R.prestate n) (R.prestate_measurable n) (R.pattern n)
    (R.pattern_measurable n) (R.fail n) (R.fail_measurable n) (R.fail_local n) (R.fresh n)
    (R.good n) (R.prestate_good n) _ (Real.exp_pos _).le (R.product_bound n)
  have hmP : Measurable (R.prestate n) :=
    (R.prestate_measurable n).mono ((R.start_stopping n).measurableSpace_le) le_rfl
  have hF : MeasurableSet {ω | ω ∈ R.fail n (R.prestate n ω)} :=
    (R.fail_measurable n).preimage (hmP.prodMk measurable_id)
  have hE : MeasurableSet (R.process.event n) :=
    (R.start_stopping (n + 1)).measurableSpace_le _ (R.birth_adapted n)
  have hsub : R.process.event n ⊆ {ω | ω ∈ R.fail n (R.prestate n ω)} := fun ω h => h.2
  have hmono := condExp_mono (m := R.process.history n) (μ := sourcesLaw (Torus d m) R.M)
    ((integrable_const (1 : ℝ)).indicator hE) ((integrable_const (1 : ℝ)).indicator hF)
    (ae_of_all _ (Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le_one)))
  filter_upwards [hfull, hmono] with ω h1 h2
  exact h2.trans h1

/-- The slot births of a query run. -/
def QueryRun.slots {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ}
    (R : QueryRun d m n₀ u E Cr cp cg Ch c Clate) :
    SlotBirths d m c (sourcesLaw (Torus d m) R.M) where
  process := R.process
  slot := R.slot
  slot_injective := R.slot_injective
  slot_scale := R.slot_scale
  conditional := R.conditional

/-- **Layer C glue.** A query run is a slot run on the enlarged space. -/
def slotRun_of_queryRun {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ}
    (R : QueryRun d m n₀ u E Cr cp cg Ch c Clate) :
    SlotRun d m n₀ u E Cr cp cg Ch c Clate (RandomSources (Torus d m) R.M) where
  μ := sourcesLaw (Torus d m) R.M
  prob := inferInstance
  trueConfig := trueConfig
  trueConfig_measurable := trueConfig_measurable d m R.M
  law := trueConfig_law d m R.M
  slots := R.slots
  pending := R.pending
  latest := R.latest
  pending_measurable := R.pending_measurable
  before := R.before
  step := R.step
  dichotomy := R.dichotomy
  late := R.late
  late_card := R.late_card
  late_scale := R.late_scale
  exceptional := R.exceptional
  exceptional_null := R.exceptional_null
  success := R.success
  failure_cover := R.failure_cover
  certificate := R.certificate

/-- **Reduction of `UniformCertificateInput` to query runs with uniform constants.** -/
theorem uniformCertificateInput_of_queryRuns
    (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (Cr cp cg Ch c Clate : ℝ) (hcp : 0 < cp) (hcg : 0 < cg) (hCh : 1 ≤ Ch) (hc : 0 < c)
    (hClate : 0 ≤ Clate) (N₀ : ℕ)
    (hrun : ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      Nonempty (QueryRun d m n₀ u E Cr cp cg Ch c Clate)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_slotRuns d hd e₂ Cr cp cg Ch c Clate hcp hcg hCh hc hClate N₀
    (fun n₀ m h1 h2 u hu E hE => by
      obtain ⟨R⟩ := hrun n₀ m h1 h2 u hu E hE
      exact ⟨_, inferInstance, ⟨slotRun_of_queryRun R⟩⟩)

end AndersonAC.AgentS78
