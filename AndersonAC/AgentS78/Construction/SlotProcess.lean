import AndersonAC.AgentS78.Construction.RunLaw

/-!
# chronological birth slots

08-history.tex:37–99. All possible birth labels are listed in one deterministic
chronological order of *slots*; the retained history just before slot `n` is the stopped
σ-field `history n`, and the slot's birth indicator is measurable one slot later. The
conditional bound (history-birth) `E(B_n | F_n⁻) ≤ p_{j(n)}` is the only probabilistic
input. Layer B turns it into the joint bound (history-joint) for the label-indexed
births of a `PendingHistory`, and into the per-trial bound for the late trials.
-/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- A chronological slot process for the births of one run (08-history.tex:52–80). -/
structure SlotBirths (d m : ℕ) (c : ℝ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) where
  process : BirthProcess Ω
  slot : BirthLabel (Torus d m) → ℕ
  slot_injective : Function.Injective slot
  slot_scale : ∀ a, process.scale (slot a) = a.scale
  conditional : ∀ n, ∀ᵐ ω ∂μ,
    μ[(process.event n).indicator (fun _ => (1 : ℝ)) | process.history n] ω ≤
      birthBound c (process.scale n)

theorem birthBound_anti_scale {c : ℝ} (hc : 0 ≤ c) {i j : ℕ} (hij : i ≤ j) :
    birthBound c j ≤ birthBound c i := by
  unfold birthBound
  apply Real.exp_le_exp.mpr
  have : (4 : ℝ) ^ (c * (i : ℝ)) ≤ (4 : ℝ) ^ (c * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hc)
  linarith

/-- (history-joint) for label-indexed births contained in their slot events. -/
theorem birth_joint_of_slots {d m : ℕ} {c : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : SlotBirths d m c μ)
    (birth : BirthLabel (Torus d m) → Set Ω)
    (hbirth : ∀ a, birth a ⊆ P.process.event (P.slot a))
    (S : Finset (BirthLabel (Torus d m))) :
    μ (⋂ a ∈ S, birth a) ≤ ENNReal.ofReal (witnessWeight c S) := by
  classical
  have hsub : (⋂ a ∈ S, birth a) ⊆ ⋂ n ∈ S.image P.slot, P.process.event n := by
    intro ω hω
    simp only [Set.mem_iInter] at hω ⊢
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact hbirth a (hω a ha)
  refine le_trans (measure_mono hsub) (le_trans
    (chronological_joint μ P.process c P.conditional (S.image P.slot)) (le_of_eq ?_))
  congr 1
  rw [Finset.prod_image (fun a _ b _ h => P.slot_injective h)]
  unfold witnessWeight
  exact Finset.prod_congr rfl (fun a _ => by rw [P.slot_scale])

/-- One slot event has probability at most its conditional bound. -/
theorem slot_event_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B : BirthProcess Ω) (c : ℝ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ,
      μ[(B.event n).indicator (fun _ => (1 : ℝ)) | B.history n] ω ≤ birthBound c (B.scale n))
    (n : ℕ) : μ (B.event n) ≤ ENNReal.ofReal (birthBound c (B.scale n)) := by
  have h := chronological_joint μ B c hbound {n}
  simpa using h

/-- **Layer B glue.** A run whose births and late trials are chronological slot events
with conditional bounds (history-birth) is a `RunLaw`. Late trials are after the cutoff,
so their slot scale is at least `⌊m/2⌋`. -/
def runLaw_of_slots {d m n₀ : ℕ} {u E Cr cp cg Ch c Clate : ℝ} (hc : 0 ≤ c)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (trueConfig : Ω → OAI.Anderson.TorusConfiguration d m)
    (htrue : Measurable trueConfig) (hlaw : μ.map trueConfig = OAI.Anderson.torusLaw d m)
    (H : PendingHistory d m n₀ Ω) (hHC : H.C = Ch)
    (hpend : ∀ j x, MeasurableSet (H.pending j x)) (hbirthm : ∀ a, MeasurableSet (H.birth a))
    (P : SlotBirths d m c μ) (hbirth : ∀ a, H.birth a ⊆ P.process.event (P.slot a))
    (late : Finset ℕ)
    (hlate_card : (late.card : ℝ) ≤ Clate * ((m : ℝ) + 1) * (4 : ℝ) ^ (20 * d * m))
    (hlate_scale : ∀ n ∈ late, m / 2 ≤ P.process.scale n)
    (exceptional : Set Ω) (hnull : μ exceptional = 0) (success : Set Ω)
    (hcover : successᶜ ⊆
      (⋃ x, H.pending (m / 2) x) ∪ (⋃ n ∈ late, P.process.event n) ∪ exceptional)
    (hcert : success ⊆ trueConfig ⁻¹' boundedCertificateEvent d n₀ m u E Cr cp cg) :
    RunLaw d m n₀ u E Cr cp cg Ch c Clate Ω where
  μ := μ
  prob := hμ
  trueConfig := trueConfig
  trueConfig_measurable := htrue
  law := hlaw
  history := H
  history_C := hHC
  pending_measurable := hpend
  birth_measurable := hbirthm
  birth_joint := birth_joint_of_slots P H.birth hbirth
  late := late
  late_card := hlate_card
  lateEvent := P.process.event
  late_prob := fun n hn => le_trans (slot_event_le P.process c P.conditional n)
    (ENNReal.ofReal_le_ofReal (birthBound_anti_scale hc (hlate_scale n hn)))
  exceptional := exceptional
  exceptional_null := hnull
  success := success
  failure_cover := hcover
  certificate := hcert

end AndersonAC.AgentS78
