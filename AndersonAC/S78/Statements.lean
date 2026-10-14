import AndersonAC.S78.Definitions
import AndersonAC.S78.MeasurableReset
import AndersonAC.S78Comm.Commutator
import AndersonAC.S78Hist.Closure
import AndersonAC.S78Schur.Bridge
import AndersonAC.S78.ChronologicalBridge
import AndersonAC.S78Abort.Abort
import AndersonAC.S78Taylor.Taylor
import AndersonAC.S78Persist.Persistence
import AndersonAC.S78Proj.Elementary
import AndersonAC.S78.EnergyChange
import AndersonAC.S78Scale.Proofs
import AndersonAC.S78Row.Clearing
import AndersonAC.S78Row.Row
import AndersonAC.S78Tail.Proofs
import AndersonAC.S78Union.Bounds
import AndersonAC.S78Complete.CertificateCompletion
import AndersonAC.S78WSupp.WitnessSupport
import AndersonAC.S78Metric.Metric
import AndersonAC.S78Extract.Extract
import AndersonAC.S78Thresh.Threshold
import AndersonAC.S78.DiagonalReset
import AndersonAC.S78Var.Proof
import AndersonAC.S2.WardPackage
import AndersonAC.S78Moment.Moments
import AndersonAC.S78Moment.Translation
import AndersonAC.S78Stage.Induction
import AndersonAC.S78WRec.Final
import AndersonAC.S78Pending.Pending
import AndersonAC.S78.WeightedEndpoints
import AndersonAC.S78Geom.Geometry
import AndersonAC.S78.AssemblyEndpoints

/-! Results for §§7–8 with their explicit hypotheses. Concrete definitions
are in Definitions.lean. See PLAN.md for construction obligations. -/
open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
noncomputable section
namespace AndersonAC.S78

theorem assembly_metric {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (G : SimpleGraph ι) (hconn : G.Connected) (T : Finset ι) (O : κ → Finset ι)
    (c μ R ℓ : ℝ) (M : ℕ) (hc : 0 < c) (hμ : 0 ≤ μ)
    (hold : ∀ u v, c * (G.dist u v : ℝ) - μ ≤ terminalDistance G T u v)
    (hsize : ∀ a, (O a).card ≤ M)
    (hsep : ∀ a a', a ≠ a' → ∀ u ∈ O a, ∀ v ∈ O a', R - 2 * ℓ ≤ (G.dist u v : ℝ))
    (hmargin : 2 * (M : ℝ) < c * (R - 2 * ℓ) - μ) :
    ∀ u v, c * (1 - 2 * (M : ℝ) / (c * (R - 2 * ℓ) - μ)) * (G.dist u v : ℝ) - μ - 2 * (M : ℝ) ≤
      terminalDistance G (T ∪ Finset.univ.biUnion O) u v := by
  exact AndersonAC.SolS78.assembly_metric_proof G hconn T O c μ R ℓ M hc hμ hold hsize hsep hmargin

theorem committed_assembly (d : ℕ) (hd : 3 ≤ d) (C c P : ℝ)
    (hC : 1 ≤ C) (hc : 0 < c) (hP : 0 ≤ P) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧ ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
      (I : AssemblyInput d m k t b r), I.C = C → I.c = c → I.P = P → t < t₀ →
      ∀ a : Fin (k + 1),
      matrixNorm (squareKernel (normalizedInverse (I.state a) t)) ≤
        matrixNorm (squareKernel (normalizedInverse (I.state 0) t)) + t ^ (0.10 * delta) ∧
      (∀ i ∈ (I.state a).active, ‖(I.state a).g i i - r i‖ ≤ C' * t ^ (0.42 * delta - (d : ℝ) * nu d)) ∧
      (∀ i, (rowFour (normalizedInverse (I.state a) t) i) ^ (1 / 4 : ℝ) ≤
        (0.7 ^ (1 / 4 : ℝ) + C' * t ^ (0.0225 * delta - (d : ℝ) * nu d)) * t ^ ((1 + delta) / 4) ∧
        rowFour (normalizedInverse (I.state a) t) i < 0.8 * t ^ (1 + delta)) ∧
      constantKernel (I.state a).active (endpointEnergy (I.state a) r t) ∧
      (∀ f, |∑ q : Fin k with q.val < a.val, operationEnergyError I q f| ≤
        t ^ (0.10 * delta) * endpointEnergy (I.state 0) r t f) ∧
      (∀ y, neutral (I.state a).active y →
        (1 + t ^ (0.10 * delta))⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y ≤
          inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ∧
        inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ≤
          (1 - t ^ (0.10 * delta))⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y) := by
  exact AndersonAC.SolS78.committed_assembly_of_estimates
    AndersonAC.SolS78.finiteFormInput_proof AndersonAC.SolS78.assemblyMatrixBounds_proof
    AndersonAC.SolS78.assemblyEnergyBounds_proof d hd C c P hC hc hP

theorem endpoint_square_change (z a : ℂ) : (z + a) ^ 2 - z ^ 2 = 2 * z * a + a ^ 2 := by
  exact AndersonAC.SolS78.endpoint_square_change_proof z a

theorem endpoint_modulus_change (z a : ℂ) :
    ‖z + a‖ ^ 2 - ‖z‖ ^ 2 = 2 * (star z * a).re + ‖a‖ ^ 2 := by
  exact AndersonAC.SolS78.endpoint_modulus_change_proof z a

theorem fourth_row_from_entry_and_two {ι : Type} [Fintype ι] (a : Matrix ι ι ℂ) (i : ι) (U V : ℝ)
    (hU : 0 ≤ U) (hentry : ∀ j, ‖a i j‖ ≤ U) (hrow : rowTwo a i ≤ V) : rowFour a i ≤ U ^ 2 * V := by
  exact AndersonAC.SolS78.fourth_row_from_entry_and_two_proof a i U V hU hentry hrow

theorem diagonal_reset (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ),
      0 < t → t < t₀ → (∀ i j, M i j = M j i ∧ (M i j).im = 0) →
      (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ ‖r i‖ ≤ C) →
      (∀ i, (resetInverse M r t i i).im ≤ C) →
      matrixNorm (squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t)) < 1 / 2 →
      (∀ v : ι → ℂ, ‖((1 - squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t))⁻¹).mulVec v‖ ≤
        C * Real.log (1 / t) * ‖v‖) →
      ‖resetLag M r t‖ ≤ t ^ (0.36 * delta) →
      ∃ ζ : ι → ℂ, ‖ζ‖ ≤ t ^ (0.35 * delta) ∧ ResetOutput M r ζ t C' ∧
        (∀ i, c / 2 ≤ ((r + ζ) i).im ∧ ((r + ζ) i).im ≤ 2 * C) := by
  exact AndersonAC.SolS78.diagonal_reset_of_variation AndersonAC.Blueprint.Packages.ward
    AndersonAC.SolS78.reset_variation_proof c C hc hC
/-- The measurable reset is the limit of measurable contractions on a closed ball. -/

theorem measurable_contraction_reset {Ω ι : Type} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (a : ℝ) (ha : 0 ≤ a)
    (T : Ω → (ι → ℂ) → (ι → ℂ)) (hT : Measurable (Function.uncurry T))
    (hball : ∀ ω z, ‖z‖ ≤ a → ‖T ω z‖ ≤ a)
    (hcontract : ∀ ω z w, ‖z‖ ≤ a → ‖w‖ ≤ a → ‖T ω z - T ω w‖ ≤ (1 / 2) * ‖z - w‖) :
    ∃ ζ : Ω → ι → ℂ, Measurable ζ ∧ ∀ ω, ‖ζ ω‖ ≤ a ∧ T ω (ζ ω) = ζ ω := by
  have hb : ∀ ω z, ‖z - (0 : ι → ℂ)‖ ≤ a → ‖T ω z - 0‖ ≤ a := by
    simpa only [sub_zero] using hball
  have hc : ∀ ω z w, ‖z - (0 : ι → ℂ)‖ ≤ a → ‖w - 0‖ ≤ a →
      ‖T ω z - T ω w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖ := by
    simpa only [sub_zero] using hcontract
  simpa only [sub_zero] using
    AndersonAC.SolS78.measurable_fixedPoint_closedBall T 0 a ha hT hb hc

theorem chronological_joint {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : BirthProcess Ω) (c : ℝ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ,
      μ[(B.event n).indicator (fun _ => (1 : ℝ)) | B.history n] ω ≤ birthBound c (B.scale n))
    (S : Finset ℕ) :
    μ (⋂ n ∈ S, B.event n) ≤ ENNReal.ofReal (∏ n ∈ S, birthBound c (B.scale n)) := by
  exact AndersonAC.SolS78.chronological_joint_for_section μ B c hbound S

theorem extract_witness (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ (m n₀ : ℕ) (Ω : Type) (H : PendingHistory d m n₀ Ω), N ≤ n₀ → H.C = C →
      ∀ j x ω, n₀ ≤ j → clearingScheduled j m → ω ∈ H.pending j x →
        ∃ L, IsWitness d m n₀ j x L ∧ ∀ a ∈ L, ω ∈ H.birth a := by
  exact AndersonAC.SolS78.extract_witness_proof d hd C hC

theorem witness_support (d : ℕ) (hd : 3 ≤ d) :
    ∃ N : ℕ, ∀ m n₀ j x L, N ≤ n₀ → IsWitness d m n₀ j x L →
      (∀ a ∈ L, physicalDistance d m x a.anchor ≤ witnessRadius j) ∧
      (∀ a ∈ L, n₀ < a.scale ∧ a.scale ≤ j) := by
  exact AndersonAC.SolS78.witness_support_proof d hd

theorem close_history_recursion (d : ℕ) (hd : 3 ≤ d) (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ n₀ J, N ≤ n₀ → ∀ Z : ℕ → ℝ, (∀ j, 0 ≤ Z j) → Z n₀ = 0 →
      (∀ j, n₀ < j → j ≤ J → Z j ≤ recursionBound d n₀ j c C Z) →
      ∀ j, n₀ ≤ j → j ≤ J → Z j ≤ birthBound (historyExponent d c) j := by
  exact AndersonAC.SolS78.close_history_recursion_proof d hd c C hc hC


theorem pending_site_bound (d : ℕ) (hd : 3 ≤ d) (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ (m n₀ : ℕ) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (H : PendingHistory d m n₀ Ω), N ≤ n₀ → H.C = C →
      (∀ j x, MeasurableSet (H.pending j x)) → (∀ a, MeasurableSet (H.birth a)) →
      (∀ S : Finset (BirthLabel (Torus d m)), μ (⋂ a ∈ S, H.birth a) ≤ ENNReal.ofReal (witnessWeight c S)) →
      ∀ j x, n₀ ≤ j → clearingScheduled j m →
        μ (H.pending j x) ≤ ENNReal.ofReal (birthBound (historyExponent d c) j) := by
  exact AndersonAC.SolS78.pending_site_bound_proof d hd c C hc hC

theorem uniform_abort_bound (d : ℕ) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n₀ m, N ≤ n₀ → 4 * n₀ ≤ m → abortBound d m q C ≤ Real.exp (-(m : ℝ)) := by
  exact AndersonAC.SolS78.uniform_abort_bound_proof d q C hq hC


theorem abort_bound_tendsto (d : ℕ) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C) :
    Tendsto (fun m : ℕ => abortBound d m q C) atTop (𝓝 0) := by
  exact AndersonAC.SolS78.abort_bound_tendsto_proof d q C hq hC


theorem final_tail_update (η : ℝ) (ξ r : ℂ) :
    (Real.sqrt (1 / 2 : ℝ) : ℂ) * (ξ / (Real.sqrt (1 / 2 : ℝ) : ℂ) +
      (2 * η : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) * r) = ξ + (η : ℂ) * r := by
  exact AndersonAC.SolS78.final_tail_update_proof η ξ r

theorem window_threshold_nonempty (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (hengine : UniformCertificateInput d e₂) : ∃ k, windowThreshold d e₂ k := by
  exact AndersonAC.SolS78.window_threshold_nonempty_proof d hd e₂ hengine

theorem threshold_nonempty (d : ℕ) (hd : 4 ≤ d) (e₂ : ℝ)
    (hengine : UniformCertificateInput d e₂) : ∃ k, thresholdCriterion d k := by
  exact AndersonAC.SolS78.threshold_nonempty_proof d hd e₂ hengine

theorem threshold_measurable (d k n₀ m : ℕ) (u E : ℝ) :
    MeasurableSet (certificateEvent d k n₀ m u E) := by
  exact OAI.Anderson.certificateEvent_measurableSet d k n₀ m u E

theorem threshold_exists_positive (d : ℕ) (hd : 4 ≤ d) (e₂ : ℝ)
    (hengine : UniformCertificateInput d e₂) : ∃ lambda : ℝ, finiteBoxThreshold d lambda ∧ 0 < lambda := by
  exact AndersonAC.SolS78.threshold_exists_positive_proof d hd e₂ hengine

theorem threshold_probability {d k : ℕ} (hk : IsLeast {n : ℕ | thresholdCriterion d n} k)
    {coupling : ℝ} (hc : 0 < coupling) (hsmall : coupling < Real.sqrt 3 / (2 : ℝ) ^ k) :
    ∃ n₀ : ℕ, k ≤ n₀ ∧ ∃ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 ∧
      OAI.Anderson.scaleCoupling n₀ u = coupling ∧ ∀ m, 4 * n₀ ≤ m →
        ∀ E ∈ OAI.Anderson.higherDimWindow d,
          (1 / 2 : ℝ≥0∞) ≤ OAI.Anderson.torusLaw d m (certificateEvent d k n₀ m u E) := by
  exact AndersonAC.SolS78.threshold_probability_proof hk hc hsmall

/-! Geometry trace: both successful groups and one currently provisional group
are counted. Failed groups are absent after rollback. -/
/-- Lemma 7.2, assertions (1),(3), under the inductively maintained location
hypothesis. It includes a prospective first budget-breaking pivot. -/

theorem uniform_clearing_geometry (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∃ C' : ℝ, 0 < C' ∧ ∀ (m n₀ j l : ℕ) (u : ℝ),
      N ≤ n₀ → n₀ ≤ j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ T : ClearingGeometry d m n₀ j l u C,
      (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        terminalDistance (nnGraph d m) (geometryTerminals T) x y) ∧
      Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ geometryTerminals T).card ∧
      (∀ a, T.index a = j → (T.core a \ geometryTerminals T).card <
        (Finset.univ \ geometryTerminals T).card) ∧
      (∀ x, ((Finset.univ.filter fun a => T.index a = j ∧ x ∈ cube d m (T.anchor a)
          (200 * C * stageScale u j m ^ (-nu d) * separationRadius j)).card : ℝ) ≤
        C' * stageScale u j m ^ (-(d : ℝ) * nu d)) := by
  exact AndersonAC.SolS78.uniform_clearing_geometry_proof d hd C hC
/-- Lemma 7.2 assertion (2), with §6's proposed-location implication as input.
`representation` only needs the already localized earlier pivots. -/

theorem clearing_locality (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ (m n₀ j q : ℕ) (u : ℝ) (B : Finset (Torus d m))
      (pivot : Fin q → Torus d m) (T : Fin (q + 1) → Finset (Torus d m)),
      N ≤ n₀ → n₀ ≤ j → clearingScheduled j m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      (∀ a, (∀ i : Fin q, i.val < a.val → ∃ y ∈ B,
          physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) →
        ∃ l : ℕ, ∃ trace : ClearingGeometry d m n₀ j l u C, T a = geometryTerminals trace) →
      (∀ i : Fin q,
        (∀ x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
          terminalDistance (nnGraph d m) (T i.castSucc) x y) →
        ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) →
      (∀ i, ∃ y ∈ B, physicalDistance d m (pivot i) y ≤ inspectionRadius j / 2) ∧
      (∀ a x y, physicalDistance d m x y / 2 - stageScale u j m ^ (-1.03 : ℝ) ≤
        terminalDistance (nnGraph d m) (T a) x y) ∧
      (∀ a, Fintype.card (Torus d m) ≤ 2 * (Finset.univ \ T a).card) := by
  exact AndersonAC.SolS78.clearing_locality_proof d hd C hC

theorem localized_pivot_excludes_old_marks {d m : ℕ} (B bad : Finset (Torus d m))
    (x : Torus d m) (R ℓ : ℝ) (hR : ℓ < R)
    (hnear : ∃ y ∈ B, physicalDistance d m x y ≤ ℓ / 2)
    (hbad : ∀ z ∈ bad, ∀ y ∈ B, R - ℓ / 2 < physicalDistance d m z y) : x ∉ bad := by
  exact AndersonAC.SolS78.localized_pivot_excludes_old_marks_proof B bad x R ℓ hR hnear hbad
/-- Uniform scale comparison (history-scale-comparison). -/

theorem stage_scale_comparison (u : ℝ) (j m : ℕ)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hjm : j ≤ m) :
    (1 / 4 : ℝ) / (4 : ℝ) ^ j < stageScale u j m ∧
    stageScale u j m ≤ 2 / (4 : ℝ) ^ j := by
  exact AndersonAC.SolS78.stage_scale_comparison_proof u j m hu hjm
/-- The dimension-independent interpolation used in assembly. -/

theorem assembly_exponent_margins (d : ℕ) (hd : 3 ≤ d) :
    (d : ℝ) * nu d = 0.00001 * delta ∧
    0.36 * delta < 0.42 * delta - (d : ℝ) * nu d ∧
    0 < 0.0225 * delta - (d : ℝ) * nu d ∧
    0.10 * delta < 0.125 * delta - (d : ℝ) * nu d ∧ heatExponent < 0.03 := by
  exact AndersonAC.SolS78.assembly_exponent_margins_proof d hd
/-- (assembly-lattice-moments), with q=0 understood as a zeroth moment. -/

theorem lattice_exponential_moments (d q : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m t, 0 < t → t ≤ 1 → ∀ x : Torus d m,
      (∑ y, Real.exp (-c * t * physicalDistance d m x y) * physicalDistance d m x y ^ q) ≤
        C * t ^ (-(d : ℝ) - (q : ℝ)) := by
  exact AndersonAC.SolS78.lattice_exponential_moments_proof d q c hc
/-- (assembly-translation). -/

theorem translation_energy (d m : ℕ) (v : Torus d m → ℝ) (u : Torus d m) :
    (∑ i, (v (i + u) - v i) ^ 2) ≤
      physicalDistance d m 0 u ^ 2 * gradientEnergy (nnGraph d m) v := by
  exact AndersonAC.SolS78.translation_energy_proof d m v u
/-- §7.4 Taylor remainder, with constants independent of active cardinality. -/

theorem reset_taylor (c C : ℝ) (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ C' a₀ : ℝ, 0 < C' ∧ 0 < a₀ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ),
      0 < t → (∀ i j, M i j = M j i ∧ (M i j).im = 0) →
      (∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ (resetInverse M r t i i).im ≤ C) →
      ∃ R : (ι → ℂ) → (ι → ℂ),
      (∀ z, ‖z‖ ≤ a₀ →
        (fun i => resetInverse M (r + z) t i i) =
          (fun i => resetInverse M r t i i) +
          (squareKernel ((Real.sqrt t : ℂ) • resetInverse M r t)).mulVec z + R z) ∧
      (∀ z, ‖z‖ ≤ a₀ → ‖R z‖ ≤ C' * ‖z‖ ^ 2) ∧
      (∀ a z w, 0 ≤ a → a ≤ a₀ → ‖z‖ ≤ a → ‖w‖ ≤ a → ‖R z - R w‖ ≤ C' * a * ‖z - w‖) := by
  exact AndersonAC.SolS78.reset_taylor_proof c C hc hC

/-- Proposition 7.5 bookkeeping, with its one-stage estimates explicit.
Initialization and the derivation of PathwiseStageInputs are separate obligations. -/

theorem deterministic_induction (d : ℕ) (hd : 3 ≤ d) (cP CP cL CL C : ℝ)
    (hcP : 0 < cP) (hCP : cP ≤ CP) (hcL : 0 < cL) (hCL : 0 < CL) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m n₀ u (H : PathwiseStageInputs d m n₀ u C),
      N ≤ n₀ → 4 * n₀ ≤ m → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      StageBounds d m n₀ n₀ u cP CP cL CL C₀ (H.state n₀) (H.r n₀) →
      matrixNorm (squareKernel (normalizedInverse (H.state n₀) (stageScale u n₀ m))) ≤ 1 / 4 →
      ∀ n, n₀ ≤ n → n ≤ m →
        StageBounds d m n₀ n u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀ (H.state n) (H.r n) := by
  exact AndersonAC.SolS78.deterministic_induction_proof d hd cP CP cL CL C hcP hCP hcL hCL hC
/-- Compact sharp-diagonal margin in the proof of Proposition 7.5. -/

theorem sharp_diagonal_margin (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ θ ∈ Set.Icc (0.25 : ℝ) 0.625, a ≤ θ ^ κ - θ := by
  exact AndersonAC.SolS78.sharp_diagonal_margin_proof κ hκ hκ1
/-- Persistence from the status rule: a pending survivor either retains its
previous label or gets the current stage as its latest label. -/

theorem pending_persistence (pending : ℕ → Prop) (latest : ℕ → ℕ)
    (hstep : ∀ n, pending (n + 1) →
      (pending n ∧ latest (n + 1) = latest n) ∨ latest (n + 1) = n + 1)
    (hstamp : ∀ n, pending n → latest n ≤ n) (r j : ℕ)
    (hrj : r ≤ j) (hp : pending j) (hl : latest j ≤ r) : pending r := by
  exact AndersonAC.SolS78.pending_persistence_proof pending latest hstep hstamp r j hrj hp hl
/-- (history-recursion), obtained by counting leaf labels and ordered children. -/

theorem witness_recursion (d : ℕ) (hd : 3 ≤ d) :
    ∃ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ m n₀ j c, N ≤ n₀ → n₀ < j → clearingScheduled j m → 0 < c →
      witnessMass d m n₀ j c ≤ recursionBound d n₀ j c C (fun r => witnessMass d m n₀ r c) := by
  exact AndersonAC.SolS78.witness_recursion_proof d hd
/-- Each child witness has distinct physical support, hence distinct labels. -/

theorem witness_children_disjoint (d : ℕ) (hd : 3 ≤ d) :
    ∃ N : ℕ, ∀ m n₀ r x y L K, N ≤ n₀ → IsWitness d m n₀ r x L → IsWitness d m n₀ r y K →
      3 * witnessRadius r < physicalDistance d m x y → Disjoint L K := by
  exact AndersonAC.SolS78.witness_children_disjoint_proof d hd

theorem cutoff_probability_bound {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d m J : ℕ)
    (pending : Torus d m → Set Ω) (q : ℝ)
    (hp : ∀ x, μ (pending x) ≤ ENNReal.ofReal (birthBound q J)) :
    μ (⋃ x, pending x) ≤ ENNReal.ofReal ((4 : ℝ) ^ (20 * d * m) * birthBound q J) := by
  exact AndersonAC.SolS78.cutoff_probability_bound_proof μ d m J pending q hp
/-- Uniform late-trial union bound; aborted and skipped slots have empty events. -/

theorem late_failure_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Finset ℕ) (event : ℕ → Set Ω) (p : ℝ)
    (hp : ∀ n ∈ S, μ (event n) ≤ ENNReal.ofReal p) :
    μ (⋃ n ∈ S, event n) ≤ ENNReal.ofReal ((S.card : ℝ) * p) := by
  exact AndersonAC.SolS78.late_failure_bound_proof μ S event p hp

theorem final_tail_moments {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hmean : ∫ ω, ξ ω ∂μ = 0) (hvar : ∫ ω, (ξ ω) ^ 2 ∂μ = η)
    (hbound : ∀ᵐ ω ∂μ, |ξ ω| ≤ Real.sqrt (3 * η)) :
    (∫ ω, ξ ω / Real.sqrt (1 / 2 : ℝ) ∂μ) = 0 ∧
    (∫ ω, (ξ ω / Real.sqrt (1 / 2 : ℝ)) ^ 2 ∂μ) = 2 * η ∧
    (∀ᵐ ω ∂μ, |ξ ω / Real.sqrt (1 / 2 : ℝ)| ≤ Real.sqrt (3 * (2 * η))) := by
  exact AndersonAC.SolS78.final_tail_moments_proof μ ξ η hη hmean hvar hbound
/-- Last paragraph of the certificate proof: project auxiliary success onto
true variables, using the unconditional marginal, not a conditional law. -/

theorem success_projects_to_true_law {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (d m : ℕ) (trueConfig : Ω → OAI.Anderson.TorusConfiguration d m)
    (hmap : Measurable trueConfig) (hlaw : μ.map trueConfig = OAI.Anderson.torusLaw d m)
    (S : Set Ω) (event : Set (OAI.Anderson.TorusConfiguration d m))
    (hevent : MeasurableSet event) (hsuccess : S ⊆ trueConfig ⁻¹' event) :
    μ S ≤ OAI.Anderson.torusLaw d m event := by
  exact AndersonAC.SolS78.success_projects_to_true_law_proof μ d m trueConfig
    hmap hlaw S event hevent hsuccess

theorem certificate_family_of_uniform_input (e₂ : ℝ)
    (hengine : ∀ d : ℕ, 3 ≤ d → UniformCertificateInput d e₂) : CertificateFamily e₂ := by
  exact AndersonAC.SolS78.certificate_family_of_uniform_input_proof e₂ hengine
theorem rollback_has_zero_error {ι Q : Type} (T : TrialRecord ι Q) (hf : T.outcome = .fail)
    (r : ι → ℂ) (t : ℝ) : endpointEnergy T.output r t = endpointEnergy T.before r t ∧
      normalizedInverse T.output t = normalizedInverse T.before t := by
  exact AndersonAC.SolS78.rollback_has_zero_error_proof T hf r t

theorem intrinsic_threshold_spec (d : ℕ) (hne : ∃ k, thresholdCriterion d k) :
    IsLeast {k | thresholdCriterion d k} (thresholdIndex d hne) ∧
    finiteBoxThreshold d (intrinsicThreshold d hne) ∧ 0 < intrinsicThreshold d hne := by
  exact AndersonAC.SolS78.intrinsic_threshold_spec_proof d hne
/-- The bridge is the extra old energy in the Schur minimum, not a new edge error. -/

theorem schur_bridge_trial {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hBA : B ⊆ A) (p : ι → ℝ) (hp : ∀ i ∈ A, 0 ≤ p i)
    (h : Matrix ι ι ℂ) (hsym : ∀ i j, h i j = h j i) (f : ι → ℝ) (c : ℝ) :
    0 ≤ schurEnergy B (wardEnergy A p h) f - wardEnergy B p h f ∧
    schurEnergy B (wardEnergy A p h) f - wardEnergy B p h f ≤
      ∑ i ∈ B, ∑ x ∈ A \ B, p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2 := by
  exact AndersonAC.SolS78.schur_bridge_trial_proof A B hBA p hp h hsym f c


/-- (assembly-weighted-local); the cube-weight inequality is supplied by §3. -/

theorem weighted_local_energy (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : Torus d m) (R b Lmax Ltotal : ℝ)
      (A : Finset (Torus d m)) (w : Matrix (Torus d m) (Torus d m) ℝ)
      (α v : Torus d m → ℝ),
      1 ≤ R → 4 * R < (OAI.Anderson.sideLength m : ℝ) → 0 < b → 0 ≤ Lmax → 0 ≤ Ltotal →
      (∀ i j, 0 ≤ w i j ∧ w i j = w j i) →
      (∀ i j, i ∉ cube d m z R ∩ A ∨ j ∉ cube d m z R ∩ A → w i j = 0) →
      (∀ i, (∑ j, w i j) ≤ Lmax) → (∑ i, ∑ j, w i j) ≤ Ltotal →
      (∑ i, ∑ j, w i j * ((α i + v i) - (α j + v j)) ^ 2) ≤
        C * (Lmax + b * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ)) *
          ((∑ i ∈ cube d m z (2 * R) ∩ A, (α i) ^ 2) + b⁻¹ * cubeGradient d m (cube d m z (2 * R)) v) := by
  exact AndersonAC.SolS78.weighted_local_energy_proof d hd
/-- (assembly-reset-commutator), the exact matrix identity used in the form bound. -/

theorem reset_commutator {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : Matrix ι ι ℂ) (z : ι → ℂ) (f : ι → ℝ)
    (hh : IsUnit h.det) (hnew : IsUnit (h⁻¹ - Matrix.diagonal z).det) :
    let F := Matrix.diagonal (fun i => (f i : ℂ))
    let h' := (h⁻¹ - Matrix.diagonal z)⁻¹
    F * h' - h' * F = (1 - h * Matrix.diagonal z)⁻¹ * (F * h - h * F) *
      (1 - Matrix.diagonal z * h)⁻¹ := by
  exact AndersonAC.SolS78.reset_commutator_proof h z f hh hnew

theorem successful_clearing_distortions (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧ ∀ (ι : Type) [Fintype ι]
      (heat core : Matrix ι ι ℂ) (t : ℝ), 0 < t → t < min t₀ 1 →
      (∀ i j, ‖heat i j‖ ≤ Real.sqrt t * t ^ (0.42 * delta)) →
      (∀ i, rowTwo heat i ≤ t ^ (0.25 * delta)) → frobeniusSq heat ≤ t ^ (-1 - 0.47 * delta) →
      (∀ i j, ‖core i j‖ ≤ C * Real.sqrt t * t ^ (0.44 * delta)) →
      (∀ i, rowTwo core i ≤ C * t ^ (0.44 * delta)) → frobeniusSq core ≤ C * t ^ (-1 - nu d) →
      (∀ i j, ‖(heat + core) i j‖ ≤ C' * Real.sqrt t * t ^ (0.42 * delta)) ∧
      (∀ i, rowTwo (heat + core) i ≤ C' * t ^ (0.25 * delta)) ∧
      frobeniusSq (heat + core) ≤ C' * t ^ (-1 - 0.47 * delta) := by
  exact AndersonAC.SolS78.successful_clearing_distortions_proof d hd C hC
/-- Same closed-graph projection proof as the OAI k-bounded event. -/

theorem bounded_certificate_event_measurable (d n₀ m : ℕ) (u E Cr cp cg : ℝ) :
    MeasurableSet (boundedCertificateEvent d n₀ m u E Cr cp cg) := by
  exact AndersonAC.SolS78.bounded_certificate_event_measurable_proof d n₀ m u E Cr cp cg
/-- §8.3 quantitative completion from the final physical block identity and
unconditional marginal. The success inclusion must be established from the
§2 terminal-Schur identity and last true-tail sweep, rather than assumed fresh
conditional on eventual success. -/

theorem certificate_completion {Ω : Type} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (e₂ q C Cr cp cg : ℝ) (cutoff : ℕ)
    (hq : 0 < q) (hC : 0 ≤ C) (hcp : 0 < cp) (hcg : 0 < cg)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (trueConfig : ∀ m : ℕ, Ω → OAI.Anderson.TorusConfiguration d m)
    (hmap : ∀ m, Measurable (trueConfig m))
    (hlaw : ∀ m, μ.map (trueConfig m) = OAI.Anderson.torusLaw d m)
    (success : ℕ → ℕ → ℝ → ℝ → Set Ω)
    (hmeas : ∀ n₀ m u E, MeasurableSet (success n₀ m u E))
    (hfinal : ∀ n₀ m u E, cutoff ≤ n₀ → 4 * n₀ ≤ m →
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → E ∈ OAI.Anderson.energyWindow d e₂ →
      success n₀ m u E ⊆ (trueConfig m) ⁻¹' boundedCertificateEvent d n₀ m u E Cr cp cg)
    (habort : ∀ n₀ m u E, cutoff ≤ n₀ → 4 * n₀ ≤ m →
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → E ∈ OAI.Anderson.energyWindow d e₂ →
      μ (success n₀ m u E)ᶜ ≤ ENNReal.ofReal (abortBound d m q C)) :
    UniformCertificateInput d e₂ := by
  exact AndersonAC.SolS78.certificate_completion_proof d hd e₂ q C Cr cp cg cutoff
    hq hC hcp hcg μ trueConfig hmap hlaw success hmeas hfinal habort
end AndersonAC.S78
