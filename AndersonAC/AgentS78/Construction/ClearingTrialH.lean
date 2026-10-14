import AndersonAC.AgentS78.Construction.ClearingTrial
import AndersonAC.S6.Preparation
import AndersonAC.AgentS6.TrialLocation
import AndersonAC.AgentS6.Frozen
import AndersonAC.AgentS6Conc.Bridge
import AndersonAC.S2.WardPackage
import AndersonAC.S78.Statements

/-!
# WP10 construction, C4b: the clearing first-trial bound from Proposition 6.6

`ClearingGood` (the deterministic trial hypotheses of a clearing attempt at stage
`j ≤ ⌊m/2⌋`) and the reduction of the clearing first-trial bound to

* Proposition 6.6, `S6.preparation_of_small_component` (proved, sol-s6 0415bba/aaf6984),
  applied with `μ = sourcesLaw` and trial-start σ-algebra `⊥` (06-clearing.tex:826–850);
* the pivot location of the stopped trial, `AgentS6.trial_pivots_located`
  (06-clearing.tex:772–784, 07-assembly.tex:200–216) and
  `S78.localized_pivot_excludes_old_marks` (07-assembly.tex:200–216);
* the vector concentration input, from the blueprint `ConcentrationInput` through
  `AgentS6.vectorConcentrationBridge_proof`;
* the frozen drift contract `AgentS6.LeverageDriftDischargeStatement` (muse-s6lev2, not yet
  delivered: a named hypothesis here);
* two sub-contracts on the clearing trial indexed by the active sites:
  `ClearingGeometryStatement` (the geometric fields of `S6.TrialLocalInput`,
  06-clearing.tex:757–771 and Lemma 7.2, 07-assembly.tex:96–200) and
  `ClearingResidualStatement` (its residual fields, 07-assembly.tex:200–236);
* `TrialReindexStatement`: transport of a stopped trial and its local input along an
  equivalence `ι ≃ Fin n` (Proposition 6.6 is stated for `Fin n`).

The frozen `ClearingTrialStatement` does not record that the trial's filtration is its
query history; Proposition 6.6 needs it (residual mean/variance given `q.history k`). The
variant `ClearingTrialStatementH` adds `∀ k, q.history k = queryHistory ⊥ q.pivot q.residual k`
(which `S6.construct_stopped_trial` provides). See INTERFACE-ISSUES (agent-s78clrtrial).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

/-- `ClearingTrialStatement` with the query-history hypothesis
`q.history = queryHistory ⊥ q.pivot q.residual` in place of `q.history 0 = ⊥`. -/
def ClearingTrialStatementH (d : ℕ)
    (good : ∀ {m : ℕ}, ℕ → ℝ → ℝ → ℕ → Set (RunRecord d m)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, ∀ j : ℕ, n₀ < j → clearingScheduled j m →
    ∀ (M : ℕ → ℕ) (x : RunRecord d m), x ∈ good n₀ u E j →
    ∀ B : Finset (ActiveSite x), B.Nonempty → B.map (Function.Embedding.subtype _) ∈ x.components →
      eligibleCore d B (stageScale u j m) →
      (∀ z ∈ x.pending, z ∉ B.map (Function.Embedding.subtype _) →
        ∀ y ∈ B.map (Function.Embedding.subtype _),
          separationRadius j - inspectionRadius j / 2 < physicalDistance d m z y) →
    ∀ (order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)))
      (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B (stageScale u j m)
        (fun _ i => x.r i) (fun _ => trialG0 x) order),
      (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
      (∀ k ω, k < q.stop ω → q.residual k ω =
        trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω (q.pivot k ω)
          (x.prefixLength (q.pivot k ω))) →
      (∀ k ω, k < q.stop ω → (q.pivot k ω).val ∉ x.pending ∧
        ∃ y ∈ B, physicalDistance d m (q.pivot k ω).val y.val ≤ inspectionRadius j / 2) ∧
      sourcesLaw (Torus d m) M {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} ≤
        ENNReal.ofReal (birthBound c j)

/-! ## The deterministic trial hypotheses -/

/-- The deterministic hypotheses on the entering record `x` of a clearing attempt at stage
`j` (frozen `t = stageScale u j m`, coupling `scaleCoupling n₀ u`).

* `broad`: the broad damping bounds (06-clearing.tex:clearing-broad; StageBounds' first
  clause, S78/Definitions.lean `StageBounds`, gives them with `cP, CP`);
* `fourth`, `lag`: the trial-start bounds of Proposition 6.6 for `g⁰ = endpoint.g` on the
  active sites (06-clearing.tex:829–832, eq. clearing-start: `max_i ∑_k |h⁰_ik|⁴ ≤ .8 H_*`,
  `max_i |g⁰_ii − r_i| = o(t^{β_w})`, uniformly: the `o` is the fixed function `qlag`);
* `coupled`: a coupled (active, nonpending) site carries the true prefix of `j − n₀` digits
  (02-state.tex:96–103, 104–113: "at a stage boundary this prefix has `n − n₀` digits");
* (separation of the attempted core from the other pending sites, 07-assembly.tex:200–209, is
  a hypothesis on the core `B` in the trial statements, not a record clause: after a failed
  clearing the inspected exterior sites of that component are pending within `ℓ_j/2` of it;
  agent-s78phase2 03:43:17, decision agent-s78con4);
* `coreBall`: a snapshot component lies in a ball of radius `|C| R_j` about one of its points
  (07-assembly.tex:181–183: diameter at most `(r_* − 1) R_j`);
* `geo`: the record-level clearing geometry consumed by `ClearingGeometryStatement`
  (terminal Schur structure and the geometry trace of Lemma 7.2, 07-assembly.tex:96–200);
  left as a parameter for the geometry contract. -/
structure ClearingGoodAt {d m : ℕ} (cP CP : ℝ) (qlag : ℝ → ℝ) (n₀ : ℕ) (u : ℝ) (j : ℕ)
    (x : RunRecord d m) : Prop where
  broad : ∀ i ∈ x.endpoint.active, ‖x.r i‖ ≤ CP ∧ cP ≤ (x.r i).im ∧ (x.r i).im ≤ CP
  fourth : ∀ i : ActiveSite x,
    AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse (stageScale u j m) (trialG0 x)) i ≤
      (4 / 5) * AndersonAC.S6.fourthCap (stageScale u j m)
  lag : ∀ i ∈ x.endpoint.active, ‖x.endpoint.g i i - x.r i‖ ≤
    qlag (stageScale u j m) * stageScale u j m ^ AndersonAC.S6.betaW
  coupled : ∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i + n₀ = j
  coreBall : ∀ C ∈ x.components, ∃ a, ∀ y ∈ C,
    physicalDistance d m a y ≤ (C.card : ℝ) * separationRadius j

/-- The C4b good set: `ClearingGoodAt` and the geometry parameter `geo`. -/
def ClearingGood (d : ℕ) (cP CP : ℝ) (qlag : ℝ → ℝ)
    (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m)) {m : ℕ} (n₀ : ℕ) (u _E : ℝ)
    (j : ℕ) : Set (RunRecord d m) :=
  {x | ClearingGoodAt cP CP qlag n₀ u j x ∧ x ∈ geo n₀ u j}

/-! ## The local input of §6, split into its geometric and residual fields -/

section Split

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

open AndersonAC.S6

/-- The geometric fields of `S6.TrialLocalInput` (06-clearing.tex:757–771). -/
structure TrialGeometryInput {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (d : ℕ) (c K Cloc : ℝ) (dist : ι → ι → ℝ) (collapsed : ℕ → Ω → ι → ι → ℝ)
    (ell : ℝ) : Prop where
  dist_nonneg : ∀ i j, 0 ≤ dist i j
  dist_symm : ∀ i j, dist i j = dist j i
  dist_triangle : ∀ i j k, dist i k ≤ dist i j + dist j k
  dist_self : ∀ i, dist i i = 0
  ell_lower : (1 / 256) * t ^ (-4 : ℤ) ≤ ell
  ell_upper : ell ≤ 2 * t ^ (-4 : ℤ)
  core_ball : ∃ center, ∀ b ∈ core, dist center b ≤ t ^ (-Cloc)
  shells : ∀ i (n : ℕ),
    ((Finset.univ.filter (fun j => (n : ℝ) ≤ dist i j ∧ dist i j < n + 1)).card : ℝ) ≤
      K * (1 + (n : ℝ)) ^ (d - 1)
  volume : ∀ i (L : ℝ), 0 ≤ L →
    ((Finset.univ.filter (fun j => dist i j ≤ L)).card : ℝ) ≤ K * (1 + L) ^ d
  metric : ∀ k ω, k ≤ q.stop ω →
    (∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2) →
    ∀ i j, dist i j / 2 - t ^ (-(103 / 100 : ℝ)) ≤ collapsed k ω i j
  range_geometry : ∀ k ω, k ≤ q.stop ω →
    (∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2) →
    ∃ H : Matrix ι ι ℂ,
      ExteriorGeometry d (fun i => max (distanceToCore (collapsed k ω) core i - 1) 0)
        H (trialCross t (r ω) (q.state k ω)) t (r ω)
  resolvent_decay : ∀ k ω, k < q.stop ω →
    (∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2) →
    ∀ i j : {i // i ∈ (q.state k ω).active},
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) i j‖ ≤
        K / Real.sqrt t * Real.exp (-c * t * collapsed k ω i j)

/-- The residual fields of `S6.TrialLocalInput` (07-assembly.tex:200–236). -/
structure TrialResidualInput {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (μ : Measure Ω) (K : ℝ)
    (dist : ι → ι → ℝ) (ell : ℝ) : Prop where
  residual_bound : ∀ k ω, k < q.stop ω →
    distanceToCore dist core (q.pivot k ω) < ell / 2 → |q.residual k ω| ≤ K * Real.sqrt t
  residual_integrable : ∀ k, Integrable (q.residual k) μ
  residual_square_integrable : ∀ k, Integrable (fun ω => (q.residual k ω) ^ 2) μ
  residual_mean : ∀ k, ∀ᵐ ω ∂μ, k < q.stop ω →
    distanceToCore dist core (q.pivot k ω) < ell / 2 → μ[q.residual k | q.history k] ω = 0
  residual_variance : ∀ k, ∃ η : Ω → ℝ,
    StronglyMeasurable[q.history k] η ∧
    (∀ᵐ ω ∂μ, k < q.stop ω →
      distanceToCore dist core (q.pivot k ω) < ell / 2 →
      0 ≤ η ω / t ∧ η ω / t ≤ K * t ∧
        μ[(fun ω => (q.residual k ω) ^ 2) | q.history k] ω = t - η ω)

theorem trialLocalInput_of_split {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    {q : StoppedTrial (Ω := Ω) core t r g0 order} {μ : Measure Ω} {d : ℕ} {c K K' Cloc : ℝ}
    {dist : ι → ι → ℝ} {collapsed : ℕ → Ω → ι → ι → ℝ} {ell : ℝ}
    (hg : TrialGeometryInput q d c K Cloc dist collapsed ell)
    (hr : TrialResidualInput q μ K' dist ell) (hK : K' ≤ K) (ht : 0 < t) :
    TrialLocalInput q μ d c K Cloc dist collapsed ell where
  dist_nonneg := hg.dist_nonneg
  dist_symm := hg.dist_symm
  dist_triangle := hg.dist_triangle
  dist_self := hg.dist_self
  ell_lower := hg.ell_lower
  ell_upper := hg.ell_upper
  core_ball := hg.core_ball
  shells := hg.shells
  volume := hg.volume
  metric := hg.metric
  range_geometry := hg.range_geometry
  resolvent_decay := hg.resolvent_decay
  residual_bound := fun k ω hk hl =>
    (hr.residual_bound k ω hk hl).trans
      (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg t))
  residual_integrable := hr.residual_integrable
  residual_square_integrable := hr.residual_square_integrable
  residual_mean := hr.residual_mean
  residual_variance := fun k => by
    obtain ⟨η, hη, hae⟩ := hr.residual_variance k
    refine ⟨η, hη, hae.mono fun ω h hk hl => ?_⟩
    obtain ⟨h1, h2, h3⟩ := h hk hl
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hK ht.le), h3⟩

end Split

/-! ## Truncated residual stream

After the stop a `StoppedTrial` constrains its residuals only through `residual_revealed`,
so they need not be integrable. Proposition 6.6 is applied to the same trial with the
residual set to `0` after the stop (same states, pivots, stop, outcome and history). -/

section Trunc

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

open AndersonAC.S6

theorem stopping_lt_measurableSet {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) :
    MeasurableSet[q.history k] {ω | k < q.stop ω} := by
  have h := q.stopping k
  have : {ω | k < q.stop ω} = {ω | ((q.stop ω : ℕ) : WithTop ℕ) ≤ (k : WithTop ℕ)}ᶜ := by
    ext ω
    simp [WithTop.coe_le_coe, not_le]
  rw [this]
  exact h.compl

/-- The trial with residual `0` after the stop. -/
def truncTrial {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    (q : StoppedTrial (Ω := Ω) core t r g0 order) :
    StoppedTrial (Ω := Ω) core t r g0 order :=
  { q with
    residual := fun k ω => if k < q.stop ω then q.residual k ω else 0
    heat := fun k ω hk => by
      simp only [if_pos hk]
      exact q.heat k ω hk
    residual_revealed := fun k => by
      have hs : MeasurableSet[q.history (k + 1)] {ω | k < q.stop ω} :=
        q.history.mono (Nat.le_succ k) _ (stopping_lt_measurableSet q k)
      have : (fun ω => if k < q.stop ω then q.residual k ω else 0) =
          {ω | k < q.stop ω}.indicator (q.residual k) := by
        funext ω
        simp [Set.indicator_apply]
      rw [this]
      exact (q.residual_revealed k).indicator hs }

theorem TrialGeometryInput.trunc {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)}
    {q : StoppedTrial (Ω := Ω) core t r g0 order} {d : ℕ} {c K Cloc : ℝ}
    {dist : ι → ι → ℝ} {collapsed : ℕ → Ω → ι → ι → ℝ} {ell : ℝ}
    (h : TrialGeometryInput q d c K Cloc dist collapsed ell) :
    TrialGeometryInput (truncTrial q) d c K Cloc dist collapsed ell where
  dist_nonneg := h.dist_nonneg
  dist_symm := h.dist_symm
  dist_triangle := h.dist_triangle
  dist_self := h.dist_self
  ell_lower := h.ell_lower
  ell_upper := h.ell_upper
  core_ball := h.core_ball
  shells := h.shells
  volume := h.volume
  metric := h.metric
  range_geometry := h.range_geometry
  resolvent_decay := h.resolvent_decay

end Trunc

/-! ## Sub-contracts -/

/-- **Sub-contract (geometry).** On good entering records, the clearing trial on the active
sites has the geometric local input of §6 with the physical distance and `ℓ = ℓ_j = 4^{4j}`
(06-clearing.tex:757–771; Lemma 7.2, 07-assembly.tex:96–200: metric (1), the range
geometry of the terminal Schur structure, the collapsed resolvent decay of Lemma 6.2;
`ℓ_j ≍ t_j^{-4}`; core ball from the snapshot diameter; lattice shell and volume counts).
The constants are uniform and compatible with the broad bounds `cP, CP`. -/
def ClearingGeometryStatement (d : ℕ)
    (good : ∀ {m : ℕ}, ℕ → ℝ → ℝ → ℕ → Set (RunRecord d m)) (cP CP : ℝ) : Prop :=
  ∃ c K Cloc : ℝ, 0 < c ∧ c ≤ cP ∧ CP ≤ K ∧ 1 ≤ K ∧ 0 ≤ Cloc ∧
  ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, ∀ j : ℕ, n₀ < j → clearingScheduled j m →
    ∀ (M : ℕ → ℕ) (x : RunRecord d m), x ∈ good n₀ u E j →
    ∀ B : Finset (ActiveSite x), B.Nonempty → B.map (Function.Embedding.subtype _) ∈ x.components →
      eligibleCore d B (stageScale u j m) →
    ∀ (order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)))
      (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B (stageScale u j m)
        (fun _ i => x.r i) (fun _ => trialG0 x) order),
      (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
      (∀ k ω, k < q.stop ω → q.residual k ω =
        trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω (q.pivot k ω)
          (x.prefixLength (q.pivot k ω))) →
      ∃ collapsed : ℕ → RandomSources (Torus d m) M → ActiveSite x → ActiveSite x → ℝ,
        TrialGeometryInput q d c K Cloc (fun a b => physicalDistance d m a.val b.val)
          collapsed (inspectionRadius j)

/-- **Sub-contract (residual law).** On good entering records, the revealed residual of a
localized pivot (a coupled site with an untouched true suffix of `j − n₀` exposed digits) is
centered with conditional variance `s_j = t_j − η` (stated for `truncTrial q`, whose residual is `0` after the stop), `0 ≤ η ≤ C t_j²`, and bounded by
`√(3 s_j)` (07-assembly.tex:200–236, 02-state.tex:85–89; `Lemma conditional-freshness`). -/
def ClearingResidualStatement (d : ℕ)
    (good : ∀ {m : ℕ}, ℕ → ℝ → ℝ → ℕ → Set (RunRecord d m)) : Prop :=
  ∃ K : ℝ, ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, ∀ j : ℕ, n₀ < j → clearingScheduled j m →
    ∀ (M : ℕ → ℕ) (x : RunRecord d m), x ∈ good n₀ u E j →
    ∀ B : Finset (ActiveSite x), B.Nonempty → B.map (Function.Embedding.subtype _) ∈ x.components →
      eligibleCore d B (stageScale u j m) →
      (∀ z ∈ x.pending, z ∉ B.map (Function.Embedding.subtype _) →
        ∀ y ∈ B.map (Function.Embedding.subtype _),
          separationRadius j - inspectionRadius j / 2 < physicalDistance d m z y) →
    ∀ (order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)))
      (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B (stageScale u j m)
        (fun _ i => x.r i) (fun _ => trialG0 x) order),
      (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
      (∀ k ω, k < q.stop ω → q.residual k ω =
        trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω (q.pivot k ω)
          (x.prefixLength (q.pivot k ω))) →
      TrialResidualInput (truncTrial q) (sourcesLaw (Torus d m) M) K
        (fun a b => physicalDistance d m a.val b.val) (inspectionRadius j)

/-- **Sub-contract (transport, mechanical).** A stopped trial and its local input transported
along `e : ι ≃ Fin n` (Proposition 6.6 and `trial_pivots_located` are stated for `Fin n`). -/
def TrialReindexStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (n : ℕ) (e : ι ≃ Fin n) (core : Finset ι) (t : ℝ)
    (r : Ω → ι → ℂ) (g0 : Ω → Matrix ι ι ℂ) (order : ι ≃ Fin (Fintype.card ι))
    (q : AndersonAC.S6.StoppedTrial (Ω := Ω) core t r g0 order),
    ∃ q' : AndersonAC.S6.StoppedTrial (Ω := Ω) (core.map e.toEmbedding) t
        (fun ω i => r ω (e.symm i)) (fun ω => (g0 ω).submatrix e.symm e.symm)
        (e.symm.trans (order.trans (finCongr (Fintype.card_congr e)))),
      q'.history = q.history ∧ q'.stop = q.stop ∧ q'.outcome = q.outcome ∧
      q'.residual = q.residual ∧ (∀ k ω, q'.pivot k ω = e (q.pivot k ω)) ∧
      ∀ (μ : Measure Ω) (d : ℕ) (c K Cloc : ℝ) (dist : ι → ι → ℝ)
        (collapsed : ℕ → Ω → ι → ι → ℝ) (ell : ℝ),
        AndersonAC.S6.TrialLocalInput q μ d c K Cloc dist collapsed ell →
        AndersonAC.S6.TrialLocalInput q' μ d c K Cloc (fun a b => dist (e.symm a) (e.symm b))
          (fun k ω a b => collapsed k ω (e.symm a) (e.symm b)) ell

/-! ## Uniform forms of Proposition 6.6 and of the drift contract (requested from sol-s6 and
muse-s6lev2; the frozen forms choose `t0`, `ε` after the space and the law) -/

open AndersonAC.S6 in
/-- Proposition 6.6 (06-clearing.tex:826–850) with `t0` chosen before the probability space:
"the constants are independent of the torus volume and of the component". -/
def PreparationUniformStatement : Prop :=
  ∀ (d : ℕ) (_hd : 3 ≤ d) (c K Cloc cConc : ℝ) (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc)
    (_hConc : 0 < cConc) (qlag ε : ℝ → ℝ) (_hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (_hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) (_hεpos : ∀ t, 0 ≤ ε t),
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
      (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
      (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → 1 ≤ core.card → (core.card : ℝ) ≤ coreCap d t →
      (∀ ω, BroadBounds c K (r ω)) →
      (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
      (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      VectorConcentrationInput μ q.history cConc →
      LeverageDriftInput μ q.history (ε t) (fun k => {ω | k < q.stop ω})
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω)))
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω))) →
      ∀ᵐ ω ∂μ, conditionalProbability μ (q.history 0) {ω | q.outcome ω = .fail} ω ≤
        Real.exp (-t ^ (-clearingExponent d))

open AndersonAC.S6 in
/-- `AgentS6.LeverageDriftDischargeStatement` with `ε` and `t0` chosen before the space. -/
def LeverageDriftUniformStatement : Prop :=
  ∀ (_hWard : AndersonAC.Blueprint.WardInput)
    (d : ℕ) (_hd : 3 ≤ d) (c K Cloc : ℝ) (_hc : 0 < c) (_hK : 1 ≤ K) (_hCloc : 0 ≤ Cloc)
    (qlag : ℝ → ℝ) (_hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0)),
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ (∀ t, 0 ≤ ε t) ∧ ∃ t0 : ℝ, 0 < t0 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (n : ℕ) (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ)
        (g0 : Ω → Matrix (Fin n) (Fin n) ℂ) (order : Fin n ≃ Fin (Fintype.card (Fin n)))
        (q : StoppedTrial (Ω := Ω) core t r g0 order)
        (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → 1 ≤ core.card → (core.card : ℝ) ≤ coreCap d t →
      (∀ ω, BroadBounds c K (r ω)) →
      (∀ ω i, fourthRow (scaledInverse t (g0 ω)) i ≤ (4 / 5) * fourthCap t) →
      (∀ ω i, ‖g0 ω i i - r ω i‖ ≤ qlag t * t ^ betaW) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      LeverageDriftInput μ q.history (ε t) (fun k => {ω | k < q.stop ω})
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state k ω) (q.ridge k ω)))
        (onRunning (fun k => {ω | k < q.stop ω})
          (fun k ω => trialWeights t (r ω) (q.state (k + 1) ω) (q.ridge k ω)))

end AndersonAC.AgentS78
