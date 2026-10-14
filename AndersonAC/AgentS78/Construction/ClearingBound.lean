import AndersonAC.AgentS78.Construction.ClearingBoundNull
import AndersonAC.AgentS78.Construction.ClearingBoundFlip
import AndersonAC.AgentS78.Construction.ClearingTrialH
import AndersonAC.AgentS78.Construction.ClearingBlock
import AndersonAC.AgentS78.Construction.ClearingFacts
import AndersonAC.AgentS78.Construction.StagePhaseGood
import AndersonAC.AgentS78.Construction.OrderSizes
import AndersonAC.AgentS78.Construction.Exceptional
import AndersonAC.AgentS78.Construction.ClearingTrialZProof
import AndersonAC.AgentS78.Construction.FinalInputs
import AndersonAC.AgentS78.Construction.StagePhaseGoodR
import AndersonAC.AgentS78Geo.Geo
import AndersonAC.AgentS6Construct.Construct

/-!
# The clearing first-failure bound on good records (agent-s78clrbound)

Target: the `hboundC` field of `BoxInvariantK` (BoxSplit.lean), request DISPATCH 02:51:56
(agent-s78con3). For good entering records of the clearing block of `(j, y)`,
`sourcesLaw (localFirstFail (clearingBlock n₀ j u y) x) ≤ birthBound c j`.

Route (06-clearing.tex:788–857, 07-assembly.tex:18–34, 02-state.tex:220–229):

1. no core (or aborted record): the failure set is empty (`empty_firstFail_empty`);
2. otherwise `B` := the core as a finset of active sites, the order of `siteRank`;
3. the trial `q` of `S6.construct_stopped_trial` with `M₀` the real active block of
   `x.endpoint.M`, `F₀ = ⊥`, and residuals the `λ`-coupled true residuals **modified on a null
   set `Z`** (`clrTerminal_ae`, ClearingBoundNull.lean): its `hterminal` (invertibility of every
   principal block) holds only almost surely;
4. its initial inverse is `trialG0 x` (damped identity, `activeInverse_eq_trialG0`);
5. C4b off a null set (`ClearingTrialStatementZ`, frozen by agent-s78con4, proved by
   `clearingTrialZ_proof`); `Z` is taken flip-invariant (`flipSat`, ClearingBoundFlip.lean);
6. muse-s78clear's bridge, sample by sample (`ClearingBridgeAtStatement`, the form adopted by
   the lead 03:57:19; open, a named hypothesis here).

**Interface defect (INTERFACE-ISSUES 03:54:15, accepted 03:57:19).** The frozen
`ClearingTrialStatement` and the frozen `clearingBlock_bridge` ask for `q.residual = trueResidual`
at **every** sample. A `StoppedTrial` with exact residuals need not exist: `HeatTransition`
requires `s.M x x + ξ ≠ 0`, and the run is forced, so at a sample where the forced pivot has a
singular real Schur pivot no such trial exists. The consumer can only build the trial with
residuals exact off a null set; hence the two amended forms above.

Results: `clearingBound_of_contracts` (any geometry, C4b-Z and the bridge as hypotheses),
`clearingBound_records` (C4b-Z discharged, record hypotheses explicit) and
`clearingBound_clearPhaseR` (records of agent-s78phase2's `ClearPhaseR … j (rank y)`).
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

/-! ## The two contracts -/

/-- The bridge **sample by sample** (lead decision 03:57:19, with the damped-record hypothesis
approved 04:58:00): same data as muse-s78clear's frozen bridge plus
`IsDampedEndpoint rec0.endpoint rec0.r t_j`, and at each sample `ω` whose running residuals are
exact and whose running pivots pass the guard, `ω` is a block-local first failure iff the trial
fails at `ω`. This is verbatim agent-s78cbridge's `ClearingBridgeAtDStatement d m`
(INTERFACE-ISSUES 04:57:43), so `fun m => clearingBridgeAtD_proof d m` discharges it. -/
def ClearingBridgeAtStatement (d m : ℕ) : Prop :=
  ∀ (n₀ j : ℕ) (u : ℝ) (x : Torus d m) (M : ℕ → ℕ) (rec0 : RunRecord d m)
    (B : Finset (ActiveSite rec0)),
    theCore (d := d) (m := m) j u x rec0 = B.map (Function.Embedding.subtype _) →
    B.Nonempty → rec0.aborted = false → clearingScheduled j m →
    Disjoint rec0.endpoint.active rec0.terminal →
    IsDampedEndpoint rec0.endpoint rec0.r (stageScale u j m) →
    ∀ (order : ActiveSite rec0 ≃ Fin (Fintype.card (ActiveSite rec0))),
    (∀ a b : ActiveSite rec0, (order a).val ≤ (order b).val ↔
        (siteRank d m a.val).val ≤ (siteRank d m b.val).val) →
    ∀ (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M)
      B (stageScale u j m) (fun _ i => rec0.r i) (fun _ => trialG0 rec0) order),
    (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
    ∀ ω : RandomSources (Torus d m) M,
    (∀ k, k < q.stop ω → q.residual k ω = trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω
        (q.pivot k ω) (rec0.prefixLength (q.pivot k ω))) →
    (∀ k, k < q.stop ω → (q.pivot k ω).val ∉ rec0.pending ∧
      ∃ y ∈ B, physicalDistance d m (q.pivot k ω).val y.val ≤ inspectionRadius j / 2) →
    (ω ∈ localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) rec0 ↔
      q.outcome ω = AndersonAC.S6.TrialOutcome.fail)

/-! ## Adapters -/

variable {d m : ℕ}

/-- An equivalence with `Fin (card α)` ordered like an injective rank. -/
theorem exists_equivFin_of_rank {α : Type} [Fintype α] (f : α → ℕ) (hf : Function.Injective f) :
    ∃ e : α ≃ Fin (Fintype.card α), ∀ a b, (e a).val ≤ (e b).val ↔ f a ≤ f b := by
  let _ : LinearOrder α := LinearOrder.lift' f hf
  let o := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨o.toEquiv, fun a b => ?_⟩
  show (o a : Fin _) ≤ o b ↔ _
  rw [o.le_iff_le]
  rfl

/-- The `siteRank` order on the active sites. -/
theorem exists_activeOrder (x : RunRecord d m) :
    ∃ order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)), ∀ a b : ActiveSite x,
      (order a).val ≤ (order b).val ↔ (siteRank d m a.val).val ≤ (siteRank d m b.val).val :=
  exists_equivFin_of_rank (fun a : ActiveSite x => (siteRank d m a.val).val)
    (fun a b h => Subtype.val_injective ((siteRank d m).injective (Fin.val_injective h)))

/-- A nonempty core is the eligible component anchored at `y`. -/
theorem theCore_spec_of_ne {j : ℕ} {u : ℝ} {y : Torus d m} {x : RunRecord d m}
    (h : theCore (d := d) (m := m) j u y x ≠ ∅) :
    theCore (d := d) (m := m) j u y x ∈ x.components ∧
      eligibleCand (d := d) (m := m) j u y (theCore (d := d) (m := m) j u y x) := by
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr h
  obtain ⟨Bc, hBc, hel, hwB⟩ := mem_theCore (d := d) (m := m) (j := j) (u := u) (y := y) x hw
  have huniq : ∀ B ∈ x.components, eligibleCand (d := d) (m := m) j u y B → B = Bc := by
    intro B hB helB
    by_contra hne
    apply h
    classical
    unfold theCore
    dsimp only
    rw [if_neg]
    intro hcard
    obtain ⟨C, hC⟩ := Finset.card_eq_one.mp hcard
    have h1 : B ∈ x.components.filter (fun B => eligibleCand (d := d) (m := m) j u y B) :=
      Finset.mem_filter.mpr ⟨hB, helB⟩
    have h2 : Bc ∈ x.components.filter (fun B => eligibleCand (d := d) (m := m) j u y B) :=
      Finset.mem_filter.mpr ⟨hBc, hel⟩
    rw [hC, Finset.mem_singleton] at h1 h2
    exact hne (h1.trans h2.symm)
  rw [theCore_eq_of_unique j u y x hBc hel huniq]
  exact ⟨hBc, hel⟩

/-- The real active block of the committed `M`. -/
def activeRealM (x : RunRecord d m) : Matrix (ActiveSite x) (ActiveSite x) ℝ :=
  fun a b => (x.endpoint.M a.val b.val).re

/-- **The damped identity:** the §6 initial inverse of the real active block is `trialG0 x`. -/
theorem activeInverse_eq_trialG0 {x : RunRecord d m} {t : ℝ}
    (hD : IsDampedEndpoint x.endpoint x.r t) :
    AndersonAC.S6.activeInverse (activeRealM x) t (fun i : ActiveSite x => x.r i.val) =
      trialG0 x := by
  obtain ⟨hsym, -, hBG⟩ := hD
  dsimp only at hBG
  have hM : (activeRealM x).map Complex.ofReal =
      x.endpoint.M.submatrix (fun i : x.endpoint.active => i.val)
        (fun i : x.endpoint.active => i.val) := by
    ext a b
    simp only [activeRealM, Matrix.map_apply, Matrix.submatrix_apply]
    exact Complex.ext (by simp) (by simp [(hsym a.val b.val).2])
  unfold AndersonAC.S6.activeInverse AndersonAC.S6.dampedMatrix trialG0
  rw [hM]
  exact Matrix.inv_eq_right_inv hBG.1

theorem activeRealM_isSymm {x : RunRecord d m} {t : ℝ}
    (hD : IsDampedEndpoint x.endpoint x.r t) : (activeRealM x).IsSymm := by
  ext a b
  simp only [Matrix.transpose_apply, activeRealM]
  rw [(hD.1 b.val a.val).1]

/-- The initial inverse of a stopped trial may be rewritten along an equality. -/
theorem stoppedTrial_transport_g0 {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    [MeasurableSpace ι] {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ}
    {g0 g0' : Ω → Matrix ι ι ℂ} {order : ι ≃ Fin (Fintype.card ι)} (h : g0 = g0')
    (q : AndersonAC.S6.StoppedTrial (Ω := Ω) core t r g0 order) :
    ∃ q' : AndersonAC.S6.StoppedTrial (Ω := Ω) core t r g0' order,
      q'.history = q.history ∧ q'.pivot = q.pivot ∧ q'.residual = q.residual ∧
        q'.stop = q.stop ∧ q'.outcome = q.outcome := by
  subst h
  exact ⟨q, rfl, rfl, rfl, rfl, rfl⟩

theorem trueResidual_measurable {M : ℕ → ℕ} (lam : ℝ) (y : Torus d m) (h : ℕ) :
    Measurable (fun ω : RandomSources (Torus d m) M => trueResidual lam ω y h) :=
  (AndersonAC.S2.binarySuffix_measurable lam h).comp
    (Measurable.of_eval fun k => (measurable_pi_apply (Sum.inl (y, k))).comp measurable_fst)

/-- A null flip-stable set is `FlipInvariantNull` (ClearingTrialZ.lean). -/
theorem flipInvariantNull_of_stable {M : ℕ → ℕ} {Z : Set (RandomSources (Torus d m) M)}
    (h0 : sourcesLaw (Torus d m) M Z = 0) (hs : FlipStable (Torus d m) Z) :
    FlipInvariantNull Z :=
  ⟨h0, fun y => ⟨Set.ext fun ω => hs.2.1 y ω, fun n => Set.ext fun ω => hs.2.2 y n ω⟩⟩

/-- **The clearing trial, exact off a null set.** For a damped record, a nonempty core of active
sites, broad damping and `0 < t < 1`, there are a `sourcesLaw`-null set `Z` and a stopped trial
on the active sites with frozen data `(x.r, trialG0 x)`, query history from `⊥`, whose running
residuals are the `λ`-coupled true residuals off `Z` (S6.construct_stopped_trial with the
residuals replaced on `Z` by those of a fixed sample outside `Z`). -/
theorem clrTrial_exists (M : ℕ → ℕ) (x : RunRecord d m) (B : Finset (ActiveSite x))
    (hB : B.Nonempty) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (cP CP : ℝ)
    (hr : AndersonAC.S6.BroadBounds cP CP (fun i : ActiveSite x => x.r i.val))
    (hD : IsDampedEndpoint x.endpoint x.r t) (lam : ℝ) (hlam : lam ≠ 0)
    (order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x))) :
    ∃ Z : Set (RandomSources (Torus d m) M), FlipInvariantNull Z ∧
    ∃ q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B t
        (fun _ i => x.r i) (fun _ => trialG0 x) order,
      (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) ∧
      (∀ k ω, ω ∉ Z → k < q.stop ω →
        q.residual k ω = trueResidual lam ω (q.pivot k ω) (x.prefixLength (q.pivot k ω))) := by
  classical
  have : Nonempty (ActiveSite x) := ⟨hB.choose⟩
  set μ := sourcesLaw (Torus d m) M
  let M0 := activeRealM x
  let ξ : ActiveSite x → RandomSources (Torus d m) M → ℝ :=
    fun i ω => trueResidual lam ω i.val (x.prefixLength i.val)
  have hae := clrTerminal_ae M x.endpoint.active M0 lam hlam x.prefixLength
  set Z0 := {ω : RandomSources (Torus d m) M | ¬ ∀ T : Finset (ActiveSite x),
    IsUnit (clrPrincipal M0 (fun i => ξ i ω) T).det} with hZ0def
  have hZ0 : μ Z0 = 0 := ae_iff.mp hae
  set Z1 := toMeasurable μ Z0
  have hZ1 : μ Z1 = 0 := by rw [measure_toMeasurable]; exact hZ0
  have hZ1m : MeasurableSet Z1 := measurableSet_toMeasurable μ Z0
  set Z := flipSat Z1
  have hZ : μ Z = 0 := flipSat_null hZ1m hZ1
  have hstab : FlipStable (Torus d m) Z := flipSat_stable hZ1m
  have hZm : MeasurableSet Z := hstab.1
  obtain ⟨ω₀, hω₀⟩ : ∃ ω, ω ∉ Z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hu : Z = Set.univ := Set.eq_univ_of_forall hcon
    rw [hu, measure_univ] at hZ
    exact one_ne_zero hZ
  have hgood : ∀ ω, ω ∉ Z → ∀ T : Finset (ActiveSite x),
      IsUnit (clrPrincipal M0 (fun i => ξ i ω) T).det := by
    intro ω hω
    by_contra hcon
    exact hω (subset_flipSat Z1 (subset_toMeasurable μ Z0 hcon))
  let ξ' : ActiveSite x → RandomSources (Torus d m) M → ℝ :=
    fun i => Z.piecewise (fun _ => ξ i ω₀) (ξ i)
  have hξ' : ∀ i, Measurable (ξ' i) := fun i =>
    Measurable.piecewise hZm measurable_const
      (trueResidual_measurable lam i.val (x.prefixLength i.val))
  have hterm : ∀ ω (T : Finset (ActiveSite x)), IsUnit
      (((M0 + Matrix.diagonal (fun i => ξ' i ω)).submatrix
        (fun i : {i // i ∈ T} => (i : ActiveSite x))
        (fun i : {i // i ∈ T} => (i : ActiveSite x))).det) := by
    intro ω T
    by_cases hω : ω ∈ Z
    · have : (fun i => ξ' i ω) = fun i => ξ i ω₀ := by
        funext i; simp only [ξ', Set.piecewise_eq_of_mem _ _ _ hω]
      rw [this]
      exact hgood ω₀ hω₀ T
    · have : (fun i => ξ' i ω) = fun i => ξ i ω := by
        funext i; simp only [ξ', Set.piecewise_eq_of_notMem _ _ _ hω]
      rw [this]
      exact hgood ω hω T
  have hl : AndersonAC.S6.leverageScale t < 2 := by
    unfold AndersonAC.S6.leverageScale
    have : t ^ (1 + AndersonAC.S6.e0) < 1 :=
      Real.rpow_lt_one ht.le ht1 (by norm_num [AndersonAC.S6.e0, AndersonAC.S6.delta])
    linarith
  have hN : 1 ≤ AndersonAC.S6.heatLimit t := by
    unfold AndersonAC.S6.heatLimit
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le
      (by norm_num [AndersonAC.S6.eh, AndersonAC.S6.delta])
  obtain ⟨q, hhist, -, hres, -⟩ := AndersonAC.S6.construct_stopped_trial (Ω := RandomSources (Torus d m) M)
    B t cP CP (fun _ i => x.r i.val) (fun _ => M0) ξ' ⊥ order ht hl hN (fun _ => hr)
    (fun _ => activeRealM_isSymm hD) stronglyMeasurable_const stronglyMeasurable_const hξ'
    bot_le hterm
  have hg : (fun ω : RandomSources (Torus d m) M =>
      AndersonAC.S6.activeInverse M0 t ((fun _ i => x.r i.val : RandomSources (Torus d m) M →
        ActiveSite x → ℂ) ω)) = fun _ => trialG0 x := by
    funext ω
    exact activeInverse_eq_trialG0 hD
  obtain ⟨q', hH, hP, hR, hS, -⟩ := stoppedTrial_transport_g0 hg q
  refine ⟨Z, flipInvariantNull_of_stable hZ hstab, q', fun k => ?_, fun k ω hω hk => ?_⟩
  · rw [hH, hP, hR]; exact hhist k
  · rw [hS] at hk
    rw [hR, hP, hres k ω hk]
    simp only [ξ', Set.piecewise_eq_of_notMem _ _ _ hω, ξ]

/-! ## The bound -/

theorem stageScale_lt_one {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {j m : ℕ} (hj : 1 ≤ j)
    (hm : 1 ≤ m) : stageScale u j m < 1 := by
  unfold stageScale
  have h4j : (4 : ℝ) ≤ 4 ^ j := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
  have h4m : (4 : ℝ) ≤ 4 ^ m := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hm
  have h1 : u / 4 ^ j ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hu.2]
  have h2 : u / 4 ^ m ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hu.2]
  linarith

/-- The record hypotheses of the clearing bound at the clearing block of `(j, y)`: on a
non-aborted record, the C4b good set, disjoint active and terminal sites, the core among the
active sites, and the separation of the other pending sites from the core
(07-assembly.tex:200–209). -/
def ClearingBoundRecord (d : ℕ) {m : ℕ} (cP CP : ℝ) (qlag : ℝ → ℝ)
    (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m)) (n₀ : ℕ) (u E : ℝ) (j : ℕ)
    (y : Torus d m) (x : RunRecord d m) : Prop :=
  x.aborted = false → x ∈ ClearingGood d cP CP qlag geo n₀ u E j ∧
    Disjoint x.endpoint.active x.terminal ∧
    theCore (d := d) (m := m) j u y x ⊆ x.endpoint.active ∧
    ∀ z ∈ x.pending, z ∉ theCore (d := d) (m := m) j u y x →
      ∀ w ∈ theCore (d := d) (m := m) j u y x,
        separationRadius j - inspectionRadius j / 2 < physicalDistance d m z w

/-- **The clearing first-failure bound from the two contracts.** For every geometry parameter
`geo` whose records are damped endpoints at `t_j`, the C4b-Z constants give the bound on every
entering record satisfying `ClearingBoundRecord`. -/
theorem clearingBound_of_contracts (d : ℕ) (hbr : ∀ m, ClearingBridgeAtStatement d m)
    (cP CP : ℝ) (hcP : 0 < cP) (qlag : ℝ → ℝ)
    (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m))
    (hgeo : ∀ {m : ℕ} (n₀ : ℕ) (u : ℝ) (j : ℕ) (x : RunRecord d m), x ∈ geo n₀ u j →
      IsDampedEndpoint x.endpoint x.r (stageScale u j m))
    (hC4 : ClearingTrialStatementZ d (ClearingGood d cP CP qlag geo)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
      ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, ∀ j : ℕ, n₀ < j → j ≤ m / 2 →
      ∀ (y : Torus d m) (M : ℕ → ℕ) (x : RunRecord d m),
      ClearingBoundRecord d cP CP qlag geo n₀ u E j y x →
      sourcesLaw (Torus d m) M
        (localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u y) x) ≤
          ENNReal.ofReal (birthBound c j) := by
  obtain ⟨c, hc, N, hN⟩ := hC4
  refine ⟨c, hc, N, ?_⟩
  intro n₀ m hN0 h4 u hu E j hj hjm y M x hx
  by_cases hemp : x.aborted = true ∨ theCore (d := d) (m := m) j u y x = ∅
  · have h0 : localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u y) x = ∅ := by
      apply empty_firstFail_empty (d := d) (m := m) (n₀ := n₀) (j := j) (u := u) (x := y) (M := M)
      rcases hemp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    rw [h0, measure_empty]
    exact bot_le
  obtain ⟨hab, hne⟩ := not_or.mp hemp
  have habf : x.aborted = false := by simpa using hab
  obtain ⟨hgood, hdisj, hsubA, hsep⟩ := hx habf
  obtain ⟨hmemC, helC⟩ := theCore_spec_of_ne (d := d) (m := m) hne
  classical
  let B : Finset (ActiveSite x) :=
    Finset.univ.filter (fun a : ActiveSite x => a.val ∈ theCore (d := d) (m := m) j u y x)
  have hcore : theCore (d := d) (m := m) j u y x = B.map (Function.Embedding.subtype _) := by
    ext w
    simp only [B, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · intro hw; exact ⟨⟨w, hsubA hw⟩, hw, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ha
  have hBne : B.Nonempty := by
    obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact ⟨⟨w, hsubA hw⟩, by simp [B, hw]⟩
  have hBmem : B.map (Function.Embedding.subtype _) ∈ x.components := hcore ▸ hmemC
  have hel : eligibleCore d B (stageScale u j m) := by
    have h := helC.2.2.1
    unfold eligibleCore at h ⊢
    rw [hcore, Finset.card_map] at h
    exact h
  have hsepB : ∀ z ∈ x.pending, z ∉ B.map (Function.Embedding.subtype _) →
      ∀ w ∈ B.map (Function.Embedding.subtype _),
        separationRadius j - inspectionRadius j / 2 < physicalDistance d m z w := by
    rw [← hcore]; exact hsep
  obtain ⟨order, horder⟩ := exists_activeOrder x
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have hj1 : 1 ≤ j := by omega
  have hm1 : 1 ≤ m := by omega
  have ht : 0 < stageScale u j m := by unfold stageScale; positivity
  have ht1 := stageScale_lt_one hu hj1 hm1
  have hr : AndersonAC.S6.BroadBounds cP CP (fun i : ActiveSite x => x.r i.val) :=
    ⟨hcP, fun i => hgood.1.broad i.val i.property⟩
  obtain ⟨Z, hZ, q, hhist, hres⟩ := clrTrial_exists M x B hBne (stageScale u j m) ht ht1 cP CP hr
    (hgeo n₀ u j x hgood.2) (OAI.Anderson.scaleCoupling n₀ u) (scaleCoupling_ne_zero n₀ hu0)
    order
  have hsch : clearingScheduled j m := hjm
  obtain ⟨hguard, hbound⟩ := hN n₀ m hN0 h4 u hu E j hj hsch M x hgood B hBne hBmem hel hsepB
    order q Z hZ hhist hres
  have hsub : localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u y) x ⊆
      {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} ∪ Z := by
    intro ω hω
    by_cases hωZ : ω ∈ Z
    · exact Or.inr hωZ
    · left
      exact (hbr m n₀ j u y M x B hcore hBne habf hsch hdisj (hgeo n₀ u j x hgood.2) order horder q hhist ω
        (fun k hk => hres k ω hωZ hk) (fun k hk => hguard k ω hωZ hk)).mp hω
  calc sourcesLaw (Torus d m) M (localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u y) x)
      ≤ sourcesLaw (Torus d m) M ({ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} ∪ Z) :=
        measure_mono hsub
    _ ≤ sourcesLaw (Torus d m) M {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} +
          sourcesLaw (Torus d m) M Z := measure_union_le _ _
    _ = sourcesLaw (Torus d m) M {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} := by
        rw [hZ.1, add_zero]
    _ ≤ ENNReal.ofReal (birthBound c j) := hbound

/-- **The clearing first-failure bound, C4b discharged** (`clearingTrialZ_proof` with
`concentrationInput_closed`): conditional only on the sample-by-sample bridge and the record
hypotheses `ClearingBoundRecord` for the geometry `clearingGeo d Ctr`. -/
theorem clearingBound_records (d : ℕ) (hd : 3 ≤ d) (hbr : ∀ m, ClearingBridgeAtStatement d m)
    (cP CP : ℝ) (hcP : 0 < cP) (qlag : ℝ → ℝ) (hqlag : Filter.Tendsto qlag (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (Ctr : ℝ) (hCtr : 1 ≤ Ctr) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
      ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, ∀ j : ℕ, n₀ < j → j ≤ m / 2 →
      ∀ (y : Torus d m) (M : ℕ → ℕ) (x : RunRecord d m),
      ClearingBoundRecord d cP CP qlag (AgentS78Geo.clearingGeo d Ctr) n₀ u E j y x →
      sourcesLaw (Torus d m) M
        (localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u y) x) ≤
          ENNReal.ofReal (birthBound c j) :=
  clearingBound_of_contracts d hbr cP CP hcP qlag (AgentS78Geo.clearingGeo d Ctr)
    (fun _ _ _ _ hx => hx.damped)
    (clearingTrialZ_proof d hd concentrationInput_closed cP CP qlag hcP hqlag Ctr hCtr)

/-- The core of the clearing block of `(j, y)` consists of sites of rank at least that of `y`. -/
theorem theCore_rank_ge {j : ℕ} {u : ℝ} {y : Torus d m} {x : RunRecord d m} :
    ∀ c ∈ theCore (d := d) (m := m) j u y x, (siteRank d m y).val ≤ (siteRank d m c).val := by
  intro c hc
  obtain ⟨Bc, -, hel, hcB⟩ := mem_theCore (d := d) (m := m) (j := j) (u := u) (y := y) x hc
  exact hel.2.1.2 c hcB

theorem two_div_four_pow_lt {t₀ : ℝ} (ht₀ : 0 < t₀) : ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
    2 / (4 : ℝ) ^ j < t₀ := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < t₀ / 2)
    (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨N, fun j hj => ?_⟩
  have h1 : (1 / 4 : ℝ) ^ j ≤ (1 / 4) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have h2 : 2 / (4 : ℝ) ^ j = 2 * (1 / 4) ^ j := by rw [one_div_pow]; ring
  rw [h2]
  linarith

/-- `t_j ≤ 2 · 4^{-j}` for `j ≤ m`. -/
theorem stageScale_le_two_div {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {j m : ℕ} (hjm : j ≤ m) :
    stageScale u j m ≤ 2 / (4 : ℝ) ^ j := by
  unfold stageScale
  have h4j : (0 : ℝ) < 4 ^ j := by positivity
  have hmj : (4 : ℝ) ^ j ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hjm
  have h1 : u / 4 ^ j ≤ 1 / 4 ^ j := div_le_div_of_nonneg_right hu.2 h4j.le
  have h2 : u / 4 ^ m ≤ 1 / 4 ^ j :=
    (div_le_div_of_nonneg_right hu.2 (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) h4j hmj)
  have : 2 / (4 : ℝ) ^ j = 1 / 4 ^ j + 1 / 4 ^ j := by ring
  linarith

/-- **The clearing first-failure bound on the clearing-phase invariant** (`ClearPhaseR` of
agent-s78phase2 at scan position `rank y`, the position at the clearing block of `(j, y)`):
conditional only on the sample-by-sample bridge of muse-s78clear. The constants: `C'` and `t₀`
of `clearPhaseR_good` (from `CA cA PA`), the C4b-Z constant `c` for the lag function
`phaseQlag d C'`, and `N` large enough that `t_j < t₀` for `j > N`. -/
theorem clearingBound_clearPhaseR (d : ℕ) (hd : 3 ≤ d) (hbr : ∀ m, ClearingBridgeAtStatement d m)
    (CA cA PA : ℝ) (hCA : 1 ≤ CA) (hcA : 0 < cA) (hPA : 0 ≤ PA)
    (cP CP : ℝ) (hcP : 0 < cP) (Ctr : ℝ) (hCtr : 1 ≤ Ctr) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
      ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ (E : ℝ) (ρ : ℂ) (C : ℝ) (j : ℕ), n₀ < j →
      j ≤ m / 2 → ∀ (y : Torus d m) (M : ℕ → ℕ) (x : RunRecord d m),
      ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j (siteRank d m y).val x →
      sourcesLaw (Torus d m) M
        (localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u y) x) ≤
          ENNReal.ofReal (birthBound c j) := by
  obtain ⟨C', t₀, hC', ht₀, hgoodR⟩ := clearPhaseR_good hd CA cA PA hCA hcA hPA
  obtain ⟨c, hc, N₁, hN₁⟩ := clearingBound_records d hd hbr cP CP hcP (phaseQlag d C')
    (phaseQlag_tendsto hd C') Ctr hCtr
  obtain ⟨N₂, hN₂⟩ := two_div_four_pow_lt ht₀
  refine ⟨c, hc, max N₁ N₂, ?_⟩
  intro n₀ m hN0 h4 u hu E ρ C j hj hjm y M x hx
  refine hN₁ n₀ m (le_of_max_le_left hN0) h4 u hu E j hj hjm y M x ?_
  intro hab
  have ht : stageScale u j m < t₀ :=
    (stageScale_le_two_div hu (by omega)).trans_lt
      (hN₂ j (by have := le_of_max_le_right hN0; omega))
  obtain ⟨hbroad, h4r, hlag, hcoup, hsepR, hball, hgeo⟩ :=
    hgoodR (m := m) cP CP Ctr n₀ u E ρ C j (siteRank d m y).val x hu ht hx hab
  obtain ⟨D, hpos, -, -, -⟩ := hx hab
  have hrank := theCore_rank_ge (d := d) (m := m) (j := j) (u := u) (y := y) (x := x)
  refine ⟨⟨⟨hbroad, h4r, hlag, hcoup, hball⟩, hgeo⟩, ?_, ?_, ?_⟩
  · rw [hpos.base.activeCompl]
    exact Finset.sdiff_disjoint
  · by_cases hne : theCore (d := d) (m := m) j u y x = ∅
    · rw [hne]; exact Finset.empty_subset _
    · exact (hpos.untouched _ (theCore_spec_of_ne (d := d) (m := m) hne).1 hrank).trans
        hpos.base.pendingActive
  · intro z hz hzC w hw
    have hne : theCore (d := d) (m := m) j u y x ≠ ∅ := Finset.ne_empty_of_mem hw
    exact hsepR _ (theCore_spec_of_ne (d := d) (m := m) hne).1 hrank z hz hzC w hw

end AndersonAC.AgentS78
