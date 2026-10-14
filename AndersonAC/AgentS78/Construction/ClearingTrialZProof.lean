import AndersonAC.AgentS78.Construction.ClearingTrialZGeo
import AndersonAC.AgentS78.Construction.ClearingTrialFinal

/-!
# WP10 construction, C4b off a null set: `clearingTrialZ_proof`

`ClearingTrialStatementZ` (frozen by agent-s78con4, ClearingTrialZ.lean): the trial's residuals
are the true ones only off a flip-invariant null set `Z`. Route: `Z₂ = flipClosure Z` is a
measurable flip-invariant null superset; for a sample `ω₁ ∉ Z` the trial `q₁ = compTrial ψ q`,
`ψ = ω₁` on `Z₂` and `id` elsewhere, repeats at every sample the data of a sample off `Z`, so
Proposition 6.6 applies to it (geometry: `clearingGeometryQ_proof`; residual law:
`ResidualZ.clearingResidualZ`). Part (a) at `ω₁ ∉ Z` is the pivot location of `q₁` at `ω₁`
(`ψ ω₁ = ω₁`); part (b) holds for `q₁` and `q₁ = q` off the null set `Z₂`.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)
open AndersonAC.AgentS78Geo (clearingGeo)
open AndersonAC.AgentS78.ResidualZ (flipClosure compTrial)

/-- **C4b off a null set.** -/
theorem clearingTrialZ_proof (d : ℕ) (hd : 3 ≤ d)
    (hconc : AndersonAC.Blueprint.ConcentrationInput)
    (cP CP : ℝ) (qlag : ℝ → ℝ) (hcP : 0 < cP) (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (Ctr : ℝ) (hCtr : 1 ≤ Ctr) :
    ClearingTrialStatementZ d (ClearingGood d cP CP qlag (clearingGeo d Ctr)) := by
  obtain ⟨c, K, Cloc, hc, hccP, hCPK, hK, hCloc, Ng, hgeoN⟩ :=
    AndersonAC.AgentS78Geo.clearingGeometryQ_proof hd cP CP hcP qlag Ctr hCtr
  set K₁ := max K 4 with hK₁def
  have hK₁ : 1 ≤ K₁ := hK.trans (le_max_left _ _)
  obtain ⟨cConc, hcConc, hvec⟩ := AndersonAC.AgentS6.vectorConcentrationBridge_proof hconc
  obtain ⟨ε, hε, hεpos, t1, ht1, hdr⟩ :=
    leverageDriftUniform_proof AndersonAC.Blueprint.Packages.ward d hd c K₁ Cloc hc hK₁ hCloc
      qlag hqlag
  obtain ⟨t2, ht2, hpr⟩ :=
    preparationUniform_proof d hd c K₁ Cloc cConc hc hK₁ hCloc hcConc qlag ε hqlag hε hεpos
  obtain ⟨t3, ht3, hloc⟩ :=
    AndersonAC.AgentS6.trial_pivots_located.{0} AndersonAC.Blueprint.Packages.ward d c K₁ Cloc hc
  set t0 := min t1 (min t2 t3) with ht0def
  have ht0 : 0 < t0 := lt_min ht1 (lt_min ht2 ht3)
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (half_pos ht0) (by norm_num : (1 / 4 : ℝ) < 1)
  have hκ := AndersonAC.AgentS6.clearingExponent_pos d hd
  refine ⟨AndersonAC.S6.clearingExponent d / 2, half_pos hκ, max Ng N₁, ?_⟩
  intro n₀ m hN hm u hu E j hj hsched M x hx B hB hBmem hBel hsep order q Z hZ hhist hres
  have hNg : Ng ≤ n₀ := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ j := ((le_max_right _ _).trans hN).trans hj.le
  have hj1 : 1 ≤ j := by omega
  have hjm : j ≤ m := (Nat.div_le_self m 2).trans' hsched
  obtain ⟨htlo, hthi⟩ := stage_scale_comparison u j m hu hjm
  have htpos : 0 < (stageScale u j m) := lt_of_le_of_lt (by positivity) htlo
  have htt0 : (stageScale u j m) < t0 := by
    refine lt_of_le_of_lt hthi ?_
    have h4 : (1 / 4 : ℝ) ^ j ≤ (1 / 4 : ℝ) ^ N₁ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hN₁
    have : 2 / (4 : ℝ) ^ j = 2 * (1 / 4 : ℝ) ^ j := by
      rw [div_eq_mul_inv, one_div, inv_pow]
    rw [this]
    linarith
  have htt1 : (stageScale u j m) < t1 := lt_of_lt_of_le htt0 (min_le_left _ _)
  have htt2 : (stageScale u j m) < t2 :=
    lt_of_lt_of_le htt0 ((min_le_right _ _).trans (min_le_left _ _))
  have htt3 : (stageScale u j m) < t3 :=
    lt_of_lt_of_le htt0 ((min_le_right _ _).trans (min_le_right _ _))
  have hxg : ClearingGoodAt cP CP qlag n₀ u j x := hx.1
  -- consequences of Proposition 6.6 and of the pivot location for any trial with local input
  have hcons : ∀ (q₁ : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B
        (stageScale u j m) (fun _ i => x.r i) (fun _ => trialG0 x) order)
      (coll : ℕ → RandomSources (Torus d m) M → ActiveSite x → ActiveSite x → ℝ),
      AndersonAC.S6.TrialLocalInput (truncTrial q₁) (sourcesLaw (Torus d m) M) d c K₁ Cloc
        (fun a b : ActiveSite x => physicalDistance d m a.val b.val) coll (inspectionRadius j) →
      q₁.history 0 = ⊥ →
      (∀ k ω, k < q₁.stop ω → AndersonAC.S6.distanceToCore
        (fun a b : ActiveSite x => physicalDistance d m a.val b.val) B (q₁.pivot k ω) <
          inspectionRadius j / 2) ∧
      sourcesLaw (Torus d m) M {ω | q₁.outcome ω = AndersonAC.S6.TrialOutcome.fail} ≤
        ENNReal.ofReal (birthBound (AndersonAC.S6.clearingExponent d / 2) j) := by
    intro q₁ coll hL h0₁
    -- transport to `Fin (Fintype.card (ActiveSite x))`
    obtain ⟨e, -⟩ : ∃ _e : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)), True :=
      ⟨Fintype.equivFin _, trivial⟩
    obtain ⟨q', hh', hs', ho', -, hp', hL'⟩ := TrialReindex.trialReindex_proof
      (Fintype.card (ActiveSite x)) e B (stageScale u j m) (fun _ i => x.r i) (fun _ => trialG0 x)
      order (truncTrial q₁)
    have hL'' := hL' (sourcesLaw (Torus d m) M) d c K₁ Cloc _ coll _ hL
    have hcard1 : 1 ≤ (B.map e.toEmbedding).card := by
      rw [Finset.card_map]; exact hB.card_pos
    have hcard2 : ((B.map e.toEmbedding).card : ℝ) ≤ AndersonAC.S6.coreCap d (stageScale u j m) := by
      rw [Finset.card_map]; unfold AndersonAC.S6.coreCap; rw [← nu_eq]; exact hBel
    have hbroad : ∀ ω : RandomSources (Torus d m) M,
        AndersonAC.S6.BroadBounds c K₁ (fun i : Fin (Fintype.card (ActiveSite x)) => x.r (e.symm i).val) := by
      intro _
      refine ⟨hc, fun i => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hxg.broad _ (e.symm i).property
      exact ⟨h1.trans (hCPK.trans (le_max_left _ _)), hccP.trans h2,
        h3.trans (hCPK.trans (le_max_left _ _))⟩
    have hfourth : ∀ (_ω : RandomSources (Torus d m) M) (i : Fin (Fintype.card (ActiveSite x))),
        AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse (stageScale u j m)
          ((trialG0 x).submatrix e.symm e.symm)) i ≤ (4 / 5) * AndersonAC.S6.fourthCap (stageScale u j m) := by
      intro _ i
      refine le_of_eq_of_le ?_ (hxg.fourth (e.symm i))
      simp only [AndersonAC.S6.fourthRow, AndersonAC.S6.scaledInverse, Matrix.smul_apply,
        Matrix.submatrix_apply]
      exact Equiv.sum_comp e.symm
        (fun a => ‖(Real.sqrt (stageScale u j m) : ℂ) • trialG0 x (e.symm i) a‖ ^ 4)
    have hlag : ∀ (_ω : RandomSources (Torus d m) M) (i : Fin (Fintype.card (ActiveSite x))),
        ‖(trialG0 x).submatrix e.symm e.symm i i - x.r (e.symm i).val‖ ≤
          qlag (stageScale u j m) * (stageScale u j m) ^ AndersonAC.S6.betaW :=
      fun _ i => hxg.lag _ (e.symm i).property
    have hdrift' := hdr (sourcesLaw (Torus d m) M) (Fintype.card (ActiveSite x)) (B.map e.toEmbedding) (stageScale u j m) _ _ _ q' _ _ _ htpos
      htt1 hcard1 hcard2 hbroad hfourth hlag hL''
    have hfail := hpr (sourcesLaw (Torus d m) M) (Fintype.card (ActiveSite x)) (B.map e.toEmbedding) (stageScale u j m) _ _ _ q' _ _ _ htpos
      htt2 hcard1 hcard2 hbroad hfourth hlag hL'' (hvec _ _ _) hdrift'
    have hloc' := hloc (sourcesLaw (Torus d m) M) (Fintype.card (ActiveSite x)) _ (stageScale u j m) _ _ _ q' _ _ _ htpos htt3 hbroad hL''
    refine ⟨fun k ω hk => ?_, ?_⟩
    · have h1 := hloc' k ω (by rw [hs']; exact hk)
      rw [hp', distanceToCore_map e
        (fun a b : ActiveSite x => physicalDistance d m a.val b.val)] at h1
      exact h1
    · have ho'' : q'.outcome = q₁.outcome := ho'
      rw [← ho'']
      have hA : MeasurableSet {ω | q'.outcome ω = AndersonAC.S6.TrialOutcome.fail} :=
        q'.outcome_measurable
          (MeasurableSpace.measurableSet_top (s := {AndersonAC.S6.TrialOutcome.fail}))
      have h0 : q'.history 0 = ⊥ := by
        rw [hh']; exact h0₁
      rw [h0] at hfail
      exact (measure_le_of_condProb_bot _ hA hfail).trans
        (ENNReal.ofReal_le_ofReal (exp_le_birthBound_clr hκ hj1 htpos hthi))
  -- the flip closure of `Z`
  obtain ⟨Z₂, hZ₂⟩ : ∃ Z₂, Z₂ = flipClosure (Torus d m) Z := ⟨_, rfl⟩
  have hZsub : Z ⊆ Z₂ := hZ₂ ▸ ResidualZ.subset_flipClosure _ Z
  have hZ₂m : MeasurableSet Z₂ := hZ₂ ▸ ResidualZ.flipClosure_measurable _ Z
  have hZ₂null : sourcesLaw (Torus d m) M Z₂ = 0 := hZ₂ ▸ ResidualZ.flipClosure_null _ Z hZ.1
  -- the composed trial for a sample `ω₁ ∉ Z`
  have hkey : ∀ ω₁, ω₁ ∉ Z → ∃ q₁ : AndersonAC.S6.StoppedTrial
      (Ω := RandomSources (Torus d m) M) B (stageScale u j m) (fun _ i => x.r i)
        (fun _ => trialG0 x) order,
      (∀ ω, ω ∉ Z₂ → q₁.outcome ω = q.outcome ω) ∧ q₁.stop ω₁ = q.stop ω₁ ∧
      (∀ k, q₁.pivot k ω₁ = q.pivot k ω₁) ∧ q₁.history 0 = ⊥ ∧
      ∃ coll, AndersonAC.S6.TrialLocalInput (truncTrial q₁) (sourcesLaw (Torus d m) M) d c K₁
        Cloc (fun a b : ActiveSite x => physicalDistance d m a.val b.val) coll
        (inspectionRadius j) := by
    intro ω₁ hω₁
    classical
    let ψ : RandomSources (Torus d m) M → RandomSources (Torus d m) M :=
      fun ω => if ω ∈ Z₂ then ω₁ else ω
    have hψ : Measurable ψ := Measurable.ite hZ₂m measurable_const measurable_id
    have hψoff : ∀ ω, ω ∉ Z₂ → ψ ω = ω := fun ω h => if_neg h
    have hψon : ∀ ω, ω ∈ Z₂ → ψ ω = ω₁ := fun ω h => if_pos h
    have hψ₁ : ψ ω₁ = ω₁ := by
      by_cases h : ω₁ ∈ Z₂
      · exact hψon _ h
      · exact hψoff _ h
    have hψψ : ∀ ω, ψ (ψ ω) = ψ ω := by
      intro ω
      by_cases h : ω ∈ Z₂
      · rw [hψon _ h, hψ₁]
      · rw [hψoff _ h, hψoff _ h]
    have hψZ : ∀ ω, ψ ω ∉ Z := by
      intro ω
      by_cases h : ω ∈ Z₂
      · rw [hψon _ h]; exact hω₁
      · rw [hψoff _ h]; exact fun h' => h (hZsub h')
    let q₁ : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B (stageScale u j m)
        (fun _ i => x.r i) (fun _ => trialG0 x) order := compTrial ψ hψ q
    have hhist₁ : ∀ k, q₁.history k = AndersonAC.S6.queryHistory ⊥ q₁.pivot q₁.residual k :=
      ResidualZ.compTrial_history ψ hψ q hhist
    have hres₁ : ∀ k ω, k < q₁.stop ω → q₁.residual k ω =
        Residual.siteSuffix (Torus d m) (OAI.Anderson.scaleCoupling n₀ u)
          (x.prefixLength (q₁.pivot k ω).val) (q₁.pivot k ω).val (ψ ω) :=
      fun k ω hk => hres k (ψ ω) (hψZ ω) hk
    have hq : ResidualZ.LawHypZ q₁ Subtype.val (OAI.Anderson.scaleCoupling n₀ u)
        (fun i => x.prefixLength i.val) Z₂ :=
      { hist := hhist₁
        inj := Subtype.val_injective
        res := fun k ω hωZ hk => by
          have := hres₁ k ω hk
          rwa [hψoff ω hωZ] at this
        null := hZ₂null
        site := fun y ω => hZ₂ ▸ ResidualZ.flipClosure_site _ Z y ω
        digit := fun y n ω => hZ₂ ▸ ResidualZ.flipClosure_digit _ Z y n ω
        const := fun ω ω' hω hω' => by
          have h1 : ψ ω = ψ ω' := by rw [hψon _ hω, hψon _ hω']
          refine ⟨?_, fun k => ⟨?_, ?_⟩⟩
          · show q.stop (ψ ω) = q.stop (ψ ω'); rw [h1]
          · show q.pivot k (ψ ω) = q.pivot k (ψ ω'); rw [h1]
          · show q.residual k (ψ ω) = q.residual k (ψ ω'); rw [h1] }
    have hrep : ∀ ω, ∃ ω', (∀ k, k < q₁.stop ω' → q₁.residual k ω' =
        Residual.siteSuffix (Torus d m) (OAI.Anderson.scaleCoupling n₀ u)
          (x.prefixLength (q₁.pivot k ω').val) (q₁.pivot k ω').val ω') ∧
        q₁.stop ω = q₁.stop ω' ∧
        ∀ k, q₁.pivot k ω = q₁.pivot k ω' ∧ q₁.residual k ω = q₁.residual k ω' := by
      intro ω
      refine ⟨ψ ω, fun k hk => ?_, ?_, fun k => ⟨?_, ?_⟩⟩
      · have := hres₁ k (ψ ω) hk
        rwa [hψψ] at this
      · show q.stop (ψ ω) = q.stop (ψ (ψ ω)); rw [hψψ]
      · show q.pivot k (ψ ω) = q.pivot k (ψ (ψ ω)); rw [hψψ]
      · show q.residual k (ψ ω) = q.residual k (ψ (ψ ω)); rw [hψψ]
    obtain ⟨coll, hG⟩ := hgeoN n₀ m hNg hm u hu E j hj hsched M x hx B hB hBmem hBel order q₁
    have hR := ResidualZ.clearingResidualZ hu hj hsched hxg hB hBmem hsep q₁ hq hrep
    have hL := trialLocalInput_of_split (hG.trunc.mono_K (le_max_left K 4) htpos) hR
      (le_max_right K 4) htpos
    refine ⟨q₁, fun ω hω => ?_, ?_, fun k => ?_, ?_, coll, hL⟩
    · show q.outcome (ψ ω) = q.outcome ω; rw [hψoff ω hω]
    · show q.stop (ψ ω₁) = q.stop ω₁; rw [hψ₁]
    · show q.pivot k (ψ ω₁) = q.pivot k ω₁; rw [hψ₁]
    · show (q.history 0).comap ψ = ⊥
      rw [hhist 0, queryHistory_zero, MeasurableSpace.comap_bot]
  refine ⟨fun k ω hωZ hk => ?_, ?_⟩
  · -- (a) location and non-pending, at a sample off `Z`
    obtain ⟨q₁, -, hst, hpv, h0, coll, hL⟩ := hkey ω hωZ
    have h1 := (hcons q₁ coll hL h0).1 k ω (by rw [hst]; exact hk)
    rw [hpv] at h1
    obtain ⟨y, hyB, hy⟩ := exists_near_of_distanceToCore_lt hB h1
    have hnear : physicalDistance d m (q.pivot k ω).val y.val ≤ inspectionRadius j / 2 := hy.le
    refine ⟨fun hpend => ?_, y, hyB, hnear⟩
    obtain ⟨_, hnotcore, -⟩ := q.heat k ω hk
    have hnotB : (q.pivot k ω).val ∉ B.map (Function.Embedding.subtype _) := by
      rw [Finset.mem_map]
      rintro ⟨a, ha, hav⟩
      exact hnotcore (Subtype.val_injective hav ▸ ha)
    have hRl : inspectionRadius j < separationRadius j := by
      unfold inspectionRadius separationRadius
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    refine localized_pivot_excludes_old_marks (B.map (Function.Embedding.subtype _))
      (x.pending.filter (fun z => z ∉ B.map (Function.Embedding.subtype _))) _
      (separationRadius j) (inspectionRadius j) hRl
      ⟨y.val, Finset.mem_map_of_mem _ hyB, hnear⟩ ?_
      (Finset.mem_filter.mpr ⟨hpend, hnotB⟩)
    intro z hz y' hy'
    rw [Finset.mem_filter] at hz
    exact hsep z hz.1 hz.2 y' hy'
  · -- (b) the failure probability, through a composed trial equal to `q` off `Z₂`
    obtain ⟨ω₁, hω₁⟩ : ∃ ω₁, ω₁ ∉ Z := by
      by_contra hall
      push_neg at hall
      have hZu : Z = Set.univ := Set.eq_univ_of_forall hall
      have := hZ.1
      rw [hZu, measure_univ] at this
      exact one_ne_zero this
    obtain ⟨q₁, hout, -, -, h0, coll, hL⟩ := hkey ω₁ hω₁
    have hb := (hcons q₁ coll hL h0).2
    have hsub : {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} ⊆
        {ω | q₁.outcome ω = AndersonAC.S6.TrialOutcome.fail} ∪ Z₂ := by
      intro ω hω
      by_cases h : ω ∈ Z₂
      · exact Or.inr h
      · left
        show q₁.outcome ω = _
        rw [hout ω h]; exact hω
    calc sourcesLaw (Torus d m) M {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail}
        ≤ sourcesLaw (Torus d m) M ({ω | q₁.outcome ω = AndersonAC.S6.TrialOutcome.fail} ∪ Z₂) :=
          measure_mono hsub
      _ ≤ sourcesLaw (Torus d m) M {ω | q₁.outcome ω = AndersonAC.S6.TrialOutcome.fail} +
          sourcesLaw (Torus d m) M Z₂ := measure_union_le _ _
      _ ≤ _ := by rw [hZ₂null, add_zero]; exact hb

end AndersonAC.AgentS78
