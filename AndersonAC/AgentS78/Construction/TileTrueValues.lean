import AndersonAC.AgentS78.Construction.TrueValues
import AndersonAC.AgentS78.Construction.RunBasics
import AndersonAC.S2.Binary

/-!
# true values along a tile block

The tile block adds either the next true digit or the true binary suffix. This module
connects those increments to the `TrueValues` record invariant.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer binaryPrefix binarySuffix binaryValue signValue querySigns)

variable {d m : ℕ}

private theorem sqrt_four_pow (n : ℕ) : Real.sqrt ((4 : ℝ) ^ n) = (2 : ℝ) ^ n := by
  have hpow : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by congr 1; norm_num
      _ = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]
      _ = ((2 : ℝ) ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, ← pow_mul]
  rw [hpow, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

private theorem digitAmp_eq_scaleCoupling (n₀ j : ℕ) (u : ℝ) (hj : n₀ < j) :
    digitAmp u (j - 1) = OAI.Anderson.scaleCoupling n₀ u / (2 : ℝ) ^ (j - n₀) := by
  have hj1 : 1 ≤ j := by omega
  have hjs : j = j - 1 + 1 := by omega
  have hrad : 3 * (u / (4 : ℝ) ^ (j - 1)) / 4 = (3 * u) / (4 : ℝ) ^ j := by
    have hpow : (4 : ℝ) ^ j = (4 : ℝ) ^ (j - 1) * 4 := by
      rw [hjs, pow_succ]
      exact congrArg (fun n : ℕ => (4 : ℝ) ^ n * 4) (by omega)
    rw [hpow]
    field_simp
  rw [digitAmp, hrad, Real.sqrt_div' _ (pow_nonneg (by norm_num) _), sqrt_four_pow]
  rw [OAI.Anderson.scaleCoupling, div_div, ← pow_add, Nat.add_sub_of_le hj.le]

private theorem binaryPrefix_succ (c : ℝ) (h : ℕ) (a : ℕ → Bool) :
    binaryPrefix c (h + 1) a = binaryPrefix c h a +
      c / (2 : ℝ) ^ (h + 1) * signValue (a h) := by
  simp [binaryPrefix, Finset.sum_range_succ]

private theorem tileAnswer_trueDigit (P : TilePlan d m) (j : ℕ)
    (M : ℕ → ℕ) (ω : RandomSources (Torus d m) M) (L : List (Query (Torus d m)))
    (i : Torus d m) (h : ℕ) :
    tileIncrement P j (Query.trueDigit i h)
        (localAnswer (Torus d m) M L (Query.trueDigit i h) ω) =
      digitAmp P.u (j - 1) * signValue (trueDigits ω i h) := by
  simp [tileIncrement, answeredSign, localAnswer, querySigns, trueDigits]

private theorem tileAnswer_trueSuffix (P : TilePlan d m) (j : ℕ)
    (M : ℕ → ℕ) (ω : RandomSources (Torus d m) M) (L : List (Query (Torus d m)))
    (i : Torus d m) (h : ℕ) :
    tileIncrement P j (Query.trueSuffix i h)
        (localAnswer (Torus d m) M L (Query.trueSuffix i h) ω) =
      binarySuffix (couplingOf P.u P.n₀) h (trueDigits ω i) := by
  simp only [tileIncrement]
  unfold binarySuffix
  apply tsum_congr
  intro k
  simp [answeredSign, localAnswer, querySigns, trueDigits]

private theorem scalarStep_site_none (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (ζ : ℝ) : (scalarStep P j T s i ζ).2.site = none := by
  unfold scalarStep
  by_cases hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
  · simp [hok]
  · by_cases hj : m / 2 < j <;> simp [hok, failTrial, hj, trialScratch]

private theorem tileSiteAt_mem (S : Finset (Torus d m)) {v : ℕ} {i : Torus d m}
    (h : siteAt S v = some i) : i ∈ S := by
  unfold siteAt at h
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  rcases hv : L[v]? with _ | a
  · rw [hv] at h
    cases h
  rw [hv] at h
  simp only [Option.map_some, Option.some.injEq] at h
  obtain ⟨hvl, hva⟩ := List.getElem?_eq_some_iff.mp hv
  have hmem : L[v] ∈ S.map (siteRank d m).toEmbedding :=
    (Finset.mem_sort _).mp (List.getElem_mem hvl)
  rw [hva] at hmem
  obtain ⟨b, hb, hbe⟩ := Finset.mem_map.mp hmem
  rw [← h, ← hbe]
  simpa using hb

private def TileExposure (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) : Prop :=
  ∀ i, s.2.site = some i →
    i ∈ tileSites (P.cover j) T ∧ i ∈ x.endpoint.active ∧
      ((i, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live

private theorem exposedSite_info (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (v : Option ℕ) (i : Torus d m)
    (h : exposedSite P j T s v = some i) :
    i ∈ tileSites (P.cover j) T ∧ i ∈ s.1.endpoint.active ∧
      ((i, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live := by
  unfold exposedSite at h
  cases v with
  | none => simp at h
  | some v =>
      cases hv : siteAt (tileSites (P.cover j) T) v with
      | none => simp [hv] at h
      | some i' =>
          simp only [hv] at h
          split_ifs at h with hcond
          · have heq : i' = i := Option.some.inj h
            subst i'
            exact ⟨tileSiteAt_mem _ hv, hcond.1, hcond.2⟩

private theorem tileQuery_site_not_nextOrder (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (o : ℕ) (hsite : s.2.site = some i) :
    tileQuery P j T s ≠ Query.nextOrder o := by
  simp only [tileQuery, hsite]
  split_ifs <;> simp

private theorem tileExposure_of_reach (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m)
    (hreach : BlockReach (tileBlock P j T) x s) : TileExposure P j T x s := by
  induction hreach with
  | enter =>
      intro i hi
      simp only [tileBlock] at hi
      split_ifs at hi <;> cases hi
  | @step s a hreach hnot ih =>
      have hactive := (tileFreshMono_reach P j T x s hreach).2.2.2.2
      rw [tileBlock_update_running P j T s a hnot]
      let s₀ := (s.1, logQuery (tileQuery P j T s) s.2)
      change TileExposure P j T x
        (tileStep P j T s₀ (tileQuery P j T s) a)
      have hi₀ : TileExposure P j T x s₀ := by
        simpa [TileExposure, s₀, logQuery] using ih
      intro i hi
      change (tileStep P j T s₀ (tileQuery P j T s) a).2.site = some i at hi
      cases hs : s.2.site with
      | none =>
          have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
          cases hq : tileQuery P j T s with
          | nextOrder o =>
              have hi' : (tileStep P j T s₀ (Query.nextOrder o) a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              have hobs : exposedSite P j T s₀ a.2 = some i := by
                simpa [tileStep, hs₀] using hi'
              obtain ⟨hmem, hact, hlive⟩ := exposedSite_info P j T s₀ a.2 i hobs
              refine ⟨hmem, ?_, ?_⟩
              · rw [← hactive]
                exact hact
              · simpa [tileStep] using hlive
          | decision =>
              have hi' : (tileStep P j T s₀ Query.decision a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              simp [tileStep, hs₀, commitTrial] at hi'
          | trueDigit i' h =>
              have hi' : (tileStep P j T s₀ (Query.trueDigit i' h) a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              simp [tileStep, hs₀] at hi'
          | auxiliary k =>
              have hi' : (tileStep P j T s₀ (Query.auxiliary k) a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              simp [tileStep, hs₀] at hi'
          | trueSuffix i' h =>
              have hi' : (tileStep P j T s₀ (Query.trueSuffix i' h) a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              simp [tileStep, hs₀] at hi'
      | some i₀ =>
          have hs₀ : s₀.2.site = some i₀ := by simp [s₀, logQuery, hs]
          cases hq : tileQuery P j T s with
          | nextOrder o =>
              exact (tileQuery_site_not_nextOrder P j T s i₀ o hs hq).elim
          | decision =>
              have hi' : (tileStep P j T s₀ Query.decision a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              simp [tileStep, hs₀] at hi'
          | trueDigit i' h =>
              have hi' : (tileStep P j T s₀ (Query.trueDigit i' h) a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              have hnone : (tileStep P j T s₀ (Query.trueDigit i' h) a).2.site = none := by
                simp [tileStep, hs₀, scalarStep_site_none]
              rw [hnone] at hi'
              cases hi'
          | auxiliary k =>
              have hi' : (tileStep P j T s₀ (Query.auxiliary k) a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              have hnone : (tileStep P j T s₀ (Query.auxiliary k) a).2.site = none := by
                simp [tileStep, hs₀, scalarStep_site_none]
              rw [hnone] at hi'
              cases hi'
          | trueSuffix i' h =>
              have hi' : (tileStep P j T s₀ (Query.trueSuffix i' h) a).2.site = some i := by
                simpa [hq, tileStep, hs₀] using hi
              have hnone : (tileStep P j T s₀ (Query.trueSuffix i' h) a).2.site = none := by
                simp [tileStep, hs₀, scalarStep_site_none]
              rw [hnone] at hi'
              cases hi'

private theorem tileQuery_site_not_terminal (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (q : Query (Torus d m)) (hsite : s.2.site = some i)
    (hq : tileQuery P j T s = q) (hneq : q ≠ Query.decision) : i ∉ s.1.terminal := by
  by_contra hterm
  have hna : ¬ activeIn P j T s.1 i := by
    intro ha
    exact ha.2.2 hterm
  have hdec : tileQuery P j T s = Query.decision := by
    simp [tileQuery, hsite, hna]
  exact hneq (hq.symm.trans hdec)

private theorem tileQuery_site_active (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (q : Query (Torus d m)) (hsite : s.2.site = some i)
    (hq : tileQuery P j T s = q) (hneq : q ≠ Query.decision) : activeIn P j T s.1 i := by
  by_contra hna
  have hdec : tileQuery P j T s = Query.decision := by
    simp [tileQuery, hsite, hna]
  exact hneq (hq.symm.trans hdec)

private theorem scalarStep_other_site (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (site target : Torus d m) (ζ : ℝ) (hne : target ≠ site)
    (hcons : s.2.consumed target = false) (hadd : s.2.added target = 0) :
    (scalarStep P j T s site ζ).2.consumed target = false ∧
      (scalarStep P j T s site ζ).2.added target = 0 := by
  unfold scalarStep
  by_cases hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (site, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (site, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (site, false) (ζ / Real.sqrt (sweepW P.u m j)))
  · rw [if_pos hok]
    simp [Function.update_of_ne hne, hcons, hadd]
  · rw [if_neg hok]
    by_cases hj : m / 2 < j <;> simp [hj, failTrial, trialScratch, hcons, hadd]

private theorem scalarStep_other_success (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (site target : Torus d m) (ζ : ℝ) (hne : target ≠ site)
    (hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (site, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (site, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (site, false) (ζ / Real.sqrt (sweepW P.u m j)))) :
    (scalarStep P j T s site ζ).2.consumed target = s.2.consumed target ∧
      (scalarStep P j T s site ζ).2.added target = s.2.added target := by
  unfold scalarStep
  rw [if_pos hok]
  simp [Function.update_of_ne hne]

private theorem scalarStep_trialOk_of_noFail (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (ζ : ℝ)
    (hff : (scalarStep P j T s i ζ).2.firstFail = false) :
    trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j))) := by
  by_cases hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
  · exact hok
  · have hfail : (failTrial P j T s).2.firstFail = true := by
      unfold failTrial
      split_ifs <;> rfl
    have htrue : (scalarStep P j T s i ζ).2.firstFail = true := by
      unfold scalarStep
      rw [if_neg hok]
      exact hfail
    rw [htrue] at hff
    cases hff

private theorem scalarStep_success_live (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (ζ : ℝ)
    (hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))) :
    ((scalarStep P j T s i ζ).2.seq.state ((scalarStep P j T s i ζ).2.seq.length)).live =
      (s.2.seq.state s.2.seq.length).live.erase (i, false) := by
  unfold scalarStep
  rw [if_pos hok]
  simp [extendSeq, stepLive]

private def TilePathScratch (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m) : Prop :=
  TileExposure P j T x s ∧
    (∀ i, ¬ (i ∈ tileSites (P.cover j) T ∧ i ∈ x.endpoint.active) →
      s.2.consumed i = false ∧ s.2.added i = 0) ∧
    (∀ i, i ∈ x.terminal → s.2.consumed i = false ∧ s.2.added i = 0)

private theorem tileStep_keepScratch (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (q : Query (Torus d m)) (a : Answer (Torus d m))
    (h : (∃ o, q = Query.nextOrder o) ∨ q = Query.decision ∨ s.2.site = none) :
    (tileStep P j T s q a).2.consumed = s.2.consumed ∧
      (tileStep P j T s q a).2.added = s.2.added := by
  rcases h with ⟨o, rfl⟩ | hq | hs
  · simp [tileStep]
  · subst q
    cases hs : s.2.site <;> simp [tileStep, hs, commitTrial]
  · cases q with
    | nextOrder o => simp [tileStep]
    | decision => cases hsite : s.2.site <;> simp [tileStep, hsite, commitTrial]
    | trueDigit i k => simp [tileStep, hs]
    | auxiliary k => simp [tileStep, hs]
    | trueSuffix i k => simp [tileStep, hs]

private theorem tileStep_keepScratchSeq (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (q : Query (Torus d m)) (a : Answer (Torus d m))
    (h : (∃ o, q = Query.nextOrder o) ∨ q = Query.decision ∨ s.2.site = none) :
    (tileStep P j T s q a).2.added = s.2.added ∧
      (tileStep P j T s q a).2.consumed = s.2.consumed ∧
      (tileStep P j T s q a).2.seq = s.2.seq := by
  rcases h with ⟨o, rfl⟩ | hq | hs
  · simp [tileStep]
  · subst q
    cases hs : s.2.site <;> simp [tileStep, hs, commitTrial]
  · cases q with
    | nextOrder o => simp [tileStep]
    | decision => cases hsite : s.2.site <;> simp [tileStep, hsite, commitTrial]
    | trueDigit i k => simp [tileStep, hs]
    | auxiliary k => simp [tileStep, hs]
    | trueSuffix i k => simp [tileStep, hs]

private theorem tilePathScratch_of_reach (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (s : RunRecord d m × TileScratch d m)
    (hreach : BlockReach (tileBlock P j T) x s) : TilePathScratch P j T x s := by
  induction hreach with
  | enter =>
      cases habx : x.aborted <;>
        simp [TilePathScratch, TileExposure, tileBlock, habx, initScratch]
  | @step s a hreach hnot ih =>
      have hfresh := tileFreshMono_reach P j T x s hreach
      have hu := tileBlock_update_running P j T s a hnot
      let s₀ := (s.1, logQuery (tileQuery P j T s) s.2)
      have hu' : (tileBlock P j T).update s a =
          tileStep P j T s₀ (tileQuery P j T s) a := by
        simpa [s₀] using hu
      have hi₀ : TilePathScratch P j T x s₀ := by
        simpa [TilePathScratch, TileExposure, s₀, logQuery] using ih
      have hreach' : BlockReach (tileBlock P j T) x ((tileBlock P j T).update s a) :=
        BlockReach.step _ _ hreach hnot
      have hExp' := tileExposure_of_reach P j T x _ hreach'
      rw [hu'] at hExp'
      rw [hu']
      refine ⟨hExp', ?_, ?_⟩
      · intro i hi
        cases hq : tileQuery P j T s with
        | nextOrder o =>
            have hkeep := tileStep_keepScratch P j T s₀ (Query.nextOrder o) a
              (Or.inl ⟨o, rfl⟩)
            rw [hkeep.1, hkeep.2]
            exact hi₀.2.1 i hi
        | decision =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ Query.decision a
                  (Or.inr (Or.inl rfl))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.1 i hi
            | some ii =>
                have hkeep := tileStep_keepScratch P j T s₀ Query.decision a
                  (Or.inr (Or.inl rfl))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.1 i hi
        | trueDigit qi k =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ (Query.trueDigit qi k) a
                  (Or.inr (Or.inr hs₀))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.1 i hi
            | some site =>
                have hs₀ : s₀.2.site = some site := by simp [s₀, logQuery, hs]
                have hloc := hi₀.1 site hs₀
                by_cases hie : i = site
                · subst i
                  exact False.elim (hi ⟨hloc.1, hloc.2.1⟩)
                · have hzero := hi₀.2.1 i hi
                  have hout := scalarStep_other_site P j T s₀ site i
                    (tileIncrement P j (Query.trueDigit qi k) a) hie hzero.1 hzero.2
                  have hstep : tileStep P j T s₀ (Query.trueDigit qi k) a =
                      scalarStep P j T s₀ site (tileIncrement P j (Query.trueDigit qi k) a) := by
                    simp [tileStep, hs₀]
                  rw [hstep]
                  exact hout
        | auxiliary k =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ (Query.auxiliary k) a
                  (Or.inr (Or.inr hs₀))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.1 i hi
            | some ii =>
                have hs₀ : s₀.2.site = some ii := by simp [s₀, logQuery, hs]
                have hloc := hi₀.1 ii hs₀
                by_cases hie : i = ii
                · subst i
                  exact False.elim (hi ⟨hloc.1, hloc.2.1⟩)
                · have hzero := hi₀.2.1 i hi
                  have hout := scalarStep_other_site P j T s₀ ii i
                    (tileIncrement P j (Query.auxiliary k) a) hie hzero.1 hzero.2
                  have hstep : tileStep P j T s₀ (Query.auxiliary k) a =
                      scalarStep P j T s₀ ii (tileIncrement P j (Query.auxiliary k) a) := by
                    simp [tileStep, hs₀]
                  rw [hstep]
                  exact hout
        | trueSuffix qi k =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ (Query.trueSuffix qi k) a
                  (Or.inr (Or.inr hs₀))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.1 i hi
            | some site =>
                have hs₀ : s₀.2.site = some site := by simp [s₀, logQuery, hs]
                have hloc := hi₀.1 site hs₀
                by_cases hie : i = site
                · subst i
                  exact False.elim (hi ⟨hloc.1, hloc.2.1⟩)
                · have hzero := hi₀.2.1 i hi
                  have hout := scalarStep_other_site P j T s₀ site i
                    (tileIncrement P j (Query.trueSuffix qi k) a) hie hzero.1 hzero.2
                  have hstep : tileStep P j T s₀ (Query.trueSuffix qi k) a =
                      scalarStep P j T s₀ site (tileIncrement P j (Query.trueSuffix qi k) a) := by
                    simp [tileStep, hs₀]
                  rw [hstep]
                  exact hout
      · intro i hi
        cases hq : tileQuery P j T s with
        | nextOrder o =>
            have hkeep := tileStep_keepScratch P j T s₀ (Query.nextOrder o) a
              (Or.inl ⟨o, rfl⟩)
            rw [hkeep.1, hkeep.2]
            exact hi₀.2.2 i hi
        | decision =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ Query.decision a
                  (Or.inr (Or.inl rfl))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.2 i hi
            | some ii =>
                have hkeep := tileStep_keepScratch P j T s₀ Query.decision a
                  (Or.inr (Or.inl rfl))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.2 i hi
        | trueDigit qi k =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ (Query.trueDigit qi k) a
                  (Or.inr (Or.inr hs₀))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.2 i hi
            | some site =>
                have hs₀ : s₀.2.site = some site := by simp [s₀, logQuery, hs]
                have hq' : tileQuery P j T s = Query.trueDigit qi k := by simpa using hq
                have hnotTerm := tileQuery_site_not_terminal P j T s site _ hs hq'
                  (by intro h; cases h)
                have hcurrent : i ∈ s.1.terminal := hfresh.2.1 hi
                by_cases hie : i = site
                · subst i
                  exact False.elim (hnotTerm hcurrent)
                · have hzero := hi₀.2.2 i hi
                  have hout := scalarStep_other_site P j T s₀ site i
                    (tileIncrement P j (Query.trueDigit qi k) a) hie hzero.1 hzero.2
                  have hstep : tileStep P j T s₀ (Query.trueDigit qi k) a =
                      scalarStep P j T s₀ site (tileIncrement P j (Query.trueDigit qi k) a) := by
                    simp [tileStep, hs₀]
                  rw [hstep]
                  exact hout
        | auxiliary k =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ (Query.auxiliary k) a
                  (Or.inr (Or.inr hs₀))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.2 i hi
            | some ii =>
                have hs₀ : s₀.2.site = some ii := by simp [s₀, logQuery, hs]
                have hq' : tileQuery P j T s = Query.auxiliary k := by simpa using hq
                have hnotTerm := tileQuery_site_not_terminal P j T s ii _ hs hq'
                  (by intro h; cases h)
                have hcurrent : i ∈ s.1.terminal := hfresh.2.1 hi
                by_cases hie : i = ii
                · subst i
                  exact False.elim (hnotTerm hcurrent)
                · have hzero := hi₀.2.2 i hi
                  have hout := scalarStep_other_site P j T s₀ ii i
                    (tileIncrement P j (Query.auxiliary k) a) hie hzero.1 hzero.2
                  have hstep : tileStep P j T s₀ (Query.auxiliary k) a =
                      scalarStep P j T s₀ ii (tileIncrement P j (Query.auxiliary k) a) := by
                    simp [tileStep, hs₀]
                  rw [hstep]
                  exact hout
        | trueSuffix qi k =>
            cases hs : s.2.site with
            | none =>
                have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
                have hkeep := tileStep_keepScratch P j T s₀ (Query.trueSuffix qi k) a
                  (Or.inr (Or.inr hs₀))
                rw [hkeep.1, hkeep.2]
                exact hi₀.2.2 i hi
            | some site =>
                have hs₀ : s₀.2.site = some site := by simp [s₀, logQuery, hs]
                have hq' : tileQuery P j T s = Query.trueSuffix qi k := by simpa using hq
                have hnotTerm := tileQuery_site_not_terminal P j T s site _ hs hq'
                  (by intro h; cases h)
                have hcurrent : i ∈ s.1.terminal := hfresh.2.1 hi
                by_cases hie : i = site
                · subst i
                  exact False.elim (hnotTerm hcurrent)
                · have hzero := hi₀.2.2 i hi
                  have hout := scalarStep_other_site P j T s₀ site i
                    (tileIncrement P j (Query.trueSuffix qi k) a) hie hzero.1 hzero.2
                  have hstep : tileStep P j T s₀ (Query.trueSuffix qi k) a =
                      scalarStep P j T s₀ site (tileIncrement P j (Query.trueSuffix qi k) a) := by
                    simp [tileStep, hs₀]
                  rw [hstep]
                  exact hout

private def tileTrueStepValue (P : TilePlan d m) (j : ℕ) (M : ℕ → ℕ)
    (x : RunRecord d m) (ω : RandomSources (Torus d m) M) (i : Torus d m) : ℝ :=
  if IsFinalSweep m j then
    binarySuffix (OAI.Anderson.scaleCoupling P.n₀ P.u) (x.prefixLength i) (trueDigits ω i)
  else
    digitAmp P.u (j - 1) * signValue (trueDigits ω i (x.prefixLength i))

private def TileTrueScratchInv (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m)
    (M : ℕ → ℕ)
    (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m) : Prop :=
  ∀ i, i ∈ tileSites (P.cover j) T → i ∈ x.endpoint.active → i ∉ x.pending →
    i ∉ x.terminal →
      (s.2.consumed i = false → s.2.added i = 0) ∧
      (s.2.consumed i = true → s.2.added i = tileTrueStepValue P j M x ω i) ∧
      (s.2.consumed i = true →
        ((i, false) : Port d m) ∉ (s.2.seq.state s.2.seq.length).live)

private theorem tileQuery_true_site (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (hsite : s.2.site = some i)
    (hactive : activeIn P j T s.1 i) (huse : usesTrue s i) :
    (¬ IsFinalSweep m j →
      tileQuery P j T s = Query.trueDigit i (s.1.prefixLength i)) ∧
    (IsFinalSweep m j →
      tileQuery P j T s = Query.trueSuffix i (s.1.prefixLength i)) := by
  constructor <;> intro hfinal <;> simp [tileQuery, hsite, hactive, huse, hfinal]

private theorem tileTrueScratchInv_scalar_success (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (M : ℕ → ℕ)
    (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m)
    (i : Torus d m) (ζ : ℝ)
    (hInv : TileTrueScratchInv P j T x M ω s)
    (hPath : TilePathScratch P j T x s)
    (hsite : s.2.site = some i)
    (hrec : s.1 = x) (ha0 : s.2.attempt = 0)
    (hiT : i ∈ tileSites (P.cover j) T) (hiA : i ∈ x.endpoint.active)
    (hiP : i ∉ x.pending) (hiTerm : i ∉ x.terminal)
    (huse : usesTrue s i) (hζ : ζ = tileTrueStepValue P j M x ω i)
    (hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (i, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (i, false) (ζ / Real.sqrt (sweepW P.u m j)))) :
    TileTrueScratchInv P j T x M ω (scalarStep P j T s i ζ) := by
  intro t htT htA htP htTerm
  have hprev := hInv t htT htA htP htTerm
  by_cases hti : t = i
  · subst t
    have hiInv := hInv i hiT hiA hiP hiTerm
    have hiLive := (hPath.1 i hsite).2.2
    have hconsFalse : s.2.consumed i = false := by
      cases hc : s.2.consumed i with
      | false => rfl
      | true => exact False.elim (hiInv.2.2 hc hiLive)
    have haddZero : s.2.added i = 0 := hiInv.1 hconsFalse
    have hconsOut : (scalarStep P j T s i ζ).2.consumed i = true := by
      unfold scalarStep
      rw [if_pos hok]
      simp [huse]
    have haddOut : (scalarStep P j T s i ζ).2.added i = tileTrueStepValue P j M x ω i := by
      unfold scalarStep
      rw [if_pos hok]
      simp [haddZero, hζ]
    refine ⟨?_, ?_, ?_⟩
    · intro hfalse
      rw [hconsOut] at hfalse
      cases hfalse
    · intro _
      exact haddOut
    · intro _
      rw [scalarStep_success_live P j T s i ζ hok]
      change ((i, false) : Port d m) ∉
        (s.2.seq.state s.2.seq.length).live.erase ((i, false) : Port d m)
      intro hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
  · have hout := scalarStep_other_success P j T s i t ζ hti hok
    refine ⟨?_, ?_, ?_⟩
    · intro hc
      rw [hout.1] at hc
      rw [hout.2]
      exact hprev.1 hc
    · intro hc
      rw [hout.1] at hc
      rw [hout.2]
      exact hprev.2.1 hc
    · intro hc
      have htcons : s.2.consumed t = true := by rw [hout.1] at hc; exact hc
      intro hmem
      have hmem' : (t, false) ∈
          (s.2.seq.state s.2.seq.length).live.erase (i, false) := by
        rw [scalarStep_success_live P j T s i ζ hok] at hmem
        exact hmem
      exact hprev.2.2 htcons (Finset.mem_of_mem_erase hmem')

private theorem tileTrueScratchInv_other_success (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (M : ℕ → ℕ)
    (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m)
    (site : Torus d m) (ζ : ℝ)
    (hInv : TileTrueScratchInv P j T x M ω s)
    (hexcl : ∀ t, t ∈ tileSites (P.cover j) T → t ∈ x.endpoint.active →
      t ∉ x.pending → t ∉ x.terminal → t ≠ site)
    (hok : trialOk P j T s.1
      (extendSeq s.2.seq
        (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
          (s.2.seq.state s.2.seq.length) (site, false) (ζ / Real.sqrt (sweepW P.u m j)))
        (site, false) (ζ / Real.sqrt (sweepW P.u m j)))
      (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) s.1.r)
        (s.2.seq.state s.2.seq.length) (site, false) (ζ / Real.sqrt (sweepW P.u m j)))) :
    TileTrueScratchInv P j T x M ω (scalarStep P j T s site ζ) := by
  intro t htT htA htP htTerm
  have hprev := hInv t htT htA htP htTerm
  have hout := scalarStep_other_success P j T s site t ζ
    (hexcl t htT htA htP htTerm) hok
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    rw [hout.1] at hc
    rw [hout.2]
    exact hprev.1 hc
  · intro hc
    rw [hout.1] at hc
    rw [hout.2]
    exact hprev.2.1 hc
  · intro hc
    have htcons : s.2.consumed t = true := by rw [hout.1] at hc; exact hc
    intro hmem
    have hmem' : (t, false) ∈
        (s.2.seq.state s.2.seq.length).live.erase (site, false) := by
      rw [scalarStep_success_live P j T s site ζ hok] at hmem
      exact hmem
    exact hprev.2.2 htcons (Finset.mem_of_mem_erase hmem')

private theorem tileTrueScratchInv_of_keep (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (x : RunRecord d m) (M : ℕ → ℕ)
    (ω : RandomSources (Torus d m) M) (s : RunRecord d m × TileScratch d m)
    (q : Query (Torus d m)) (a : Answer (Torus d m))
    (hInv : TileTrueScratchInv P j T x M ω s)
    (hkeep : (tileStep P j T s q a).2.added = s.2.added ∧
      (tileStep P j T s q a).2.consumed = s.2.consumed ∧
      (tileStep P j T s q a).2.seq = s.2.seq) :
    TileTrueScratchInv P j T x M ω (tileStep P j T s q a) := by
  simpa only [TileTrueScratchInv, hkeep.1, hkeep.2.1, hkeep.2.2] using hInv

private theorem couplingOf_eq_scaleCoupling (u : ℝ) (n₀ : ℕ) :
    couplingOf u n₀ = OAI.Anderson.scaleCoupling n₀ u := by
  have hpow : (4 : ℝ) ^ n₀ = ((2 : ℝ) ^ n₀) ^ 2 := by
    calc
      (4 : ℝ) ^ n₀ = ((2 : ℝ) ^ 2) ^ n₀ := by congr 1; norm_num
      _ = (2 : ℝ) ^ (2 * n₀) := by rw [pow_mul]
      _ = ((2 : ℝ) ^ n₀) ^ 2 := by rw [Nat.mul_comm 2 n₀, ← pow_mul]
  unfold couplingOf OAI.Anderson.scaleCoupling
  rw [hpow, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (by positivity)]

private theorem tileTrueScratchInv_update_noFail (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (ω : RandomSources (Torus d m) M) (x : RunRecord d m)
    (L : List (Query (Torus d m))) (s : RunRecord d m × TileScratch d m)
    (a : Answer (Torus d m)) (hrun : s.2.halted = false)
    (ha0 : s.2.attempt = 0) (hrec : s.1 = x)
    (hInv : TileTrueScratchInv P j T x M ω s)
    (hPath : TilePathScratch P j T x s)
    (hans : a = localAnswer (Torus d m) M L (tileQuery P j T s) ω)
    (hff : ((tileBlock P j T).update s a).2.firstFail = false) :
    TileTrueScratchInv P j T x M ω ((tileBlock P j T).update s a) := by
  have hu := tileBlock_update_running P j T s a hrun
  let s₀ := (s.1, logQuery (tileQuery P j T s) s.2)
  have hInv₀ : TileTrueScratchInv P j T x M ω s₀ := by
    simpa [TileTrueScratchInv, s₀, logQuery] using hInv
  have hPath₀ : TilePathScratch P j T x s₀ := by
    simpa [TilePathScratch, TileExposure, s₀, logQuery] using hPath
  have hffStep : (tileStep P j T s₀ (tileQuery P j T s) a).2.firstFail = false := by
    rw [← hu]
    exact hff
  rw [hu]
  cases hs : s.2.site with
  | none =>
      have hs₀ : s₀.2.site = none := by simp [s₀, logQuery, hs]
      cases hq : tileQuery P j T s with
      | nextOrder o =>
          have hk := tileStep_keepScratchSeq P j T s₀ (Query.nextOrder o) a
            (Or.inl ⟨o, rfl⟩)
          simpa [s₀, hq] using tileTrueScratchInv_of_keep P j T x M ω s₀
            (Query.nextOrder o) a hInv₀ hk
      | decision =>
          have hk := tileStep_keepScratchSeq P j T s₀ Query.decision a
            (Or.inr (Or.inl rfl))
          simpa [s₀, hq] using tileTrueScratchInv_of_keep P j T x M ω s₀
            Query.decision a hInv₀ hk
      | trueDigit i h =>
          have hk := tileStep_keepScratchSeq P j T s₀ (Query.trueDigit i h) a
            (Or.inr (Or.inr hs₀))
          simpa [s₀, hq] using tileTrueScratchInv_of_keep P j T x M ω s₀
            (Query.trueDigit i h) a hInv₀ hk
      | auxiliary k =>
          have hk := tileStep_keepScratchSeq P j T s₀ (Query.auxiliary k) a
            (Or.inr (Or.inr hs₀))
          simpa [s₀, hq] using tileTrueScratchInv_of_keep P j T x M ω s₀
            (Query.auxiliary k) a hInv₀ hk
      | trueSuffix i h =>
          have hk := tileStep_keepScratchSeq P j T s₀ (Query.trueSuffix i h) a
            (Or.inr (Or.inr hs₀))
          simpa [s₀, hq] using tileTrueScratchInv_of_keep P j T x M ω s₀
            (Query.trueSuffix i h) a hInv₀ hk
  | some site =>
      have hs₀ : s₀.2.site = some site := by simp [s₀, logQuery, hs]
      cases hq : tileQuery P j T s with
      | nextOrder o =>
          exact (tileQuery_site_not_nextOrder P j T s site o hs hq).elim
      | decision =>
          have hk := tileStep_keepScratchSeq P j T s₀ Query.decision a
            (Or.inr (Or.inl rfl))
          simpa [s₀, hq] using tileTrueScratchInv_of_keep P j T x M ω s₀
            Query.decision a hInv₀ hk
      | trueDigit qi h =>
          have hqi : qi = site := by
            have hh := hq
            simp only [tileQuery, hs] at hh
            split_ifs at hh <;> cases hh <;> rfl
          subst site
          have hactive := tileQuery_site_active P j T s qi _ hs hq
            (by intro he; cases he)
          have huse : usesTrue s qi := by
            by_contra hnot
            have hh := hq
            simp only [tileQuery, hs, if_pos hactive, if_neg hnot] at hh
            split_ifs at hh <;> cases hh
          by_cases hfinal : IsFinalSweep m j
          · have hshape := (tileQuery_true_site P j T s qi hs hactive huse).2 hfinal
            have hneq : Query.trueDigit qi h = Query.trueSuffix qi (s.1.prefixLength qi) :=
              hq.symm.trans hshape
            cases hneq
          · have hshape := (tileQuery_true_site P j T s qi hs hactive huse).1 hfinal
            have hLen : h = s.1.prefixLength qi := by
              injection (hq.symm.trans hshape) with hqi hh
            subst h
            let ζ := tileIncrement P j (Query.trueDigit qi (s.1.prefixLength qi)) a
            have hζ : ζ = tileTrueStepValue P j M x ω qi := by
              dsimp [ζ]
              rw [hans, hq, tileAnswer_trueDigit]
              simp [tileTrueStepValue, hfinal, hrec]
            have hstep : tileStep P j T s₀ (Query.trueDigit qi (s.1.prefixLength qi)) a =
                scalarStep P j T s₀ qi ζ := by simp [tileStep, hs₀, ζ]
            have hffQ : (tileStep P j T s₀ (Query.trueDigit qi (s.1.prefixLength qi)) a).2.firstFail = false := by
              simpa [hq] using hffStep
            have hffScalar : (scalarStep P j T s₀ qi ζ).2.firstFail = false := by
              rw [← hstep]
              exact hffQ
            have hOk := scalarStep_trialOk_of_noFail P j T s₀ qi ζ hffScalar
            have hrec₀ : s₀.1 = x := by simpa [s₀] using hrec
            have ha00 : s₀.2.attempt = 0 := by simpa [s₀, logQuery] using ha0
            have huse₀ : usesTrue s₀ qi := by simpa [usesTrue, s₀, logQuery] using huse
            have hsite₀ : s₀.2.site = some qi := by simpa [s₀, logQuery] using hs
            have hInvScalar := tileTrueScratchInv_scalar_success P j T x M ω s₀ qi ζ
              hInv₀ hPath₀ hsite₀ hrec₀ ha00 hactive.1
              (by simpa [hrec] using hactive.2.1)
              (by simpa [hrec₀] using huse₀.2)
              (by simpa [hrec] using hactive.2.2)
              huse₀ hζ hOk
            have hInvScalar' : TileTrueScratchInv P j T x M ω
                (scalarStep P j T (s.1, logQuery
                  (Query.trueDigit qi (s.1.prefixLength qi)) s.2) qi ζ) := by
              simpa [s₀, hq] using hInvScalar
            have hstep' : tileStep P j T (s.1, logQuery
                (Query.trueDigit qi (s.1.prefixLength qi)) s.2)
                (Query.trueDigit qi (s.1.prefixLength qi)) a =
                scalarStep P j T (s.1, logQuery
                  (Query.trueDigit qi (s.1.prefixLength qi)) s.2) qi ζ := by
              simp [tileStep, logQuery, hs, ζ]
            rw [hstep']
            exact hInvScalar'
      | trueSuffix qi h =>
          have hqi : qi = site := by
            have hh := hq
            simp only [tileQuery, hs] at hh
            split_ifs at hh <;> cases hh <;> rfl
          subst site
          have hactive := tileQuery_site_active P j T s qi _ hs hq
            (by intro he; cases he)
          have huse : usesTrue s qi := by
            by_contra hnot
            have hh := hq
            simp only [tileQuery, hs, if_pos hactive, if_neg hnot] at hh
            split_ifs at hh <;> cases hh
          by_cases hfinal : IsFinalSweep m j
          · have hshape := (tileQuery_true_site P j T s qi hs hactive huse).2 hfinal
            have hLen : h = s.1.prefixLength qi := by
              injection (hq.symm.trans hshape) with hqi hh
            subst h
            let ζ := tileIncrement P j (Query.trueSuffix qi (s.1.prefixLength qi)) a
            have hζ : ζ = tileTrueStepValue P j M x ω qi := by
              dsimp [ζ]
              rw [hans, hq, tileAnswer_trueSuffix, couplingOf_eq_scaleCoupling]
              simp [tileTrueStepValue, hfinal, hrec]
            have hstep : tileStep P j T s₀ (Query.trueSuffix qi (s.1.prefixLength qi)) a =
                scalarStep P j T s₀ qi ζ := by simp [tileStep, hs₀, ζ]
            have hffQ : (tileStep P j T s₀ (Query.trueSuffix qi (s.1.prefixLength qi)) a).2.firstFail = false := by
              simpa [hq] using hffStep
            have hffScalar : (scalarStep P j T s₀ qi ζ).2.firstFail = false := by
              rw [← hstep]
              exact hffQ
            have hOk := scalarStep_trialOk_of_noFail P j T s₀ qi ζ hffScalar
            have hrec₀ : s₀.1 = x := by simpa [s₀] using hrec
            have ha00 : s₀.2.attempt = 0 := by simpa [s₀, logQuery] using ha0
            have huse₀ : usesTrue s₀ qi := by simpa [usesTrue, s₀, logQuery] using huse
            have hsite₀ : s₀.2.site = some qi := by simpa [s₀, logQuery] using hs
            have hInvScalar := tileTrueScratchInv_scalar_success P j T x M ω s₀ qi ζ
              hInv₀ hPath₀ hsite₀ hrec₀ ha00 hactive.1
              (by simpa [hrec] using hactive.2.1)
              (by simpa [hrec₀] using huse₀.2)
              (by simpa [hrec] using hactive.2.2)
              huse₀ hζ hOk
            have hInvScalar' : TileTrueScratchInv P j T x M ω
                (scalarStep P j T (s.1, logQuery
                  (Query.trueSuffix qi (s.1.prefixLength qi)) s.2) qi ζ) := by
              simpa [s₀, hq] using hInvScalar
            have hstep' : tileStep P j T (s.1, logQuery
                (Query.trueSuffix qi (s.1.prefixLength qi)) s.2)
                (Query.trueSuffix qi (s.1.prefixLength qi)) a =
                scalarStep P j T (s.1, logQuery
                  (Query.trueSuffix qi (s.1.prefixLength qi)) s.2) qi ζ := by
              simp [tileStep, logQuery, hs, ζ]
            rw [hstep']
            exact hInvScalar'
          · have hshape := (tileQuery_true_site P j T s qi hs hactive huse).1 hfinal
            have heq : Query.trueSuffix qi h = Query.trueDigit qi (s.1.prefixLength qi) :=
              hq.symm.trans hshape
            cases heq
      | auxiliary idx =>
          have hactive := tileQuery_site_active P j T s site _ hs hq
            (by intro he; cases he)
          have huseFalse : ¬ usesTrue s site := by
            intro hu
            have hshape := tileQuery_true_site P j T s site hs hactive hu
            by_cases hfinal : IsFinalSweep m j
            · have he := hshape.2 hfinal
              rw [hq] at he
              cases he
            · have he := hshape.1 hfinal
              rw [hq] at he
              cases he
          have hpending : site ∈ x.pending := by
            by_contra hp
            apply huseFalse
            exact ⟨ha0, by simpa [hrec] using hp⟩
          let ζ := tileIncrement P j (Query.auxiliary idx) a
          have hstep : tileStep P j T s₀ (Query.auxiliary idx) a =
              scalarStep P j T s₀ site ζ := by simp [tileStep, hs₀, ζ]
          have hffQ : (tileStep P j T s₀ (Query.auxiliary idx) a).2.firstFail = false := by
            simpa [hq] using hffStep
          have hffScalar : (scalarStep P j T s₀ site ζ).2.firstFail = false := by
            rw [← hstep]
            exact hffQ
          have hOk := scalarStep_trialOk_of_noFail P j T s₀ site ζ hffScalar
          have hexcl : ∀ t, t ∈ tileSites (P.cover j) T → t ∈ x.endpoint.active →
              t ∉ x.pending → t ∉ x.terminal → t ≠ site := by
            intro t htT htA htP htTerm heq
            subst t
            exact (htP hpending).elim
          have hout := tileTrueScratchInv_other_success P j T x M ω s₀ site ζ
            hInv₀ hexcl hOk
          have hout' : TileTrueScratchInv P j T x M ω
              (scalarStep P j T (s.1, logQuery (Query.auxiliary idx) s.2) site ζ) := by
            simpa [s₀, hq] using hout
          have hstep' : tileStep P j T (s.1, logQuery (Query.auxiliary idx) s.2)
              (Query.auxiliary idx) a =
              scalarStep P j T (s.1, logQuery (Query.auxiliary idx) s.2) site ζ := by
            simp [tileStep, logQuery, hs, ζ]
          rw [hstep']
          exact hout'
private theorem tileTrueScratchInv_of_noFail (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (ω : RandomSources (Torus d m) M) (x : RunRecord d m) (k : ℕ)
    (hab : x.aborted = false)
    (hk : ∀ k' < k, (tileBlock P j T).halted
      (localState M (tileBlock P j T) x k' ω) = false)
    (hff : (localState M (tileBlock P j T) x k ω).2.firstFail = false) :
    TileTrueScratchInv P j T x M ω (localState M (tileBlock P j T) x k ω) := by
  have hallFF := tileAllFalse_of_exitFalse P j T M x k ω hff
  have hFirst : ∀ n, FirstTrialInv x (localState M (tileBlock P j T) x n ω) :=
    fun n => localState_induct M (tileBlock P j T) x (FirstTrialInv x)
      (firstTrialInv_enter P j T x)
      (fun s a hs => firstTrialInv_update P j T x s a hs) n ω
  have hInv : ∀ n, n ≤ k →
      (localState M (tileBlock P j T) x n ω).2.firstFail = false →
      TileTrueScratchInv P j T x M ω (localState M (tileBlock P j T) x n ω) := by
    intro n
    induction n with
    | zero =>
        intro _ _
        simp [TileTrueScratchInv, localState_zero, tileBlock, hab, initScratch,
          tileTrueStepValue]
    | succ n ih =>
        intro hn hffNext
        have hnlt : n < k := by omega
        have hffPrev := hallFF n (by omega)
        have hrun := hk n hnlt
        let s := localState M (tileBlock P j T) x n ω
        have hrunS : (tileBlock P j T).halted s = false := by simpa [s] using hrun
        have ha0 : s.2.attempt = 0 := by
          by_contra hne
          have htrue := (hFirst n).1 hne
          simp [hffPrev] at htrue
        have hrec : s.1 = x := (hFirst n).2 ha0 (by simpa [tileBlock_halted] using hrunS)
        have hPrevInv : TileTrueScratchInv P j T x M ω s := by
          simpa [s] using ih (by omega) hffPrev
        have hreach : BlockReach (tileBlock P j T) x s := by
          simpa [s] using localState_reach M (tileBlock P j T) x ω n
            (fun l hl => hk l (by omega))
        have hPath : TilePathScratch P j T x s := tilePathScratch_of_reach P j T x s hreach
        let L := (machineRun (Torus d m) M ((tileBlock P j T).enter x)
          (tileBlock P j T).next (tileBlock P j T).update n ω).2
        let a := localAnswer (Torus d m) M L ((tileBlock P j T).next s) ω
        have hsu : localState M (tileBlock P j T) x (n + 1) ω =
            (tileBlock P j T).update s a := by
          rw [localState_succ]
        have hnext : (tileBlock P j T).next s = tileQuery P j T s := by
          simpa [s] using tileBlock_next_running P j T s hrunS
        have hans : a = localAnswer (Torus d m) M L (tileQuery P j T s) ω := by
          simp [a, hnext]
        have hffUpdate : ((tileBlock P j T).update s a).2.firstFail = false := by
          rw [← hsu]
          exact hffNext
        have hstep := tileTrueScratchInv_update_noFail P j T M ω x L s a hrunS ha0
          hrec hPrevInv hPath hans hffUpdate
        rw [hsu]
        exact hstep
  exact hInv k le_rfl hff

private theorem binaryValue_scale (c : ℝ) (a : ℕ → Bool) :
    c * binaryValue 1 a = binaryValue c a := by
  unfold binaryValue
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

/-! ## Assembly -/

/-- A scalar slot halts only by aborting. -/
private theorem scalarStep_halt_abort (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (s : RunRecord d m × TileScratch d m) (i : Torus d m)
    (ζ : ℝ) (hrun : s.2.halted = false)
    (hh : (scalarStep P j T s i ζ).2.halted = true) :
    (scalarStep P j T s i ζ).1.aborted = true := by
  classical
  unfold scalarStep at hh ⊢
  dsimp only at hh ⊢
  split_ifs at hh ⊢ with hok
  · simp [hrun] at hh
  · unfold failTrial at hh ⊢
    dsimp only at hh ⊢
    by_cases hlate : m / 2 < j
    · simp [hlate]
    · simp [hlate, trialScratch, hrun] at hh

/-- **The halting step of a running tile block** is the commit (or an abort). -/
private theorem tile_halt_commit (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (s : RunRecord d m × TileScratch d m) (hrun : s.2.halted = false) (a : Answer (Torus d m))
    (hh : ((tileBlock P j T).update s a).2.halted = true)
    (hab : ((tileBlock P j T).update s a).1.aborted = false) :
    ((tileBlock P j T).update s a).1 =
      commitTrial s.1 (logQuery (tileQuery P j T s) s.2) (decide (IsFinalSweep m j)) := by
  classical
  rw [tileBlock_update_running P j T s a hrun] at hh hab ⊢
  generalize tileQuery P j T s = q at hh hab ⊢
  have hrun0 : (logQuery q s.2).halted = false := hrun
  have hscal : ∀ ζ : ℝ,
      (match (logQuery q s.2).site with
        | none => (s.1, logQuery q s.2)
        | some i => scalarStep P j T (s.1, logQuery q s.2) i ζ).2.halted = true →
      (match (logQuery q s.2).site with
        | none => (s.1, logQuery q s.2)
        | some i => scalarStep P j T (s.1, logQuery q s.2) i ζ).1.aborted = true := by
    intro ζ
    rcases hsite : (logQuery q s.2).site with _ | i
    · intro h; simp [hrun0] at h
    · intro h; exact scalarStep_halt_abort P j T _ i ζ hrun0 h
  rcases q with ⟨i, h⟩ | k | ⟨i, h⟩ | o | _
  · have h1 := hscal (tileIncrement P j (Query.trueDigit i h) a) hh
    have h2 : (tileStep P j T (s.1, logQuery (Query.trueDigit i h) s.2) (Query.trueDigit i h) a).1.aborted = true := h1
    rw [hab] at h2; cases h2
  · have h1 := hscal (tileIncrement P j (Query.auxiliary k) a) hh
    have h2 : (tileStep P j T (s.1, logQuery (Query.auxiliary k) s.2) (Query.auxiliary k) a).1.aborted = true := h1
    rw [hab] at h2; cases h2
  · have h1 := hscal (tileIncrement P j (Query.trueSuffix i h) a) hh
    have h2 : (tileStep P j T (s.1, logQuery (Query.trueSuffix i h) s.2) (Query.trueSuffix i h) a).1.aborted = true := h1
    rw [hab] at h2; cases h2
  · simp [tileStep, hrun0] at hh
  · simp only [tileStep] at hh hab ⊢
    rcases hsite : (logQuery Query.decision s.2).site with _ | i
    · rfl
    · rw [hsite] at hh; simp [hrun0] at hh

/-- **Tile true-values discipline** (contract `TileTrueValuesStatement`). -/
theorem tileTrueValues_proof : TileTrueValuesStatement := by
  classical
  intro d m P j T M ω x k hj1 hj2 hpre hx hrun hh
  cases k with
  | zero =>
    have hab : x.aborted = true := by
      by_contra hne
      have hf : x.aborted = false := by simpa using hne
      simp [localState_zero, tileBlock, hf, initScratch] at hh
    have : (tileBlock P j T).exit (localState M (tileBlock P j T) x 0 ω) = x := by
      simp [localState_zero, tileBlock, hab]
    rw [this]; intro h; rw [hab] at h; cases h
  | succ k =>
    have hreachS := localState_reach M (tileBlock P j T) x ω (k + 1) hrun
    by_cases hxa : x.aborted = true
    · have h1 := tile_reach_aborted P j T x hxa _ hreachS
      show (localState M (tileBlock P j T) x (k + 1) ω).1 ∈ _
      rw [h1]; intro h; rw [hxa] at h; cases h
    have hxab : x.aborted = false := by simpa using hxa
    set s := localState M (tileBlock P j T) x k ω with hsdef
    have hk' : ∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) =
        false := fun k' hk' => hrun k' (by omega)
    have hreach : BlockReach (tileBlock P j T) x s := localState_reach M _ x ω k hk'
    have hsrun : s.2.halted = false := hrun k (by omega)
    have hR : TRun P j T x s := (tile_reach P j T x hxab s hreach).1 hsrun
    have hpath := tilePathScratch_of_reach P j T x s hreach
    obtain ⟨htv, hcv⟩ := hx hxab
    show (localState M (tileBlock P j T) x (k + 1) ω).1 ∈ _
    rw [localState_succ]
    set a := localAnswer (Torus d m) M (machineRun (Torus d m) M ((tileBlock P j T).enter x)
      (tileBlock P j T).next (tileBlock P j T).update k ω).2
      ((tileBlock P j T).next (localState M (tileBlock P j T) x k ω)) ω with ha
    intro hzab
    have hhz : ((tileBlock P j T).update s a).2.halted = true := by
      have := hh; rw [localState_succ] at this; exact this
    rw [tile_halt_commit P j T s hsrun a hhz hzab]
    rw [tile_halt_commit P j T s hsrun a hhz hzab] at hzab
    set sc := logQuery (tileQuery P j T s) s.2 with hsc
    have hcons : sc.consumed = s.2.consumed := rfl
    have hadd : sc.added = s.2.added := rfl
    have hinst : s.1.installed = x.installed := hR.inst
    have hpref : s.1.prefixLength = x.prefixLength := hR.pref
    have hterm : s.1.terminal = x.terminal := hR.term
    by_cases hat : s.2.attempt = 0
    · -- accepted first trial
      have hff : s.2.firstFail = false := hR.ff0 hat
      have hinv := tileTrueScratchInv_of_noFail P j T M ω x k hxab hk' hff
      rw [← hsdef] at hinv
      have hpend : s.1.pending = x.pending := hR.pend0 hat
      refine ⟨fun i hi => ?_, fun i hp ht => ?_⟩
      · -- terminal sites
        simp only [commitTrial, hcons, hadd, hinst] at hi ⊢
        by_cases hxt : i ∈ x.terminal
        · rw [(hpath.2.2 i hxt).2, add_zero]; exact htv i hxt
        · have hfin : IsFinalSweep m j ∧ s.2.consumed i = true := by
            rw [hterm] at hi
            by_cases hf : IsFinalSweep m j
            · simp only [hf, decide_true, if_true, Finset.mem_union, Finset.mem_filter,
                Finset.mem_univ, true_and] at hi
              exact ⟨hf, hi.resolve_left hxt⟩
            · simp only [hf, decide_false, if_false] at hi; exact absurd hi hxt
          have hTA : i ∈ tileSites (P.cover j) T ∧ i ∈ x.endpoint.active := by
            by_contra hn; rw [(hpath.2.1 i hn).1] at hfin; cases hfin.2
          have hnp : i ∉ x.pending := by
            have := (hR.cons0 hat i).mp hfin.2; exact this.2.2
          rw [(hinv i hTA.1 hTA.2 hnp hxt).2.1 hfin.2]
          unfold tileTrueStepValue
          rw [if_pos hfin.1, hcv i hnp hxt, ← AndersonAC.S2.binary_prefix_suffix,
            ← binaryValue_scale]
          rfl
      · -- coupled sites
        simp only [commitTrial, hcons, hadd, hinst, hpref] at hp ht ⊢
        rw [hpend] at hp
        have hxt : i ∉ x.terminal := by
          intro h'; apply ht; rw [hterm]; split_ifs <;> simp [h']
        by_cases hc : s.2.consumed i = true
        · have hnf : ¬ IsFinalSweep m j := by
            intro hf; apply ht; rw [hterm]
            simp [hf, hc]
          have hTA : i ∈ tileSites (P.cover j) T ∧ i ∈ x.endpoint.active := by
            by_contra hn; rw [(hpath.2.1 i hn).1] at hc; cases hc
          rw [(hinv i hTA.1 hTA.2 hp hxt).2.1 hc]
          unfold tileTrueStepValue
          rw [if_neg hnf, hcv i hp hxt]
          have hpl := hpre hnf i hTA.1 hTA.2 hp hxt
          simp only [hc, hnf, decide_false, Bool.not_false, Bool.and_true, if_true]
          rw [show x.prefixLength i + (if decide True = true then 1 else 0) =
            x.prefixLength i + 1 from rfl]
          rw [binaryPrefix_succ, hpl, digitAmp_eq_scaleCoupling P.n₀ j P.u hj1,
            show j - 1 - P.n₀ + 1 = j - P.n₀ by omega]
        · have hc' : s.2.consumed i = false := by simpa using hc
          have hadd0 : s.2.added i = 0 := by
            by_cases hTA : i ∈ tileSites (P.cover j) T ∧ i ∈ x.endpoint.active
            · exact (hinv i hTA.1 hTA.2 hp hxt).1 hc'
            · exact (hpath.2.1 i hTA).2
          rw [hadd0, add_zero, hc']
          simp only [Bool.false_and, Bool.false_eq_true, if_false, add_zero]
          exact hcv i hp hxt
    · -- retries: the tile's active sites are pending, nothing consumed
      obtain ⟨hpend, -⟩ := hR.pend1 hat
      have hc0 : ∀ i, s.2.consumed i = false := hR.cons1 hat
      refine ⟨fun i hi => ?_, fun i hp ht => ?_⟩
      · simp only [commitTrial, hcons, hadd, hinst, hc0] at hi ⊢
        have hxt : i ∈ x.terminal := by
          rw [hterm] at hi; split_ifs at hi
          · simpa using hi
          · exact hi
        rw [(hpath.2.2 i hxt).2, add_zero]; exact htv i hxt
      · simp only [commitTrial, hcons, hadd, hinst, hpref, hc0] at hp ht ⊢
        rw [hpend] at hp
        have hxt : i ∉ x.terminal := by
          intro h'; apply ht; rw [hterm]; split_ifs <;> simp [h']
        have hxp : i ∉ x.pending := fun h' => hp (Finset.mem_union_left _ h')
        have hTA : ¬ (i ∈ tileSites (P.cover j) T ∧ i ∈ x.endpoint.active) := fun h' =>
          hp (Finset.mem_union_right _ (Finset.mem_inter.mpr h'))
        rw [(hpath.2.1 i hTA).2, add_zero]
        simp only [Bool.false_and, Bool.false_eq_true, if_false, add_zero]
        exact hcv i hxp hxt

example : TileTrueValuesStatement := tileTrueValues_proof

end AndersonAC.AgentS78
