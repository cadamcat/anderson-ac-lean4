import AndersonAC.AgentS78.Construction.StagePhaseTrace

/-!
# The DONE step facts from their analytic part

agent-s78phase2. `clearingDone_of_analytic : ClearingDoneAnalyticStatement d →
ClearingDoneStatement d` (d ≥ 3). The structural fields of `ClearingStepFacts` are proved here:

* `physical`, `nested`, `removedNonempty`: the block invariant `ClrInv` (StagePhaseClr.lean);
* `fresh`: the committed anchors of the stage are anchors of index-`j` groups of the trace, whose
  cores are farther than `R_j` from every component with an active site (`ClearingTraceOf.fresh`),
  and the attempted core contains its anchor `y` and is active;
* `removedSize`, `removedLocal`: removed sites are core sites (within `t^{-ν} R_j` of `y`) or
  guarded inspected sites (within `ℓ_j/2` of the core, at most `heatLimit` of them);
* `metric`, `activeCount`, `haloOverlap`: Lemma 7.2 (`SolS78.uniform_clearing_geometry_proof`)
  for the trace extended by the committed group (`AgentS78Geo.extendTrace`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf extendTrace physicalDistance_symm)
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

theorem cube_mono_radius (z : Torus d m) {R R' : ℝ} (h : R ≤ R') :
    cube d m z R ⊆ cube d m z R' := by
  intro w hw
  simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact fun i => (hw i).trans h

theorem overlap_le_card {ι κ β : Type} [Fintype κ] (Q : κ → Finset ι) (x : ι) (S : Finset β)
    (f : κ → β) (hmaps : ∀ a, x ∈ Q a → f a ∈ S)
    (hinj : ∀ a a', x ∈ Q a → x ∈ Q a' → f a = f a' → a = a') : overlap Q x ≤ S.card := by
  unfold overlap
  apply Finset.card_le_card_of_injOn f
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and] at ha
    exact hmaps a ha
  · intro a ha a' ha' h
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and] at ha ha'
    exact hinj a a' ha ha' h

/-- **The DONE step facts from their analytic part.** -/
theorem clearingDone_of_analytic (hd : 3 ≤ d) (hhops : ClearingDoneHopsStatement d)
    (hA : ClearingDoneAnalyticStatement d) :
    ClearingDoneStatement d := by
  intro cP CP hcP hCP Ctr hCtr
  obtain ⟨CA₀, cA₀, PA₀, hCA₀, hcA₀, hPA₀, hmainA⟩ := hA cP CP hcP hCP Ctr hCtr
  obtain ⟨Nu, C', hC', hunif⟩ :=
    AndersonAC.SolS78.uniform_clearing_geometry_proof d hd Ctr (by linarith)
  refine ⟨max CA₀ (max C' 2), cA₀, PA₀, le_trans hCA₀ (le_max_left _ _), hcA₀, hPA₀, ?_⟩
  intro CA cA PA hCA hcA hcA' hPA
  have hCA1 : CA₀ ≤ CA := (le_max_left _ _).trans hCA
  have hCA2 : C' ≤ CA := ((le_max_left _ _).trans (le_max_right _ _)).trans hCA
  have hCA3 : (2 : ℝ) ≤ CA := ((le_max_right _ _).trans (le_max_right _ _)).trans hCA
  obtain ⟨N₁, t₁, ht₁, hmain⟩ := hmainA CA cA PA hCA1 hcA hcA' hPA
  refine ⟨max N₁ Nu, min t₁ (1 / 4), lt_min ht₁ (by norm_num), ?_⟩
  intro m n₀ j u E ρ C y x D hN hj hsch hu ht hDs1 hDs2 hbroad hrec hab s hs hne hf hdn
  set t := stageScale u j m with ht_def
  have ht0 : 0 < t := stageScale_pos' hu j m
  have ht4 : t ≤ 1 / 4 := ht.le.trans (min_le_right _ _)
  have ht1 : t ≤ 1 := by linarith
  have hconn : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  obtain ⟨hx1, -, -⟩ := clr_reach n₀ j u y x s hs
  have hDx : IsDampedEndpoint x.endpoint x.r t := by
    have := D.I.physical (Fin.last D.k)
    rw [D.last, ← D.frozen] at this
    exact this
  obtain ⟨B, hb⟩ := done_basic n₀ j u y x hDx s hs hab hsch hne hf hdn
  have hrpos : ∀ i ∈ x.endpoint.active, 0 < (x.r i).im :=
    fun i _ => lt_of_lt_of_le hcP (hbroad i).1
  have hphys := clr_done_physical j u x s.2 hb.inv hab hsch hne hf hdn ht0 hrpos
  set s' := (clearingDoneExit x s.2).endpoint with hs'
  have hlast : D.I.state (Fin.last D.k) = x.endpoint := D.last
  have hyB : y ∈ B := hb.elig.1
  obtain ⟨l', T', hT'term, -, hT'anch⟩ :=
    done_trace n₀ j u Ctr hCtr y x s B hb hf hj.le ht0 ht4 D.I.anchor hrec
  have hterm : Finset.univ \ s'.active ⊆ geometryTerminals T' := by
    intro z hz
    rw [hT'term]
    show z ∈ x.terminal ∪ s.2.core ∪ s.2.inspected
    by_cases hza : z ∈ x.endpoint.active
    · have : z ∈ x.endpoint.active \ s'.active :=
        Finset.mem_sdiff.mpr ⟨hza, (Finset.mem_sdiff.mp hz).2⟩
      rw [hb.removed, ← hb.core] at this
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      rw [hrec.activeCompl] at hza
      simpa using hza
  obtain ⟨hmet, hcount, -, hover⟩ :=
    hunif m n₀ j l' u ((le_max_right _ _).trans hN) hj.le hsch hu T'
  have hmet' : ∀ v w, physicalDistance d m v w / 2 - t ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ s'.active) v w :=
    fun v w => (hmet v w).trans (AndersonAC.AgentS78Geo.terminalDistance_antitone hconn hterm v w)
  -- the committed terminal set is the complement of the committed active set
  have hTeq : (clearingDoneExit x s.2).terminal = Finset.univ \ s'.active := by
    ext z
    show z ∈ x.terminal ∪ s.2.core ∪ s.2.inspected ↔ _
    rw [hb.core]
    have hrm := hb.removed
    constructor
    · intro hz
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hza => ?_⟩
      rcases Finset.mem_union.mp hz with hz | hz
      · rcases Finset.mem_union.mp hz with hz | hz
        · have := hb.nested hza
          rw [hrec.activeCompl] at this
          exact (Finset.mem_sdiff.mp this).2 hz
        · have : z ∈ x.endpoint.active \ s'.active := by
            rw [hrm]; exact Finset.mem_union_left _ hz
          exact (Finset.mem_sdiff.mp this).2 hza
      · have : z ∈ x.endpoint.active \ s'.active := by
          rw [hrm]; exact Finset.mem_union_right _ hz
        exact (Finset.mem_sdiff.mp this).2 hza
    · intro hz
      have hza : z ∉ s'.active := (Finset.mem_sdiff.mp hz).2
      by_cases hzx : z ∈ x.endpoint.active
      · have : z ∈ x.endpoint.active \ s'.active := Finset.mem_sdiff.mpr ⟨hzx, hza⟩
        rw [hrm] at this
        rcases Finset.mem_union.mp this with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ h
      · rw [hrec.activeCompl] at hzx
        refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        simpa using hzx
  -- the hop structure of the committed matrix
  have hhops' : ∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
      (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
      ∀ a ∈ s'.active, ∀ b ∈ s'.active, s'.M a b ≠ ((J a b : ℝ) : ℂ) →
        terminalDistance (nnGraph d m) (Finset.univ \ s'.active) a b = 0 := by
    obtain ⟨l₀, T₀, hT₀, hT₀term, -⟩ := hrec.trace
    obtain ⟨J, hJs, hJ1, hJadj, hJhops⟩ := hT₀.hops
    refine ⟨J, hJs, hJ1, hJadj, fun a ha b hb' hab' => ?_⟩
    rw [← hTeq]
    refine hhops n₀ j u y x J hJadj hDx (fun a ha b hb' hab' => ?_)
      hrec.activeCompl hab s hs hne hf hdn a ha b hb' hab'
    rw [← hT₀term]; exact hJhops a ha b hb' hab'
  obtain ⟨hCT, hent, hrow, htot, hdec⟩ :=
    hmain n₀ j u E ρ C y x D ((le_max_left _ _).trans hN) hj hsch hu (ht.trans_le (min_le_left _ _))
      hDs1 hDs2 hbroad hrec hab s hs hne hf hdn hphys hmet' hhops'
  have hIC : D.I.C = CA := D.constC
  have hIc : D.I.c = cA := D.constc
  have hIP : D.I.P = PA := D.constP
  -- radii
  have hν : 0 ≤ nu d := by unfold nu delta; positivity
  have htν : 1 ≤ t ^ (-nu d) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hcr : clearRadius d m j u = t ^ (-nu d) * separationRadius j := by rw [ht_def]; rfl
  have hR0 : 0 ≤ separationRadius j := by unfold separationRadius; positivity
  have hcr0 : 0 ≤ clearRadius d m j u := by
    rw [hcr]; exact mul_nonneg (Real.rpow_nonneg ht0.le _) hR0
  have hℓR : inspectionRadius j / 2 ≤ clearRadius d m j u := by
    unfold clearRadius inspectionRadius separationRadius
    have h1 : (4 : ℝ) ^ (4 * j) ≤ (4 : ℝ) ^ (8 * j) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (0 : ℝ) ≤ (4 : ℝ) ^ (4 * j) := by positivity
    nlinarith
  -- freshness of the anchor
  have hfresh : ∀ a, D.I.anchor a ≠ y := by
    intro a hay
    obtain ⟨l, T, hTr, -, hTanch⟩ := hrec.trace
    obtain ⟨b, hbj, hba⟩ := hTanch a
    have := hTr.fresh b hbj B hb.comp ⟨y, hyB, hb.act hyB⟩ (T.anchor b) (T.anchorMem b) y hyB
    rw [hba, hay] at this
    have h0 : physicalDistance d m y y = 0 := by simp [physicalDistance]
    rw [h0] at this
    have : (0 : ℝ) ≤ separationRadius j := by unfold separationRadius; positivity
    linarith
  have hsnoc_inj : Function.Injective (Fin.snoc (α := fun _ => Torus d m) D.I.anchor y) := by
    intro a a' h
    induction a using Fin.lastCases with
    | last =>
      induction a' using Fin.lastCases with
      | last => rfl
      | cast a' => simp at h; exact absurd h.symm (hfresh a')
    | cast a =>
      induction a' using Fin.lastCases with
      | last => simp at h; exact absurd h (hfresh a)
      | cast a' => simp at h; rw [D.I.distinct h]
  -- removed sites
  have hOloc : ∀ z ∈ x.endpoint.active \ s'.active, ∃ w ∈ B,
      physicalDistance d m z w ≤ inspectionRadius j / 2 := by
    intro z hz
    rw [hb.removed] at hz
    rcases Finset.mem_union.mp hz with hzc | hzi
    · refine ⟨z, hzc, ?_⟩
      have : physicalDistance d m z z = 0 := by simp [physicalDistance]
      rw [this]; unfold inspectionRadius; positivity
    · obtain ⟨_, _, w, hw, hzw⟩ := hb.guard z hzi
      exact ⟨w, hw, hzw⟩
  have hheat := rpow_neg_nu_le_heatLimit (d := d) t ht0 ht4
  have hinspc : (s.2.inspected.card : ℝ) ≤ (heatLimit t : ℝ) := by
    have h1 := hb.inv.count hf
    have h2 := hb.inv.stepLe
    rw [AndersonAC.AgentS78Geo.heatLimit_eq] at h2
    exact_mod_cast h1.trans h2
  have hBcard : (B.card : ℝ) ≤ t ^ (-nu d) := hb.elig.2.2.1
  have hhl0 : (0 : ℝ) ≤ heatLimit t := by positivity
  refine
    { physical := by rw [← D.frozen]; exact hphys
      nested := by rw [hlast]; exact hb.nested
      activeCount := ?_
      fresh := hfresh
      removedNonempty := ?_
      removedSize := ?_
      removedLocal := ?_
      haloOverlap := ?_
      metric := hmet'
      resolventDecay := by rw [hIC, hIc]; exact hCT
      entryChange := by rw [hIC]; exact hent
      rowChange := by rw [hIC]; exact hrow
      totalChange := by rw [hIC]; exact htot
      decay := by rw [hIC, hIc, hIP]; exact hdec }
  · -- activeCount
    refine hcount.trans ?_
    have : Finset.univ \ geometryTerminals T' ⊆ s'.active := by
      intro z hz
      by_contra hza
      exact (Finset.mem_sdiff.mp hz).2 (hterm (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hza⟩))
    exact Nat.mul_le_mul_left 2 (Finset.card_le_card this)
  · -- removedNonempty
    rw [hlast, hb.removed]
    exact ⟨y, Finset.mem_union_left _ hyB⟩
  · -- removedSize
    rw [hlast, hIC, hb.removed]
    have h2 := Finset.card_union_le B s.2.inspected
    have h3 : ((B ∪ s.2.inspected).card : ℝ) ≤ B.card + s.2.inspected.card := by exact_mod_cast h2
    nlinarith
  · -- removedLocal
    rw [hlast]
    intro z hz
    obtain ⟨w, hwB, hzw⟩ := hOloc z hz
    have hwy : physicalDistance d m w y ≤ clearRadius d m j u := hb.elig.2.2.2 w hwB
    have htri : physicalDistance d m z y ≤ physicalDistance d m z w + physicalDistance d m w y := by
      unfold physicalDistance
      exact_mod_cast hconn.dist_triangle
    linarith
  · -- haloOverlap
    rw [hIC]
    intro z
    have hrad200 : 200 * D.I.Ds ≤ 200 * Ctr * t ^ (-nu d) * separationRadius j := by
      have h := hDs2
      rw [hcr] at h
      linarith
    let f : Fin (D.k + 1) → Fin l' := fun a => Classical.choose (hT'anch a)
    have hf1 : ∀ a, T'.index (f a) = j := fun a => (Classical.choose_spec (hT'anch a)).1
    have hf2 : ∀ a, T'.anchor (f a) = Fin.snoc (α := fun _ => Torus d m) D.I.anchor y a :=
      fun a => (Classical.choose_spec (hT'anch a)).2
    have h1 := overlap_le_card (fun a : Fin (D.k + 1) =>
        cube d m (Fin.snoc (α := fun _ => Torus d m) D.I.anchor y a) (200 * D.I.Ds)) z
      (Finset.univ.filter fun b : Fin l' => T'.index b = j ∧
        z ∈ cube d m (T'.anchor b) (200 * Ctr * t ^ (-nu d) * separationRadius j)) f
      (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf1 a,
        by rw [hf2 a]; exact cube_mono_radius _ hrad200 ha⟩)
      (fun a a' _ _ h => hsnoc_inj (by rw [← hf2 a, ← hf2 a']; exact congrArg T'.anchor h))
    have h2 := hover z
    have hpowν : 0 ≤ t ^ (-(d : ℝ) * nu d) := Real.rpow_nonneg ht0.le _
    have h1' : (overlap (fun a : Fin (D.k + 1) =>
        cube d m (Fin.snoc (α := fun _ => Torus d m) D.I.anchor y a) (200 * D.I.Ds)) z : ℝ) ≤
        ((Finset.univ.filter fun b : Fin l' => T'.index b = j ∧
          z ∈ cube d m (T'.anchor b) (200 * Ctr * t ^ (-nu d) * separationRadius j)).card : ℝ) := by
      exact_mod_cast h1
    exact h1'.trans (h2.trans (mul_le_mul_of_nonneg_right hCA2 hpowν))

end AndersonAC.AgentS78
