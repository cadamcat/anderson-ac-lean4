import AndersonAC.AgentS78.Construction.StagePhaseDone
import AndersonAC.AgentS78.Construction.ClearingSix

/-!
# The Lemma 7.2 trace after a DONE clearing. A DONE exit of the clearing attempt anchored at `y` adds one group to the trace
of `ClearRec` (`AgentS78Geo.extendTrace`): index `j`, core `B = theCore j u y x`, edits the
removed set `O = active \ active'` (= core ∪ inspected sites). `done_trace` gives the extended
trace with: its edits are the new terminal set, its index-`j` cores are farther than `R_j` from
every component that keeps an active site, and its index-`j` anchors include the committed
anchors followed by `y`. `done_basic` collects the structural DONE facts used by the step facts
and by the record clauses.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf extendTrace physicalDistance_symm)
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-- A nonempty core is an eligible component of the record. -/
theorem theCore_spec (j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m)
    (h : theCore (d := d) (m := m) j u y x ≠ ∅) :
    ∃ B ∈ x.components, eligibleCand (d := d) (m := m) j u y B ∧
      theCore (d := d) (m := m) j u y x = B := by
  classical
  unfold theCore at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with h1
  · obtain ⟨B, hB⟩ := Finset.card_eq_one.mp h1
    have hBm : B ∈ x.components.filter (fun B => eligibleCand (d := d) (m := m) j u y B) := by
      rw [hB]; exact Finset.mem_singleton_self B
    obtain ⟨hBc, hel⟩ := Finset.mem_filter.mp hBm
    refine ⟨B, hBc, hel, ?_⟩
    rw [hB]; simp
  · exact absurd rfl h

/-- `t^{-ν} ≤ heatLimit t` for small `t`. -/
theorem rpow_neg_nu_le_heatLimit (t : ℝ) (ht : 0 < t) (ht4 : t ≤ 1 / 4) :
    t ^ (-nu d) ≤ (heatLimit t : ℝ) := by
  have hν : 0 ≤ nu d := by unfold nu delta; positivity
  have hν1 : nu d ≤ 1 / 2 := by
    unfold nu delta
    rcases Nat.eq_zero_or_pos d with hd | hd
    · simp [hd]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  have hh : 0 ≤ heatExponent := by unfold heatExponent delta; norm_num
  have ht1 : t ≤ 1 := by linarith
  have h1 : t ^ (-nu d) ≤ t ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hs : t ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) = t⁻¹ := by
    rw [← Real.rpow_add ht]; norm_num; exact Real.rpow_neg_one t
  have hs2 : (2 : ℝ) ≤ t ^ (-(1 / 2 : ℝ)) := by
    have : (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht ht4 (by norm_num)
    refine le_trans (le_of_eq ?_) this
    rw [show (1 / 4 : ℝ) = 2⁻¹ ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hinv : t⁻¹ ≤ t ^ (-1 - heatExponent) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hfl : t ^ (-1 - heatExponent) - 1 < (heatLimit t : ℝ) := by
    unfold heatLimit
    exact Nat.sub_one_lt_floor _
  have hpos : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  nlinarith

/-- **The structural facts of a DONE exit.** -/
structure DoneBasic (n₀ j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m)
    (s : RunRecord d m × ClearScratch d m) (B : Finset (Torus d m)) : Prop where
  inv : ClrInv j u x s.2
  core : s.2.core = B
  comp : B ∈ x.components
  elig : eligibleCand (d := d) (m := m) j u y B
  act : B ⊆ x.endpoint.active
  nested : (clearingDoneExit x s.2).endpoint.active ⊆ x.endpoint.active
  removed : x.endpoint.active \ (clearingDoneExit x s.2).endpoint.active = B ∪ s.2.inspected
  guard : ∀ p ∈ s.2.inspected, guardHolds (d := d) (m := m) j B (coupledActive x) x.terminal p

theorem done_basic (n₀ j : ℕ) (u : ℝ) (y : Torus d m) (x : RunRecord d m)
    (hDx : IsDampedEndpoint x.endpoint x.r (stageScale u j m))
    (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s)
    (hab : x.aborted = false) (hsch : clearingScheduled j m) (hne : s.2.core ≠ ∅)
    (hf : s.2.failed = false) (hdn : s.2.done = true) :
    ∃ B, DoneBasic n₀ j u y x s B := by
  obtain ⟨-, hcore, -⟩ := clr_reach n₀ j u y x s hs
  have hI := clrInv_reach n₀ j u y x hDx s hs
  obtain ⟨hnest, hrem, hcorerem⟩ := clr_done_removed j u x s.2 hI hab hsch hne hf hdn
  obtain ⟨hA, hcx⟩ := clr_done_active j u x s.2 hI hab hsch hne hf hdn
  obtain ⟨B, hBc, hel, hBeq⟩ := theCore_spec j u y x (hcore ▸ hne)
  rw [hBeq] at hcore
  have hguard : ClrGuarded n₀ j u y :=
    clrGuarded_of_fail n₀ j u y (fun rc sc p h => clearingFailGuarded_proof d m j u rc sc p h)
  have hinsp := hguard x s hs
  refine ⟨B, hI, hcore, hBc, hel, hcore ▸ hcx, hnest, ?_, fun p hp => hcore ▸ hinsp p hp⟩
  apply Finset.Subset.antisymm (hcore ▸ hrem)
  intro z hz
  rcases Finset.mem_union.mp hz with hzB | hzi
  · exact hcorerem (hcore ▸ hzB)
  · have hg := hinsp z hzi
    have hza : z ∈ x.endpoint.active := coupledActive_subset_active x hg.1
    refine Finset.mem_sdiff.mpr ⟨hza, ?_⟩
    rw [clr_doneExit_endpoint x s.2 hA]
    exact Finset.disjoint_left.mp (hI.inspA hf) hzi

/-- **The trace extended by the committed group.** -/
theorem done_trace (n₀ j : ℕ) (u Ctr : ℝ) (hCtr : 2 ≤ Ctr) (y : Torus d m) (x : RunRecord d m)
    (s : RunRecord d m × ClearScratch d m) (B : Finset (Torus d m))
    (hb : DoneBasic n₀ j u y x s B) (hf : s.2.failed = false)
    (hn₀j : n₀ ≤ j) (ht0 : 0 < stageScale u j m) (ht4 : stageScale u j m ≤ 1 / 4)
    {k : ℕ} (anchor : Fin k → Torus d m) (hrec : ClearRec Ctr n₀ u j x anchor) :
    ∃ l, ∃ T' : ClearingGeometry d m n₀ j l u Ctr,
      geometryTerminals T' = (clearingDoneExit x s.2).terminal ∧
      (∀ a, T'.index a = j → ∀ C ∈ x.components,
        (∃ y' ∈ C, y' ∈ (clearingDoneExit x s.2).endpoint.active) →
        ∀ z ∈ T'.core a, ∀ w ∈ C, separationRadius j < physicalDistance d m z w) ∧
      (∀ a, ∃ b, T'.index b = j ∧ T'.anchor b = Fin.snoc (α := fun _ => Torus d m) anchor y a) := by
  set t := stageScale u j m
  obtain ⟨l, T, hTr, hTterm, hTanch⟩ := hrec.trace
  set O := x.endpoint.active \ (clearingDoneExit x s.2).endpoint.active with hO
  have hyB : y ∈ B := hb.elig.1
  have hOloc : ∀ z ∈ O, ∃ w ∈ B, physicalDistance d m z w ≤ inspectionRadius j / 2 := by
    intro z hz
    rw [hO, hb.removed] at hz
    rcases Finset.mem_union.mp hz with hzc | hzi
    · refine ⟨z, hzc, ?_⟩
      have : physicalDistance d m z z = 0 := by simp [physicalDistance]
      rw [this]; unfold inspectionRadius; positivity
    · obtain ⟨_, _, w, hw, hzw⟩ := hb.guard z hzi
      exact ⟨w, hw, hzw⟩
  have hBcard : (B.card : ℝ) ≤ t ^ (-nu d) := hb.elig.2.2.1
  have hheat := rpow_neg_nu_le_heatLimit (d := d) t ht0 ht4
  have hinspc : (s.2.inspected.card : ℝ) ≤ (heatLimit t : ℝ) := by
    have h1 := hb.inv.count hf
    have h2 := hb.inv.stepLe
    rw [AndersonAC.AgentS78Geo.heatLimit_eq] at h2
    exact_mod_cast h1.trans h2
  have hOcard : (O.card : ℝ) ≤ 2 * (heatLimit t : ℝ) := by
    rw [hO, hb.removed]
    have h2 := Finset.card_union_le B s.2.inspected
    have h3 : ((B ∪ s.2.inspected).card : ℝ) ≤ B.card + s.2.inspected.card := by exact_mod_cast h2
    linarith
  have hhl0 : (0 : ℝ) ≤ heatLimit t := by positivity
  have hrad : ∀ z ∈ B, physicalDistance d m y z ≤ t ^ (-nu d) * separationRadius j := by
    intro z hz
    rw [physicalDistance_symm]
    exact hb.elig.2.2.2 z hz
  have hBact : ∃ y' ∈ B, y' ∈ x.endpoint.active := ⟨y, hyB, hb.act hyB⟩
  have hsep : ∀ a, T.index a = j → ∀ z ∈ T.core a, ∀ w ∈ B,
      separationRadius j < physicalDistance d m z w :=
    fun a ha z hz w hw => hTr.fresh a ha B hb.comp hBact z hz w hw
  have hsize : (O.card : ℝ) ≤ Ctr * (heatLimit t : ℝ) := by nlinarith
  refine ⟨l + 1, extendTrace T B O y hn₀j hyB hBcard hrad hsep hsize hOloc, ?_, ?_, ?_⟩
  · -- edits = new terminal set
    ext z
    simp only [geometryTerminals, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha⟩
      induction a using Fin.lastCases with
      | last =>
        simp only [extendTrace, Fin.lastCases_last] at ha
        rw [hO, hb.removed] at ha
        show z ∈ x.terminal ∪ s.2.core ∪ s.2.inspected
        rw [hb.core]
        rcases Finset.mem_union.mp ha with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ h
      | cast a =>
        simp only [extendTrace, Fin.lastCases_castSucc] at ha
        show z ∈ x.terminal ∪ s.2.core ∪ s.2.inspected
        refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        rw [← hTterm]
        simp only [geometryTerminals, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨a, ha⟩
    · intro hz
      change z ∈ x.terminal ∪ s.2.core ∪ s.2.inspected at hz
      rw [hb.core] at hz
      rcases Finset.mem_union.mp hz with h | h
      · rcases Finset.mem_union.mp h with h | h
        · rw [← hTterm] at h
          simp only [geometryTerminals, Finset.mem_biUnion, Finset.mem_univ, true_and] at h
          obtain ⟨a, ha⟩ := h
          exact ⟨a.castSucc, by simpa [extendTrace] using ha⟩
        · exact ⟨Fin.last l, by
            simp only [extendTrace, Fin.lastCases_last]
            rw [hO, hb.removed]; exact Finset.mem_union_left _ h⟩
      · exact ⟨Fin.last l, by
          simp only [extendTrace, Fin.lastCases_last]
          rw [hO, hb.removed]; exact Finset.mem_union_right _ h⟩
  · -- freshness
    intro a ha C hC hCact z hz w hw
    induction a using Fin.lastCases with
    | last =>
      simp only [extendTrace, Fin.lastCases_last] at hz
      by_cases hCB : C = B
      · subst hCB
        exfalso
        obtain ⟨y', hy'C, hy'a⟩ := hCact
        have : y' ∈ O := by rw [hO, hb.removed]; exact Finset.mem_union_left _ hy'C
        exact (Finset.mem_sdiff.mp this).2 hy'a
      · exact hrec.compSep B hb.comp C hC (Ne.symm hCB) z hz w hw
    | cast a =>
      simp only [extendTrace, Fin.lastCases_castSucc] at ha hz
      obtain ⟨y', hy'C, hy'a⟩ := hCact
      exact hTr.fresh a ha C hC ⟨y', hy'C, hb.nested hy'a⟩ z hz w hw
  · -- anchors
    intro a
    induction a using Fin.lastCases with
    | last => exact ⟨Fin.last l, by simp [extendTrace]⟩
    | cast a =>
      obtain ⟨b, hb1, hb2⟩ := hTanch a
      exact ⟨b.castSucc, by simp [extendTrace, hb1, hb2]⟩

end AndersonAC.AgentS78
