import AndersonAC.AgentS78.Construction.StagePhaseTrace

/-!
# The record clauses of the clearing phase along the clearing attempts

agent-s78phase2. `ClearRecPos … j r x anchor` is `ClearRec` (StagePhaseDone.lean) plus two
clauses about the components not yet reached by the anchor scan (every site of rank `≥ r`):
they are still pending, and pending sites outside them lie farther than `R_j − ℓ_j/2`
(07-assembly.tex:200–209; the form of `ClearingGoodAt.separated` that survives failed
clearings, see StagePhaseSepDefect.lean at 4818b1d; resolved by 06976a5). At the clearing index `opIndex j 2 y` the scan
position is `r = rank y`.

* `clearRecPos_fail`: a FAIL exit keeps it (position `r + 1`);
* `clearRecPos_done`: a DONE exit keeps it with the anchors extended by `y`, given the Schur
  support of the committed matrix (`ClearingDoneHopsStatement`, frozen, mechanical);
* `ClearPhaseR`: clearing-phase data with these clauses, the scale-radius window and the broad
  damping; `clearingBlockR_keeps` and `clearOpR_hInv` (schedule form, kind 2).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf physicalDistance_symm)
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-- **Record clauses of the clearing phase at scan position `r`.** -/
structure ClearRecPos (Ctr : ℝ) (n₀ : ℕ) (u : ℝ) (j r : ℕ) (x : RunRecord d m) {k : ℕ}
    (anchor : Fin k → Torus d m) : Prop where
  base : ClearRec Ctr n₀ u j x anchor
  untouched : ∀ C ∈ x.components, (∀ c ∈ C, r ≤ (siteRank d m c).val) → C ⊆ x.pending
  sepU : ∀ C ∈ x.components, (∀ c ∈ C, r ≤ (siteRank d m c).val) → ∀ z ∈ x.pending, z ∉ C →
    ∀ w ∈ C, separationRadius j - inspectionRadius j / 2 < physicalDistance d m z w

theorem ClearRecPos.mono {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j r r' : ℕ} {x : RunRecord d m} {k : ℕ}
    {anchor : Fin k → Torus d m} (h : ClearRecPos Ctr n₀ u j r x anchor) (hr : r ≤ r') :
    ClearRecPos Ctr n₀ u j r' x anchor where
  base := h.base
  untouched C hC hCr := h.untouched C hC (fun c hc => hr.trans (hCr c hc))
  sepU C hC hCr := h.sepU C hC (fun c hc => hr.trans (hCr c hc))

theorem comp_disjoint {Ctr : ℝ} {n₀ : ℕ} {u : ℝ} {j : ℕ} {x : RunRecord d m} {k : ℕ}
    {anchor : Fin k → Torus d m} (h : ClearRec Ctr n₀ u j x anchor) {C C' : Finset (Torus d m)}
    (hC : C ∈ x.components) (hC' : C' ∈ x.components) (hne : C ≠ C') : Disjoint C C' := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have := h.compSep C hC C' hC' hne z hz z hz'
  have h0 : physicalDistance d m z z = 0 := by simp [physicalDistance]
  rw [h0] at this
  have : (0 : ℝ) ≤ separationRadius j := by unfold separationRadius; positivity
  linarith

/-- The attempted component consists of sites of rank at least that of its anchor. -/
theorem core_ranks {j : ℕ} {u : ℝ} {y : Torus d m} {B : Finset (Torus d m)}
    (h : eligibleCand (d := d) (m := m) j u y B) : ∀ c ∈ B, (siteRank d m y).val ≤ (siteRank d m c).val :=
  h.2.1.2

/-- **A FAIL exit keeps the record clauses** (scan position advances). -/
theorem clearRecPos_fail (n₀ j : ℕ) (u Ctr : ℝ) (y : Torus d m) (x : RunRecord d m)
    {k : ℕ} (anchor : Fin k → Torus d m)
    (hx : ClearRecPos Ctr n₀ u j (siteRank d m y).val x anchor)
    (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s) (hne : s.2.core ≠ ∅) :
    ClearRecPos Ctr n₀ u j ((siteRank d m y).val + 1)
      (clearingFailExit (d := d) (m := m) j y x s.2) anchor := by
  obtain ⟨-, hcore, -⟩ := clr_reach n₀ j u y x s hs
  obtain ⟨B, hBc, hel, hBeq⟩ := theCore_spec j u y x (hcore ▸ hne)
  rw [hBeq] at hcore
  have hguard : ClrGuarded n₀ j u y :=
    clrGuarded_of_fail n₀ j u y (fun rc sc p h => clearingFailGuarded_proof d m j u rc sc p h)
  have hinsp := hguard x s hs
  rw [hcore] at hinsp
  have hBpend : B ⊆ x.pending := hx.untouched B hBc (core_ranks hel)
  have hyB : y ∈ B := hel.1
  have hrec := hx.base
  have hconn : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  have hℓ : (0 : ℝ) ≤ inspectionRadius j / 2 := by unfold inspectionRadius; positivity
  -- a component of the later scan is not the attempted one
  have hCB : ∀ C ∈ x.components, (∀ c ∈ C, (siteRank d m y).val + 1 ≤ (siteRank d m c).val) →
      C ≠ B := by
    intro C _ hCr hCB
    subst hCB
    have := hCr y hyB
    omega
  have hpend' : (clearingFailExit (d := d) (m := m) j y x s.2).pending =
      x.pending ∪ B ∪ s.2.inspected := by
    show x.pending ∪ s.2.core ∪ s.2.inspected = _; rw [hcore]
  refine ⟨⟨?_, hrec.activeCompl, ?_, ?_, hrec.compSep, hrec.componentDiam, ?_⟩, ?_, ?_⟩
  · intro i hi hip
    rw [hpend'] at hip
    exact hrec.coupled i hi (fun h => hip (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  · rw [hpend']
    refine Finset.union_subset (Finset.union_subset hrec.pendingActive
      (hBpend.trans hrec.pendingActive)) ?_
    intro p hp
    exact coupledActive_subset_active x (hinsp p hp).1
  · intro C hC
    rcases hrec.compClass C hC with h | h
    · left; rw [hpend']; exact h.trans (Finset.subset_union_left.trans Finset.subset_union_left)
    · right; exact h
  · obtain ⟨l, T, h1, h2, h3⟩ := hrec.trace
    exact ⟨l, T, ⟨h1.hops, h1.fresh⟩, h2, h3⟩
  · intro C hC hCr
    rw [hpend']
    exact (hx.untouched C hC (fun c hc => (Nat.le_succ _).trans (hCr c hc))).trans
      (Finset.subset_union_left.trans Finset.subset_union_left)
  · intro C hC hCr z hz hzC w hw
    have hCB' := hCB C hC hCr
    rw [hpend'] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact hx.sepU C hC (fun c hc => (Nat.le_succ _).trans (hCr c hc)) z hz hzC w hw
      · have := hrec.compSep B hBc C hC (Ne.symm hCB') z hz w hw
        linarith
    · obtain ⟨_, _, b, hb, hzb⟩ := hinsp z hz
      have h1 := hrec.compSep B hBc C hC (Ne.symm hCB') b hb w hw
      have htri : physicalDistance d m b w ≤ physicalDistance d m b z + physicalDistance d m z w := by
        unfold physicalDistance; exact_mod_cast hconn.dist_triangle
      rw [physicalDistance_symm b z] at htri
      linarith

/-- **A DONE exit keeps the record clauses**, with the anchors extended by `y`. -/
theorem clearRecPos_done (hhops : ClearingDoneHopsStatement d) (n₀ j : ℕ) (u Ctr : ℝ)
    (hCtr : 2 ≤ Ctr) (y : Torus d m) (x : RunRecord d m) {k : ℕ} (anchor : Fin k → Torus d m)
    (hx : ClearRecPos Ctr n₀ u j (siteRank d m y).val x anchor)
    (hDx : IsDampedEndpoint x.endpoint x.r (stageScale u j m))
    (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s)
    (hab : x.aborted = false) (hsch : clearingScheduled j m) (hne : s.2.core ≠ ∅)
    (hf : s.2.failed = false) (hdn : s.2.done = true)
    (hn₀j : n₀ ≤ j) (ht0 : 0 < stageScale u j m) (ht4 : stageScale u j m ≤ 1 / 4) :
    ClearRecPos Ctr n₀ u j ((siteRank d m y).val + 1) (clearingDoneExit x s.2)
      (Fin.snoc (α := fun _ => Torus d m) anchor y) := by
  have hrec := hx.base
  obtain ⟨B, hb⟩ := done_basic n₀ j u y x hDx s hs hab hsch hne hf hdn
  obtain ⟨l', T', hT'term, hT'fresh, hT'anch⟩ :=
    done_trace n₀ j u Ctr hCtr y x s B hb hf hn₀j ht0 ht4 anchor hrec
  set x' := clearingDoneExit x s.2 with hx'
  have hyB : y ∈ B := hb.elig.1
  have hO : x.endpoint.active \ x'.endpoint.active = B ∪ s.2.inspected := hb.removed
  have hterm' : x'.terminal = x.terminal ∪ B ∪ s.2.inspected := by
    show x.terminal ∪ s.2.core ∪ s.2.inspected = _; rw [hb.core]
  have hpend' : x'.pending = x.pending \ (B ∪ s.2.inspected) := by
    show x.pending \ (s.2.core ∪ s.2.inspected) = _; rw [hb.core]
  have hcomp' : x'.components = x.components := rfl
  have hact' : x'.endpoint.active = x.endpoint.active \ (B ∪ s.2.inspected) := by
    rw [← hO]
    ext z
    simp only [Finset.mem_sdiff]
    constructor
    · intro h; exact ⟨hb.nested h, fun h' => h'.2 h⟩
    · rintro ⟨h1, h2⟩; by_contra h3; exact h2 ⟨h1, h3⟩
  have hCB : ∀ C ∈ x.components, (∀ c ∈ C, (siteRank d m y).val + 1 ≤ (siteRank d m c).val) →
      C ≠ B := by
    intro C _ hCr hCB
    subst hCB
    have := hCr y hyB
    omega
  -- a pending component other than `B` keeps its sites pending
  have hkeep : ∀ C ∈ x.components, C ≠ B → C ⊆ x.pending → C ⊆ x'.pending := by
    intro C hC hCB' hCp z hz
    rw [hpend']
    refine Finset.mem_sdiff.mpr ⟨hCp hz, fun h => ?_⟩
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.disjoint_left.mp (comp_disjoint hrec hC hb.comp hCB') hz h
    · exact (hb.guard z h).1 |> fun h' => (coupledActive_not_pending x h') (hCp hz)
  obtain ⟨l₀, T₀, hT₀, hT₀term, -⟩ := hrec.trace
  obtain ⟨J, hJs, hJ1, hJadj, hJhops⟩ := hT₀.hops
  have hMre : ∀ a b, (x.endpoint.M a b).im = 0 := fun a b => (hDx.1 a b).2
  have hhopsx : ∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active,
      x.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) → terminalDistance (nnGraph d m) x.terminal a b = 0 := by
    intro a ha b hb' hab'
    have := hJhops a ha b hb' hab'
    rwa [hT₀term] at this
  have hhops' := hhops n₀ j u y x J hJadj hDx hhopsx hrec.activeCompl hab s hs hne hf hdn
  refine ⟨⟨?_, ?_, ?_, ?_, hrec.compSep, hrec.componentDiam, ?_⟩, ?_, ?_⟩
  · -- coupled
    intro i hi hip
    rw [hact'] at hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.mp hi
    exact hrec.coupled i hi1 (fun h => hip (by rw [hpend']; exact Finset.mem_sdiff.mpr ⟨h, hi2⟩))
  · -- activeCompl
    rw [hact', hterm', hrec.activeCompl]
    ext z; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]; tauto
  · -- pendingActive
    rw [hpend', hact']
    exact Finset.sdiff_subset_sdiff hrec.pendingActive le_rfl
  · -- compClass
    intro C hC
    by_cases hCB' : C = B
    · right; subst hCB'; rw [hterm']
      exact fun z hz => Finset.mem_union_left _ (Finset.mem_union_right _ hz)
    · rcases hrec.compClass C hC with h | h
      · left; exact hkeep C hC hCB' h
      · right; rw [hterm']; exact h.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  · -- trace
    refine ⟨l', T', ⟨⟨J, hJs, hJ1, hJadj, fun a ha b hb' hab' => ?_⟩, ?_⟩, hT'term, hT'anch⟩
    · rw [hT'term]; exact hhops' a ha b hb' hab'
    · intro a ha C hC hCact z hz w hw
      exact hT'fresh a ha C hC hCact z hz w hw
  · -- untouched
    intro C hC hCr
    exact hkeep C hC (hCB C hC hCr)
      (hx.untouched C hC (fun c hc => (Nat.le_succ _).trans (hCr c hc)))
  · -- sepU
    intro C hC hCr z hz hzC w hw
    rw [hpend'] at hz
    exact hx.sepU C hC (fun c hc => (Nat.le_succ _).trans (hCr c hc)) z
      (Finset.mem_sdiff.mp hz).1 hzC w hw

end AndersonAC.AgentS78
