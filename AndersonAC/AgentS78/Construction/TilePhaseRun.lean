import AndersonAC.AgentS78.Construction.TilePhaseStart
import AndersonAC.AgentS78.Construction.RunOps
import AndersonAC.AgentS78.Construction.MarkingRule
import AndersonAC.AgentS78.Construction.SimpleDisciplines

/-!
# WP10 construction, tile phase: the operations `(j, 0, y)` of the schedule

agent-s78tphase (2026-10-14). The tile operations of stage `j` run in the order of the site
rank of `y`; operation `(j, 0, y)` is the block of the tile anchored at `y` (`tileAt`), or the
identity. With `doneUpTo P j r` = tiles without sites or with anchor rank `< r`:

* `tileOp_keeps`: operation `(j, 0, y)` maps `TileSweepInv … (doneUpTo P j (rank y))` into
  `TileSweepInv … (doneUpTo P j (rank y + 1))`, in the form of `blockRun_of_runOps`'s `hInv`
  (states reached along real local answers), given the completeness contract
  `TileCompleteStatement` (accepted trials delete every active bit port of their tile; the
  slot simulation on real answers, requested separately);
* `doneUpTo_zero_core` and `doneUpTo_all`: the start (`done = ∅`, by `tileSweepInv_start`)
  and the end (`done = univ`, by `TileSweepCore.live_end`) of the tile operations.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

section Done
variable (P : TilePlan d m) (j : ℕ)

/-- Tiles processed before the operation at anchor rank `r`. -/
def doneUpTo (r : ℕ) : Finset (Fin (P.cover j).cover.count) := by
  classical
  exact Finset.univ.filter fun S =>
    tileSites (P.cover j) S = ∅ ∨ ((siteRank d m (tileAnchor (P.cover j) S) : ℕ) < r)

theorem siteAt_zero_mem (S : Finset (Torus d m)) (hS : S.Nonempty) :
    ∃ i ∈ S, siteAt S 0 = some i := by
  unfold siteAt
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hlen : L.length = S.card := by rw [hL, Finset.length_sort, Finset.card_map]
  have hv' : 0 < L.length := hlen ▸ hS.card_pos
  rw [List.getElem?_eq_getElem hv']
  have hmem : L[0] ∈ S.map (siteRank d m).toEmbedding :=
    (Finset.mem_sort _).mp (List.getElem_mem hv')
  obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hmem
  refine ⟨a, ha, ?_⟩
  simp only [Option.map_some, Option.some.injEq]
  rw [← hae]; simp

theorem tileAnchor_mem_plan (S : Fin (P.cover j).cover.count)
    (hS : (tileSites (P.cover j) S).Nonempty) :
    tileAnchor (P.cover j) S ∈ tileSites (P.cover j) S := by
  obtain ⟨i, hi, hs⟩ := siteAt_zero_mem _ hS
  simp [tileAnchor, hs, hi]

/-- A nonempty tile is determined by its anchor. -/
theorem tile_eq_of_anchor {S S' : Fin (P.cover j).cover.count}
    (hS : (tileSites (P.cover j) S).Nonempty) (hS' : (tileSites (P.cover j) S').Nonempty)
    (h : tileAnchor (P.cover j) S = tileAnchor (P.cover j) S') : S = S' := by
  have h1 := mem_tileSites.mp (tileAnchor_mem_plan P j S hS)
  have h2 := mem_tileSites.mp (tileAnchor_mem_plan P j S' hS')
  rw [h] at h1
  exact tile_unique h1 h2

theorem tileAt_some_spec {y : Torus d m} {T : Fin (P.cover j).cover.count}
    (h : tileAt P j y = some T) :
    (tileSites (P.cover j) T).Nonempty ∧ tileAnchor (P.cover j) T = y := by
  classical
  unfold tileAt at h
  split_ifs at h with hex
  · cases h; exact Classical.choose_spec hex

theorem tileAt_none_spec {y : Torus d m} (h : tileAt P j y = none)
    (S : Fin (P.cover j).cover.count) (hS : (tileSites (P.cover j) S).Nonempty) :
    tileAnchor (P.cover j) S ≠ y := by
  classical
  unfold tileAt at h
  split_ifs at h with hex
  intro hy
  exact hex ⟨S, hS, hy⟩

theorem not_mem_doneUpTo {y : Torus d m} {T : Fin (P.cover j).cover.count}
    (h : tileAt P j y = some T) : T ∉ doneUpTo P j (siteRank d m y) := by
  classical
  obtain ⟨hne, ha⟩ := tileAt_some_spec P j h
  simp only [doneUpTo, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
  exact ⟨hne.ne_empty, by rw [ha]; exact lt_irrefl _⟩

theorem doneUpTo_succ_some {y : Torus d m} {T : Fin (P.cover j).cover.count}
    (h : tileAt P j y = some T) :
    insert T (doneUpTo P j (siteRank d m y)) = doneUpTo P j (siteRank d m y + 1) := by
  classical
  obtain ⟨hne, ha⟩ := tileAt_some_spec P j h
  ext S
  simp only [doneUpTo, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | h' | h')
    · right; rw [ha]; exact Nat.lt_succ_self _
    · left; exact h'
    · right; omega
  · rintro (h' | h')
    · right; left; exact h'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h' with h' | h'
      · right; right; exact h'
      · by_cases hS : tileSites (P.cover j) S = ∅
        · right; left; exact hS
        · left
          refine tile_eq_of_anchor P j (Finset.nonempty_iff_ne_empty.mpr hS) hne ?_
          rw [ha]; exact (siteRank d m).injective (Fin.ext h')

theorem doneUpTo_succ_none {y : Torus d m} (h : tileAt P j y = none) :
    doneUpTo P j (siteRank d m y) = doneUpTo P j (siteRank d m y + 1) := by
  classical
  ext S
  simp only [doneUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h' | h')
    · left; exact h'
    · right; omega
  · rintro (h' | h')
    · left; exact h'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h' with h' | h'
      · right; exact h'
      · by_cases hS : tileSites (P.cover j) S = ∅
        · left; exact hS
        · exfalso
          exact tileAt_none_spec P j h S (Finset.nonempty_iff_ne_empty.mpr hS)
            ((siteRank d m).injective (Fin.ext h'))

theorem doneUpTo_all : doneUpTo P j (siteCount d m) = Finset.univ := by
  classical
  ext S
  simp only [doneUpTo, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  right; exact (siteRank d m (tileAnchor (P.cover j) S)).isLt

end Done

section Mono
variable {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}

/-- Adding tiles without sites to `done` keeps the invariant. -/
theorem TileSweepCore.mono_empty {done done' : Finset (Fin (P.cover j).cover.count)}
    {x : RunRecord d m} (h : TileSweepCore C P j n₀ u E ρ Cb done x) (hsub : done ⊆ done')
    (hemp : ∀ S ∈ done', S ∉ done → tileSites (P.cover j) S = ∅) :
    TileSweepCore C P j n₀ u E ρ Cb done' x := by
  obtain ⟨blocks, hb1, hb2, hb3, hb4, hb5⟩ := h.blocks
  refine { h with
    blocks := ⟨blocks, hb1, hb2, hb3, fun S hS => hb4 S (fun h' => hS (hsub h')), hb5⟩
    done_deleted := fun S hS i hi => ?_
    undone_nonterminal := fun S hS => h.undone_nonterminal S (fun h' => hS (hsub h'))
    final_no_pending := fun hf S hS => h.final_no_pending hf S (fun h' => hS (hsub h'))
    final_prefix := fun hf S hS => h.final_prefix hf S (fun h' => hS (hsub h')) }
  by_cases hS' : S ∈ done
  · exact h.done_deleted S hS' i hi
  · rw [hemp S hS hS'] at hi; exact absurd hi (Finset.notMem_empty i)

/-- The start of the tile operations: from `done = ∅` to `doneUpTo … 0`. -/
theorem doneUpTo_zero_core {x : RunRecord d m} (h : TileSweepCore C P j n₀ u E ρ Cb ∅ x) :
    TileSweepCore C P j n₀ u E ρ Cb (doneUpTo P j 0) x := by
  classical
  refine h.mono_empty (Finset.empty_subset _) fun S hS _ => ?_
  simp only [doneUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rcases hS with hS | hS
  · exact hS
  · exact absurd hS (Nat.not_lt_zero _)

end Mono

/-! ## The completeness contract and the tile operations -/

/-- **Completeness of accepted trials on real answers (contract).** Along real local
answers with `M (tileOrderIndex j T a) = |T|` for every trial `a`, a halted, non-aborted exit
of the block of `T` has deleted the bit port of every active site of `T`, when the entering
record has every such bit port live and no such site terminal (05:338–344: the order is a
permutation of the tile; skipped slots are inactive or already deleted). -/
def TileCompleteStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M),
    TileOrderSizes P j T M → x.aborted = false →
    (∀ i ∈ tileSites (P.cover j) T, i ∈ x.endpoint.active →
      i ∉ x.terminal ∧ ((i, false) : Port d m) ∈ (x.sweep.state x.sweep.length).live) →
    (∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false) →
    (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true →
    TileAcceptComplete P j T x (localState M (tileBlock P j T) x k ω).1

section Ops
variable {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}
  {ClSc : Type} [MeasurableSpace ClSc]

/-- **The tile block of `T` keeps the invariant along real answers.** -/
theorem tileBlock_keeps_local (hcomp : TileCompleteStatement)
    {done : Finset (Fin (P.cover j).cover.count)} {T : Fin (P.cover j).cover.count}
    (hT : T ∉ done) (hu : 0 < P.u) (hj : P.n₀ < j) (hjm : j ≤ m + 1)
    (M : ℕ → ℕ) (hM : TileOrderSizes P j T M) (x : RunRecord d m)
    (hx : x ∈ TileSweepInv C P j n₀ u E ρ Cb done) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hrun : ∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false)
    (hh : (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true) :
    (tileBlock P j T).exit (localState M (tileBlock P j T) x k ω) ∈
      TileSweepInv C P j n₀ u E ρ Cb (insert T done) := by
  refine tileBlock_keeps hx hT (fun _ => xiBound_of_scales P j T x hu hj hjm)
    (sweepW_pos P.u hu m j (by omega) hjm) _
    (localState_reach M (tileBlock P j T) x ω k hrun) hh ?_
  intro hab' i hi hia
  cases hab : x.aborted
  · have h := hx hab
    exact hcomp d m P j T M x k ω hM hab
      (fun i hi hia => ⟨h.undone_nonterminal T hT i hi hia, h.tile_live_v3 hT i hi hia⟩)
      hrun hh hab' i hi hia
  · -- an aborted record enters a halted block and exits unchanged
    exfalso
    have hs := reach_of_aborted (P := P) (j := j) (T := T) hab _
      (localState_reach M (tileBlock P j T) x ω k hrun)
    rw [hs] at hab'
    simp [tileBlock, hab] at hab'

/-- **Operation `(j, 0, y)` of the schedule keeps the tile-phase invariant** (the `hInv` shape
of `blockRun_of_runOps`). -/
theorem tileOp_keeps (hcomp : TileCompleteStatement) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (hu : 0 < P.u) (hj : P.n₀ < j) (hjm : j ≤ m + 1) (y : Torus d m)
    (x : RunRecord d m)
    (hx : x ∈ TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j (siteRank d m y)))
    (k : ℕ) (ω : RandomSources (Torus d m) (tileOrderSize P))
    (hrun : ∀ k' < k, (runOp P ts₀ cl₀ clr j 0 y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ clr j 0 y) x k' ω) = false)
    (hh : (runOp P ts₀ cl₀ clr j 0 y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ clr j 0 y) x k ω) = true) :
    (runOp P ts₀ cl₀ clr j 0 y).exit
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ clr j 0 y) x k ω) ∈
      TileSweepInv C P j n₀ u E ρ Cb (doneUpTo P j (siteRank d m y + 1)) := by
  have hjj : P.n₀ < j ∧ j ≤ m + 1 := ⟨hj, hjm⟩
  have hpe : ∀ s : RunRecord d m × TileScratch d m, tileProj (tileEmbed cl₀ s) = s :=
    fun _ => rfl
  rcases hT : tileAt P j y with _ | T
  · -- no tile anchored at `y`: the identity block
    have hop : runOp P ts₀ cl₀ clr j 0 y = simpleBlock (ts₀, cl₀) id := by
      simp only [runOp, hjj, and_self, if_true, hT]
    rw [hop] at hh ⊢
    rw [← doneUpTo_succ_none P j hT]
    have := simpleBlock_reach (ts₀, cl₀) (id : RunRecord d m → RunRecord d m) x _
      (localState_reach _ _ x ω k (by rw [hop] at hrun; exact hrun))
    rw [this]
    simpa [simpleBlock] using hx
  · have hop : runOp P ts₀ cl₀ clr j 0 y = (tileBlock P j T).embed (tileEmbed cl₀) tileProj := by
      simp only [runOp, hjj, and_self, if_true, hT]
    rw [hop] at hh hrun ⊢
    rw [← doneUpTo_succ_some P j hT]
    have hM : TileOrderSizes P j T (tileOrderSize P) := fun a => tileOrderSize_index P j T a
    simp only [localState_embed _ _ _ _ hpe] at hh hrun ⊢
    simp only [Block.embed, hpe] at hh hrun ⊢
    exact tileBlock_keeps_local hcomp (not_mem_doneUpTo P j hT) hu hj hjm _ hM x hx k ω hrun hh

end Ops

end AndersonAC.AgentS78

/-! ## The stage start from the stage history alone (structural hypotheses discharged) -/

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem BoundaryHist.damped {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C : ℝ} {k : ℕ}
    {s : Endpoint (Torus d m)} {rk : Torus d m → ℂ} (h : BoundaryHist n₀ u E ρ C k s rk)
    (hk : n₀ ≤ k) : IsDampedEndpoint s rk (stageScale u k m) := by
  obtain ⟨state, r, -, -, hs, hr, -, hph, -⟩ := h
  have := hph k hk le_rfl
  rwa [hs, hr] at this

/-- **(a) with the support hypothesis discharged by the stage history.** -/
theorem tileSweepInv_start' {C : ℝ} {P : TilePlan d m} {j n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {Cb : ℝ}
    (t : ℝ) (z : RunRecord d m) (hab : z.aborted = false) (hnj : n₀ < j)
    (hist : BoundaryHist n₀ u E ρ Cb (j - 1) z.endpoint z.r)
    (hin : StageStartInputs C P j (sweepStartMap (sweepTheta P.u m j) t z))
    (hphys : PhysicalIdentity E z)
    (hterm : ∀ i ∈ z.endpoint.active, i ∉ z.terminal)
    (hpend : IsFinalSweep m j → ∀ i ∈ z.endpoint.active, i ∉ z.pending)
    (hpref : IsFinalSweep m j → ∀ i ∈ z.endpoint.active, z.prefixLength i = m - P.n₀) :
    TileSweepCore C P j n₀ u E ρ Cb (doneUpTo P j 0)
      (sweepStartMap (sweepTheta P.u m j) t z) :=
  doneUpTo_zero_core (tileSweepInv_start C P j t z hab hist
    (fun i k h => (hist.damped (by omega)).2.1 i k h) hin hphys hterm hpend hpref)

end AndersonAC.AgentS78
