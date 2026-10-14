import AndersonAC.AgentS78.Construction.BoxPhases

/-!
# WP10 construction: installed values at the final record (agent-s78box)

`runTrueValues_of_parts`: `RunTrueValuesStatement d` (BoxPhases.lean) from

* `TileTrueValuesStatement` (TrueValues.lean, frozen; luna-s78truev): tile blocks keep
  `TrueValues` along the answers of `ω`, given the stage prefix length on the coupled active sites
  of the tile — supplied here by `RunBasics` (`SweepProps.undone`);
* `ClearingTrueValuesStatement` (new): clearing blocks keep `TrueValues` along the answers of `ω`
  (DONE installs `installed + resids = λ V` on core ∪ pivots, FAIL marks pending);
* `RunAllTerminalStatement` (new): every site is terminal at the record entering stage `m + 2`.

The query-free operations keep `TrueValues` (`KeepsTV`). The invariant
`RunBasics P n ∩ TrueValues n₀ u ω` is propagated along the actual run by
`blockPrestate_mem_pathwise`; at the end `installed_eq_true`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

/-- **Clearing blocks keep the true installed values** along the answers of `ω` (new contract). -/
def ClearingTrueValuesStatement : Prop :=
  ∀ (d m n₀ j : ℕ) (u : ℝ) (y : Torus d m) (M : ℕ → ℕ) (ω : RandomSources (Torus d m) M)
    (x : RunRecord d m) (k : ℕ),
    x ∈ TrueValues n₀ u ω →
    (∀ k' < k, (clearingBlock (d := d) (m := m) n₀ j u y).halted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k' ω) = false) →
    (clearingBlock (d := d) (m := m) n₀ j u y).halted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω) = true →
    (clearingBlock (d := d) (m := m) n₀ j u y).exit
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω) ∈ TrueValues n₀ u ω

variable {d m : ℕ}

/-! ## Query-free operations -/

/-- A record map keeping the installed values, prefixes, pending and terminal sites, and never
clearing an abort (the hypothesis of `trueValues_of_keeps`). -/
def KeepsTV (f : RunRecord d m → RunRecord d m) : Prop :=
  ∀ x, (f x).installed = x.installed ∧ (f x).prefixLength = x.prefixLength ∧
    (f x).pending = x.pending ∧ (f x).terminal = x.terminal ∧
    ((f x).aborted = false → x.aborted = false)

theorem keepsTV_id : KeepsTV (id : RunRecord d m → RunRecord d m) :=
  fun _ => ⟨rfl, rfl, rfl, rfl, id⟩

theorem keepsTV_comp {f g : RunRecord d m → RunRecord d m} (hf : KeepsTV f) (hg : KeepsTV g) :
    KeepsTV (f ∘ g) := by
  intro x
  obtain ⟨a1, a2, a3, a4, a5⟩ := hf (g x)
  obtain ⟨b1, b2, b3, b4, b5⟩ := hg x
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, fun h => b5 (a5 h)⟩

theorem keepsTV_ite (c : Prop) [Decidable c] {f g : RunRecord d m → RunRecord d m}
    (hf : KeepsTV f) (hg : KeepsTV g) : KeepsTV (if c then f else g) := by
  split_ifs
  · exact hf
  · exact hg

theorem keepsTV_guard {f : RunRecord d m → RunRecord d m} (hf : KeepsTV f) :
    KeepsTV (guardMap f) := by
  intro x
  unfold guardMap
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl, id⟩
  · exact hf x

theorem keepsTV_resetMapA (t : ℝ) : KeepsTV (resetMapA (d := d) (m := m) t) :=
  fun _ => ⟨rfl, rfl, rfl, rfl, id⟩

theorem keepsTV_endMap (P : TilePlan d m) (j : ℕ) : KeepsTV (endMap P j) :=
  keepsTV_comp (keepsTV_ite _ (fun x => keeps_snapshotMap j x) keepsTV_id)
    (fun x => keeps_sweepEndMapTheta _ x)

theorem keepsTV_stageMap (P : TilePlan d m) (j : ℕ) : KeepsTV (stageMap P j) :=
  keepsTV_comp (fun x => keeps_sweepStartMap _ _ x)
    (keepsTV_comp (keepsTV_ite _ (fun x => keeps_cutoffMap x) keepsTV_id) (keepsTV_resetMapA _))

/-! ## One block along the answers of `ω` -/

/-- **Every operation keeps `TrueValues`** along the answers of `ω`, on `RunBasics` records. -/
theorem runOp_trueValues (hTT : TileTrueValuesStatement) (hCT : ClearingTrueValuesStatement)
    (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)
    (ω : RandomSources (Torus d m) (tileOrderSize P)) (n : ℕ) (x : RunRecord d m) (k : ℕ)
    (hRB : x ∈ RunBasics P n) (hx : x ∈ TrueValues P.n₀ P.u ω)
    (hrun : ∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k' ω) =
        false)
    (hh : (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) =
        true) :
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n) x k ω) ∈
        TrueValues P.n₀ P.u ω := by
  classical
  have hB : scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)) n =
      runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n) := rfl
  rw [hB] at hrun hh ⊢
  have hsimple : ∀ f : RunRecord d m → RunRecord d m, KeepsTV f →
      runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n) =
        simpleBlock (ts₀, cl₀) f →
      (runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n)).exit
        (localState (tileOrderSize P)
          (runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n))
          x k ω) ∈ TrueValues P.n₀ P.u ω := by
    intro f hf hop
    rw [hop] at hrun ⊢
    rw [simpleBlock_exit (tileOrderSize P) (ts₀, cl₀) f x k ω hrun]
    exact trueValues_of_keeps P.n₀ P.u ω f hf x hx
  by_cases hin : P.n₀ < decodeJ d m n ∧ decodeJ d m n ≤ m + 1
  swap
  · exact hsimple id keepsTV_id (by unfold runOp; rw [if_neg hin])
  by_cases hk0 : decodeK d m n = 0
  · cases hT : tileAt P (decodeJ d m n) (decodeY d m n) with
    | none => exact hsimple id keepsTV_id (by unfold runOp; rw [if_pos hin, if_pos hk0, hT])
    | some T =>
      have hrB : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n)
          (decodeY d m n) = (tileBlock P (decodeJ d m n) T).embed (tileEmbed cl₀) tileProj := by
        unfold runOp; rw [if_pos hin, if_pos hk0, hT]
      rw [hrB] at hrun hh ⊢
      have hrun' : ∀ k' < k, (tileBlock P (decodeJ d m n) T).halted
          (localState (tileOrderSize P) (tileBlock P (decodeJ d m n) T) x k' ω) = false := by
        intro k' hk'
        have := hrun k' hk'
        rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at this
        exact this
      have hh' : (tileBlock P (decodeJ d m n) T).halted
          (localState (tileOrderSize P) (tileBlock P (decodeJ d m n) T) x k ω) = true := by
        rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at hh
        exact hh
      rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)]
      show (localState (tileOrderSize P) (tileBlock P (decodeJ d m n) T) x k ω).1 ∈ _
      cases hab : x.aborted
      · refine hTT d m P (decodeJ d m n) T (tileOrderSize P) ω x k hin.1 hin.2 ?_ hx hrun' hh'
        intro _ i hi hact hpend _
        obtain ⟨-, -, h3⟩ := hRB hab
        rw [(phaseOf_tile P n hk0 hin.1 hin.2).1] at h3
        have h3' : SweepProps P (decodeJ d m n) (siteRank d m (decodeY d m n)) x := by
          rw [rank_decodeY]; exact h3
        exact h3'.undone i hact hpend (not_processedBy_of_mem P _ _ T hT i hi)
      · have hreach := localState_reach (tileOrderSize P) _ x ω k hrun'
        rw [tile_reach_aborted P _ T x hab _ hreach]
        intro h; rw [hab] at h; cases h
  by_cases hk1 : decodeK d m n = 1
  · by_cases hy : decodeY d m n = site₀ d m
    · exact hsimple _ (keepsTV_guard (keepsTV_endMap P _))
        (by unfold runOp; rw [if_pos hin, if_neg hk0, if_pos hk1, if_pos hy])
    · exact hsimple id keepsTV_id
        (by unfold runOp; rw [if_pos hin, if_neg hk0, if_pos hk1, if_neg hy])
  by_cases hk2 : decodeK d m n = 2
  · by_cases hjc : decodeJ d m n ≤ m / 2
    · have hrB : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n)
          (decodeY d m n) =
          (clearingBlock (d := d) (m := m) P.n₀ (decodeJ d m n) P.u (decodeY d m n)).embed
            (clearEmbed ts₀) clearProj := by
        unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_pos hk2, if_pos hjc]
      rw [hrB] at hrun hh ⊢
      have hrun' : ∀ k' < k, (clearingBlock (d := d) (m := m) P.n₀ (decodeJ d m n) P.u
          (decodeY d m n)).halted (localState (tileOrderSize P) (clearingBlock (d := d) (m := m)
            P.n₀ (decodeJ d m n) P.u (decodeY d m n)) x k' ω) = false := by
        intro k' hk'
        have := hrun k' hk'
        rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at this
        exact this
      have hh' : (clearingBlock (d := d) (m := m) P.n₀ (decodeJ d m n) P.u
          (decodeY d m n)).halted (localState (tileOrderSize P) (clearingBlock (d := d) (m := m)
            P.n₀ (decodeJ d m n) P.u (decodeY d m n)) x k ω) = true := by
        rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at hh
        exact hh
      rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)]
      exact hCT d m P.n₀ (decodeJ d m n) P.u (decodeY d m n) (tileOrderSize P) ω x k hx hrun' hh'
    · exact hsimple id keepsTV_id
        (by unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_pos hk2, if_neg hjc])
  by_cases hjy : decodeJ d m n ≤ m ∧ decodeY d m n = site₀ d m
  · exact hsimple _ (keepsTV_guard (keepsTV_stageMap P _))
      (by unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_neg hk2, if_pos hjy])
  · exact hsimple id keepsTV_id
      (by unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_neg hk2, if_neg hjy])

/-! ## Along the actual run -/

/-- **`RunTrueValuesStatement` from the tile and clearing true-value disciplines and the
terminal completeness at the end.** -/
theorem runTrueValues_of_parts (hTT : TileTrueValuesStatement)
    (hCT : ClearingTrueValuesStatement) (hAT : RunAllTerminalStatement d) :
    RunTrueValuesStatement d := by
  intro m P ts₀ cl₀ E ρ lab ω hn1 hm hu hst hab i
  have hmem := blockPrestate_mem_pathwise (tileOrderSize P)
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
    (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
    (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
    (runOps_orders P ts₀ cl₀ (clrOf P.n₀ P.u)
      (fun j y M S => clearingBlock_orders P.n₀ j P.u y M S))
    (runOps_aux P ts₀ cl₀ (clrOf P.n₀ P.u) (tileOrderSize P)
      (fun j y S => clearingBlock_aux P.n₀ j P.u y _ S)) ω
    (fun n => RunBasics P n ∩ TrueValues P.n₀ P.u ω)
    (fun n x k hx hrun hh =>
      ⟨runBasics_closed' P P.n₀ P.u ts₀ cl₀ n x k ω hx.1 hrun hh,
        runOp_trueValues hTT hCT P ts₀ cl₀ ω n x k hx.1 hx.2 hrun hh⟩)
    (fun h0 => by
      rw [blockPrestate_zero (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
        _ ω h0]
      exact ⟨initialRecord_runBasics P P.n₀ P.u E ρ _ _ lab,
        initialRecord_trueValues P.n₀ P.u E ρ _ _ lab ω⟩) _ hst
  exact installed_eq_true P.n₀ P.u ω _ hmem.2 hab
    (hAT m P ts₀ cl₀ E ρ lab ω hn1 hm hu hst hab) i

/-- **The true-value closure of every block** (route R2) from the tile and clearing
true-value disciplines. -/
theorem runTVClosure_of_parts (hTT : TileTrueValuesStatement) (hCT : ClearingTrueValuesStatement) :
    RunTVClosureStatement d :=
  fun _ P ts₀ cl₀ ω n x k hRB hx hrun hh => runOp_trueValues hTT hCT P ts₀ cl₀ ω n x k hRB hx hrun hh

end AndersonAC.AgentS78
