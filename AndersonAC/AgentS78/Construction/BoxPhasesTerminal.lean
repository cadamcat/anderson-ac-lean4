import AndersonAC.AgentS78.Construction.BoxPhasesTermClear
import AndersonAC.AgentS78.Construction.BoxPhasesTrue

/-!
# Every site is terminal at the final record (agent-s78box)

`runAllTerminal_proof : RunAllTerminalStatement d`, with the index bookkeeping of
BoxPhasesCore.lean (`boxInv_closed`) for the sets

* `termTS P j r`: inactive sites are terminal; during the final sweep (`j = m + 1`) the active
  sites of processed tiles are terminal and those of unprocessed tiles are not;
* `termCL j`: inactive sites are terminal;
* `termFG`: every site is terminal;

and `RB = RunBasics P`. The final-sweep tile operation uses the terminal update of the tile block
(`TExitOK.out`, RunBasics.lean), the bit-port liveness of unprocessed tiles (`SweepProps.bit`), the
completeness of accepted trials (`tileComplete_proof`) and the empty pending set after the cutoff.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

/-- Inactive sites are terminal. -/
def ATb (x : RunRecord d m) : Prop := ∀ i, i ∉ x.endpoint.active → i ∈ x.terminal

section Sets
variable (P : TilePlan d m)

def termTS (j r : ℕ) : Set (RunRecord d m) :=
  {x | x.aborted = false → ATb x ∧ (j = m + 1 →
    (∀ i ∈ x.endpoint.active, processedBy P j r i → i ∈ x.terminal) ∧
    (∀ i ∈ x.endpoint.active, ¬ processedBy P j r i → i ∉ x.terminal))}

def termCL (_j : ℕ) : Set (RunRecord d m) := {x | x.aborted = false → ATb x}

def termFG : Set (RunRecord d m) := {x | x.aborted = false → ∀ i, i ∈ x.terminal}

end Sets

/-- The sweep facts of `RunBasics` at the tile operation `(j, 0, y)`. -/
theorem sweepProps_at_tileOp (P : TilePlan d m) (j : ℕ) (y : Torus d m) (hj : P.n₀ < j)
    (hjm : j ≤ m + 1) (x : RunRecord d m) (hx : x ∈ RunBasics P (opIndex d m j 0 y))
    (hab : x.aborted = false) : SweepProps P j (siteRank d m y) x ∧
      (cutDone P (opIndex d m j 0 y) → x.pending = ∅) := by
  obtain ⟨e1, e2, e3⟩ := decode_opIndex (d := d) (m := m) j 0 y (by norm_num)
  have hr : opIndex d m j 0 y % siteCount d m = (siteRank d m y : ℕ) := by
    rw [← rank_decodeY, e3]
  obtain ⟨-, h2, h3⟩ := hx hab
  have hph := (phaseOf_tile P (opIndex d m j 0 y) e2 (by rw [e1]; exact hj)
    (by rw [e1]; exact hjm)).1
  rw [hph, e1, hr] at h3
  exact ⟨h3, h2⟩

theorem cutDone_finalTile (P : TilePlan d m) (y : Torus d m) :
    cutDone P (opIndex d m (m + 1) 0 y) := by
  left
  rw [cutoffIndex_eq]
  unfold opIndex
  have hN := siteCount_pos d m
  have : (4 * (m / 2) + 3) * siteCount d m < (4 * (m + 1) + 0) * siteCount d m :=
    Nat.mul_lt_mul_of_pos_right (by omega) hN
  omega

section Ops
variable (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m)

theorem term_tileOp (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m + 1) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n) j 0 y (termTS P j (siteRank d m y))
      (termTS P j (siteRank d m y + 1)) := by
  classical
  intro x k ω hxRB hx hrun hh _
  cases hT : tileAt P j y with
  | none =>
    have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 0 y = simpleBlock (ts₀, cl₀) id := by
      unfold runOp; rw [if_pos ⟨hj, hjm⟩, if_pos rfl, hT]
    rw [runOp_simple_exit P ts₀ cl₀ P.n₀ P.u j 0 y id hop x k ω hrun]
    intro hab
    obtain ⟨hb, hf⟩ := hx hab
    refine ⟨hb, fun hjf => ⟨fun i hi hp => (hf hjf).1 i hi ((processedBy_succ_none P j y hT i).mp hp),
      fun i hi hp => (hf hjf).2 i hi (fun h => hp ((processedBy_succ_none P j y hT i).mpr h))⟩⟩
  | some T =>
    have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 0 y =
        (tileBlock P j T).embed (tileEmbed cl₀) tileProj := by
      unfold runOp; rw [if_pos ⟨hj, hjm⟩, if_pos rfl, hT]
    rw [hop] at hrun hh ⊢
    have hrun' : ∀ k' < k, (tileBlock P j T).halted
        (localState (tileOrderSize P) (tileBlock P j T) x k' ω) = false := by
      intro k' hk'
      have := hrun k' hk'
      rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at this
      exact this
    have hh' : (tileBlock P j T).halted
        (localState (tileOrderSize P) (tileBlock P j T) x k ω) = true := by
      rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at hh
      exact hh
    rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)]
    show (localState (tileOrderSize P) (tileBlock P j T) x k ω).1 ∈ _
    have hreach := localState_reach (tileOrderSize P) _ x ω k hrun'
    cases hab : x.aborted
    swap
    · rw [tile_reach_aborted P j T x hab _ hreach]
      intro h; rw [hab] at h; cases h
    intro hzab
    obtain ⟨hb, hf⟩ := hx hab
    obtain ⟨hSP, hcut⟩ := sweepProps_at_tileOp P j y hj hjm x hxRB hab
    have hE := (tile_reach P j T x hab _ hreach).2 hh' hzab
    set z := (localState (tileOrderSize P) (tileBlock P j T) x k ω).1 with hzdef
    have hterm_mono : ∀ i, i ∈ x.terminal → i ∈ z.terminal := by
      intro i hi
      rcases hE.out with ⟨-, -, -, ht⟩ | ⟨-, -, -, ht⟩
      · exact (ht i).mpr (Or.inl hi)
      · rw [ht]; exact hi
    refine ⟨fun i hi => hterm_mono i (hb i (by rw [← hE.ep]; exact hi)), fun hjf => ?_⟩
    subst hjf
    rcases hE.out with ⟨-, -, -, ht⟩ | ⟨hlate, -, -, -⟩
    swap
    · exact absurd (by omega : m / 2 < m + 1) hlate
    have hpend : x.pending = ∅ := hcut (cutDone_finalTile P y)
    have hcomp := tileComplete_proof d m P (m + 1) T (tileOrderSize P) x k ω
      (tileOrderSize_index P _ T) hab
      (fun i hi ha => ⟨(hf rfl).2 i ha (not_processedBy_of_mem P _ y T hT i hi),
        hSP.bit i ha (not_processedBy_of_mem P _ y T hT i hi)⟩) hrun' hh'
    refine ⟨fun i hi hp => ?_, fun i hi hp => ?_⟩
    · rw [hE.ep] at hi
      rcases (processedBy_succ P (m + 1) y T hT i).mp hp with hp' | hiT
      · exact hterm_mono i ((hf rfl).1 i hi hp')
      · have hcons : ConsCond x z i := by
          unfold ConsCond
          refine ⟨hSP.bit i hi (not_processedBy_of_mem P _ y T hT i hiT), hcomp hzab i hiT hi, ?_⟩
          rw [hpend]; exact Finset.notMem_empty i
        exact (ht i).mpr (Or.inr ⟨by unfold IsFinalSweep; omega, hcons⟩)
    · rw [hE.ep] at hi
      have hp1 : ¬ processedBy P (m + 1) (siteRank d m y) i :=
        fun h => hp ((processedBy_succ P (m + 1) y T hT i).mpr (Or.inl h))
      have hp2 : i ∉ tileSites (P.cover (m + 1)) T :=
        fun h => hp ((processedBy_succ P (m + 1) y T hT i).mpr (Or.inr h))
      intro hz
      rcases (ht i).mp hz with h | ⟨-, hc⟩
      · exact (hf rfl).2 i hi hp1 h
      · unfold ConsCond at hc
        exact hp2 (hE.erased _ hc.1 hc.2.1).1

theorem term_endOp (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m) (hy : y = site₀ d m) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n) j 1 y (termTS P j (siteCount d m))
      (termCL j) := by
  intro x k ω hxRB hx hrun _ _
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 1 y =
      simpleBlock (ts₀, cl₀) (guardMap (endMap P j)) := by
    subst hy
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩), if_neg (show (1 : ℕ) ≠ 0 by norm_num),
      if_pos (show (1 : ℕ) = 1 from rfl), if_pos (show site₀ d m = site₀ d m from rfl)]
  rw [runOp_simple_exit P ts₀ cl₀ P.n₀ P.u j 1 y _ hop x k ω hrun]
  intro hzab
  cases hab : x.aborted
  swap
  · rw [guardMap_aborted _ x hab] at hzab; rw [hab] at hzab; cases hzab
  rw [guardMap_live _ x hab]
  obtain ⟨hb, -⟩ := hx hab
  obtain ⟨e1, e2, e3⟩ := decode_opIndex (d := d) (m := m) j 1 y (by norm_num)
  have hr : opIndex d m j 1 y % siteCount d m = 0 := by
    rw [← rank_decodeY, e3, hy, rank_site₀]
  obtain ⟨-, -, h3⟩ := hxRB hab
  rw [(phaseOf_end P _ e2 hr (by rw [e1]; exact hj) (by rw [e1]; omega)).1, e1] at h3
  have h3' : SweepProps P j (siteCount d m) x := h3
  obtain ⟨hA, hTm, -, -, -⟩ := endMap_fields P j x
  have hact : (endMap P j x).endpoint.active = x.endpoint.active := by
    rw [hA]; exact sweepEndActive_eq_rb x h3'.reserve
  intro i hi
  rw [hact] at hi
  rw [hTm]; exact hb i hi

theorem term_finalEndOp (y : Torus d m) (hnm : P.n₀ ≤ m) (hy : y = site₀ d m) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n) (m + 1) 1 y
      (termTS P (m + 1) (siteCount d m)) (termFG (d := d) (m := m)) := by
  intro x k ω _ hx hrun _ _
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) (m + 1) 1 y =
      simpleBlock (ts₀, cl₀) (guardMap (endMap P (m + 1))) := by
    subst hy
    unfold runOp
    rw [if_pos (show P.n₀ < m + 1 ∧ m + 1 ≤ m + 1 from ⟨by omega, le_rfl⟩),
      if_neg (show (1 : ℕ) ≠ 0 by norm_num),
      if_pos (show (1 : ℕ) = 1 from rfl), if_pos (show site₀ d m = site₀ d m from rfl)]
  rw [runOp_simple_exit P ts₀ cl₀ P.n₀ P.u (m + 1) 1 y _ hop x k ω hrun]
  intro hzab
  cases hab : x.aborted
  swap
  · rw [guardMap_aborted _ x hab] at hzab; rw [hab] at hzab; cases hzab
  rw [guardMap_live _ x hab]
  obtain ⟨hb, hf⟩ := hx hab
  obtain ⟨-, hTm, -, -, -⟩ := endMap_fields P (m + 1) x
  intro i
  rw [hTm]
  by_cases hi : i ∈ x.endpoint.active
  · exact (hf rfl).1 i hi (processedBy_all P _ i)
  · exact hb i hi

theorem term_clearOp (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m / 2) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n) j 2 y (termCL j) (termCL j) := by
  intro x k ω _ hx hrun _ _
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 2 y =
      (clearingBlock (d := d) (m := m) P.n₀ j P.u y).embed (clearEmbed ts₀) clearProj := by
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩),
      if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_neg (show (2 : ℕ) ≠ 1 by norm_num),
      if_pos (show (2 : ℕ) = 2 from rfl), if_pos hjm]
  rw [hop] at hrun ⊢
  have hrun' : ∀ k' < k, (clearingBlock (d := d) (m := m) P.n₀ j P.u y).halted
      (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k' ω) =
        false := by
    intro k' hk'
    have := hrun k' hk'
    rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)] at this
    exact this
  rw [localState_embed (tileOrderSize P) _ _ _ (fun _ => rfl)]
  have hreach := localState_reach (tileOrderSize P) _ x ω k hrun'
  change (clearingBlock (d := d) (m := m) P.n₀ j P.u y).exit
    (localState (tileOrderSize P) (clearingBlock (d := d) (m := m) P.n₀ j P.u y) x k ω) ∈ _
  intro hzab
  have hab : x.aborted = false := by
    rw [← (clear_exit_cases P.n₀ j P.u y x _ hreach).2.1]; exact hzab
  exact clear_exit_inactive P.n₀ j P.u y x _ hreach (hx hab)

theorem term_stageOp (j : ℕ) (y : Torus d m) (hj : P.n₀ < j) (hjm : j ≤ m) (hy : y = site₀ d m) :
    OpKeeps P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n) j 3 y (termCL j) (termTS P (j + 1) 0) := by
  intro x k ω _ hx hrun _ hexRB
  have hop : runOp P ts₀ cl₀ (clrOf P.n₀ P.u) j 3 y =
      simpleBlock (ts₀, cl₀) (guardMap (stageMap P j)) := by
    subst hy
    unfold runOp
    rw [if_pos (show P.n₀ < j ∧ j ≤ m + 1 from ⟨hj, by omega⟩), if_neg (show (3 : ℕ) ≠ 0 by norm_num),
      if_neg (show (3 : ℕ) ≠ 1 by norm_num), if_neg (show (3 : ℕ) ≠ 2 by norm_num),
      if_pos (show j ≤ m ∧ site₀ d m = site₀ d m from ⟨hjm, rfl⟩)]
  rw [runOp_simple_exit P ts₀ cl₀ P.n₀ P.u j 3 y _ hop x k ω hrun] at hexRB ⊢
  intro hzab
  cases hab : x.aborted
  swap
  · rw [guardMap_aborted _ x hab] at hzab; rw [hab] at hzab; cases hzab
  rw [guardMap_live _ x hab] at hexRB hzab ⊢
  have hfa : (stageMap P j x).endpoint.active = x.endpoint.active ∧
      (stageMap P j x).terminal = x.terminal := by
    unfold stageMap
    simp only [Function.comp]
    split_ifs <;> exact ⟨rfl, rfl⟩
  refine ⟨fun i hi => ?_, fun hjf => ⟨fun i _ hp => ?_, fun i hi _ => ?_⟩⟩
  · rw [hfa.1] at hi; rw [hfa.2]; exact hx hab i hi
  · obtain ⟨S, -, hS⟩ := hp; exact absurd hS (Nat.not_lt_zero _)
  · have hle : opIndex d m j 3 y + 1 ≤ finalStart d m := by
      unfold finalStart opIndex
      rw [hy, rank_site₀]
      have hN := siteCount_pos d m
      have : (4 * j + 3) * siteCount d m + 1 ≤ (4 * (m + 1) + 0) * siteCount d m := by
        have h1 : 4 * j + 3 + 1 ≤ 4 * (m + 1) + 0 := by omega
        calc (4 * j + 3) * siteCount d m + 1 ≤ (4 * j + 3) * siteCount d m + siteCount d m := by
              omega
          _ = (4 * j + 3 + 1) * siteCount d m := by ring
          _ ≤ (4 * (m + 1) + 0) * siteCount d m := Nat.mul_le_mul_right _ h1
      omega
    exact (hexRB hzab).1 hle i hi

end Ops

/-- **`RunAllTerminalStatement` holds.** -/
theorem runAllTerminal_proof : RunAllTerminalStatement d := by
  intro m P ts₀ cl₀ E ρ lab ω hn1 hm hu hst hab
  have hnm : P.n₀ < m := by omega
  have hclosed := boxInv_closed P ts₀ cl₀ P.n₀ P.u (fun n => RunBasics P n) (termTS P)
    (fun j _ => termCL (d := d) (m := m) j) (termFG (d := d) (m := m)) hnm.le
    (fun n x k ω hx hrun hh => runBasics_closed' P P.n₀ P.u ts₀ cl₀ n x k ω hx.1 hrun hh)
    (fun j y h1 h2 => term_tileOp P ts₀ cl₀ j y h1 h2)
    (fun j y h1 h2 hy => term_endOp P ts₀ cl₀ j y h1 h2 hy)
    (fun y hy => term_finalEndOp P ts₀ cl₀ y hnm.le hy)
    (fun j y h1 h2 => if hjc : j ≤ m / 2 then term_clearOp P ts₀ cl₀ j y h1 hjc
      else opKeeps_clearId P ts₀ cl₀ P.n₀ P.u _ j y (by omega) _)
    (fun j y h1 h2 hy => term_stageOp P ts₀ cl₀ j y h1 h2 hy)
  have hmem := blockPrestate_mem_pathwise (tileOrderSize P)
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
    (initialRecord P.n₀ P.u E ρ (sweepTheta P.u m (P.n₀ + 1)) (sweepScale P.u m (P.n₀ + 1)) lab)
    (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
    (runOps_orders P ts₀ cl₀ (clrOf P.n₀ P.u)
      (fun j y M S => clearingBlock_orders P.n₀ j P.u y M S))
    (runOps_aux P ts₀ cl₀ (clrOf P.n₀ P.u) (tileOrderSize P)
      (fun j y S => clearingBlock_aux P.n₀ j P.u y _ S)) ω
    (boxInv P (fun n => RunBasics P n) (termTS P) (fun j _ => termCL (d := d) (m := m) j)
      (termFG (d := d) (m := m)))
    (fun n x k hx hrun hh => hclosed n x k ω hx hrun hh)
    (fun h0 => by
      rw [blockPrestate_zero (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf P.n₀ P.u)))
        _ ω h0]
      refine ⟨initialRecord_runBasics P P.n₀ P.u E ρ _ _ lab, ?_⟩
      rw [boxPhase_zero]
      intro _
      exact ⟨fun i hi => absurd (Finset.mem_univ i) hi, fun hj => absurd hj (by omega)⟩) _ hst
  have h2 := hmem.2
  rw [boxPhase_final P hnm.le] at h2
  exact h2 hab

end AndersonAC.AgentS78
