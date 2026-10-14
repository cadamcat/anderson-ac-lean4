import AndersonAC.AgentS78.Construction.RunOpsAbort
import AndersonAC.AgentS78.Construction.ClearingBlock
import AndersonAC.AgentS78.Construction.MarkingRule
import AndersonAC.AgentS78.Construction.SimpleDisciplines

/-!
# WP10 construction: the run-level record invariant `RunBasics`

agent-s78runinv (2026-10-14), request of agent-s78con3 (DISPATCH-REQUESTS 02:04:48 UTC).

`RunBasics P n` is a set of records indexed by the block index `n` of
`scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y))`. On non-aborted records:

1. no active site is terminal, up to the first tile slot of the final sweep (`finalStart`;
   from the final sweep's commits on, consumed active sites are terminal, TileBlock 04437d8);
2. after the cutoff (`cutoffIndex < n`, or before any operation, `decodeJ n ≤ P.n₀`) no site
   is pending;
3. a phase clause (`phaseOf`): during the tile operations of the sweep into stage `j`, with the
   tiles of anchor rank `< r` processed (`SweepProps P j r`), the reserve ports of the record's
   sweep that are live are exactly those of the active sites, the bit ports of the active sites of
   unprocessed tiles are live, and every active non-pending site has consumed exactly its digits:
   `prefixLength i = j − 1 − n₀` (unprocessed) resp. `doneLength = j − n₀` (`m − n₀` for the
   final sweep `j = m + 1`) (05:451–456, 08:11–13, 08:340–353); after the tile operations of
   stage `j` (`PostProps P j`) every active non-pending site has `doneLength`.

`runBasics_closed` is closure under every block in the `hInv` shape of `blockRun_of_runOps`
(block-local runs on the real answers of `ω`). The real answers enter only through the
completeness of accepted tile trials (`RunTileCompleteStatement`, the body of agent-s78tphase's
`TileCompleteStatement`, discharged by `tileComplete_proof` in RunBasicsInit.lean, which gives
the unconditional `runBasics_closed'`). The block kinds are isolated:
`tile_exit` (tile block), `clear_exit` (clearing block, DONE/FAIL field updates only),
`endMap_fields`, `stageWith_fields` (stage operation for any reset map keeping the fields:
`resetMap` now, `resetMapA` after the switch to `stageMapA`).

Projections in the hypothesis form of `tileSweepInv_start` (lane/agent-s78tphase 69cf872):
`runBasics_sweepStart` and `runBasics_sweepStart_pre`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-! ## The invariant -/

section Defs
variable (P : TilePlan d m)

/-- Live ports at the end of the record's sweep. -/
def liveEnd (x : RunRecord d m) : Finset (Port d m) := (x.sweep.state x.sweep.length).live

/-- Site `i` lies in a tile of sweep `j` whose anchor has rank `< r`. -/
def processedBy (j r : ℕ) (i : Torus d m) : Prop :=
  ∃ S : Fin (P.cover j).cover.count, i ∈ tileSites (P.cover j) S ∧
    (siteRank d m (tileAnchor (P.cover j) S) : ℕ) < r

/-- Consumed prefix length after the tile operations of the sweep into stage `j`. -/
def doneLength (m n₀ j : ℕ) : ℕ := if j ≤ m then j - n₀ else m - n₀

/-- The record during the tile operations of the sweep into stage `j`, tiles of anchor rank
`< r` processed. -/
structure SweepProps (j r : ℕ) (x : RunRecord d m) : Prop where
  reserve : ∀ i, ((i, true) : Port d m) ∈ liveEnd x ↔ i ∈ x.endpoint.active
  bit : ∀ i ∈ x.endpoint.active, ¬ processedBy P j r i → ((i, false) : Port d m) ∈ liveEnd x
  done : ∀ i ∈ x.endpoint.active, i ∉ x.pending → processedBy P j r i →
    x.prefixLength i = doneLength m P.n₀ j
  undone : ∀ i ∈ x.endpoint.active, i ∉ x.pending → ¬ processedBy P j r i →
    x.prefixLength i = j - 1 - P.n₀

/-- The record after the tile operations of stage `j`. -/
def PostProps (j : ℕ) (x : RunRecord d m) : Prop :=
  ∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i = doneLength m P.n₀ j

/-- Phase of a block index. -/
inductive RBPhase
  | sweep (j r : ℕ)
  | post (j : ℕ)
  | free

/-- The phase clause required at block index `n`. -/
def phaseOf (n : ℕ) : RBPhase :=
  if decodeJ d m n ≤ P.n₀ then .sweep (P.n₀ + 1) 0
  else if decodeJ d m n ≤ m + 1 then
    if decodeK d m n = 0 then .sweep (decodeJ d m n) (n % siteCount d m)
    else if decodeK d m n = 1 ∧ n % siteCount d m = 0 then
      .sweep (decodeJ d m n) (siteCount d m)
    else if decodeK d m n = 3 ∧ n % siteCount d m ≠ 0 ∧ decodeJ d m n ≤ m then
      .sweep (decodeJ d m n + 1) 0
    else .post (decodeJ d m n)
  else .free

/-- What a phase requires of a record. -/
def RBPhase.Holds : RBPhase → RunRecord d m → Prop
  | .sweep j r, x => SweepProps P j r x
  | .post j, x => PostProps P j x
  | .free, _ => True

/-- Block indices after which no site may be pending. -/
def cutDone (n : ℕ) : Prop := cutoffIndex d m < n ∨ decodeJ d m n ≤ P.n₀

/-- The first tile slot of the final residual sweep (stage `m + 1`). From the commits of the
final sweep on, consumed active sites become terminal (luna-s78tdisc, TileBlock 04437d8). -/
def finalStart (d m : ℕ) : ℕ := opIndex d m (m + 1) 0 (site₀ d m)

/-- **The run-level record invariant** at block index `n`. Clause (1) is required up to the
first tile slot of the final sweep (all sweep starts, including `j = m + 1`). -/
def RunBasics (n : ℕ) : Set (RunRecord d m) :=
  {x | x.aborted = false →
    (n ≤ finalStart d m → ∀ i ∈ x.endpoint.active, i ∉ x.terminal) ∧ (cutDone P n → x.pending = ∅) ∧
      (phaseOf P n).Holds P x}

end Defs

/-! ## Arithmetic of block indices -/

section Arith

theorem decodeJ_eq_div (n : ℕ) : decodeJ d m n = n / siteCount d m / 4 := by
  unfold decodeJ; rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem rank_decodeY (n : ℕ) : ((siteRank d m (decodeY d m n)) : ℕ) = n % siteCount d m := by
  unfold decodeY; rw [Equiv.apply_symm_apply]

theorem rank_site₀ : ((siteRank d m (site₀ d m)) : ℕ) = 0 := by
  unfold site₀; rw [Equiv.apply_symm_apply]

theorem decodeY_eq_site₀_iff (n : ℕ) : decodeY d m n = site₀ d m ↔ n % siteCount d m = 0 := by
  constructor
  · intro h; rw [← rank_decodeY, h, rank_site₀]
  · intro h
    apply (siteRank d m).injective
    apply Fin.ext
    rw [rank_decodeY, rank_site₀, h]

/-- The successor of a block index. -/
theorem decode_succ (n : ℕ) :
    (n % siteCount d m + 1 < siteCount d m ∧ decodeJ d m (n + 1) = decodeJ d m n ∧
        decodeK d m (n + 1) = decodeK d m n ∧ (n + 1) % siteCount d m = n % siteCount d m + 1) ∨
      (n % siteCount d m + 1 = siteCount d m ∧ decodeK d m n < 3 ∧
        decodeJ d m (n + 1) = decodeJ d m n ∧ decodeK d m (n + 1) = decodeK d m n + 1 ∧
        (n + 1) % siteCount d m = 0) ∨
      (n % siteCount d m + 1 = siteCount d m ∧ decodeK d m n = 3 ∧
        decodeJ d m (n + 1) = decodeJ d m n + 1 ∧ decodeK d m (n + 1) = 0 ∧
        (n + 1) % siteCount d m = 0) := by
  have hN := siteCount_pos d m
  set N := siteCount d m with hNdef
  have h1 := Nat.div_add_mod n N
  have hr := Nat.mod_lt n hN
  set q := n / N with hq
  set r := n % N with hrdef
  simp only [decodeJ_eq_div, decodeK]
  rw [← hNdef]
  by_cases hR : r + 1 < N
  · have e : n + 1 = N * q + (r + 1) := by omega
    have hdiv : (n + 1) / N = q := by
      rw [e, Nat.mul_add_div hN, Nat.div_eq_of_lt hR, add_zero]
    have hmod : (n + 1) % N = r + 1 := by
      rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hR]
    left
    exact ⟨hR, by rw [hdiv], by rw [hdiv], hmod⟩
  · have hRN : r + 1 = N := by omega
    have e : n + 1 = N * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have hdiv : (n + 1) / N = q + 1 := by rw [e, Nat.mul_div_cancel_left _ hN]
    have hmod : (n + 1) % N = 0 := by rw [e, Nat.mul_mod_right]
    rw [hdiv, hmod]
    by_cases hK : q % 4 < 3
    · right; left
      exact ⟨hRN, hK, by omega, by omega, rfl⟩
    · right; right
      exact ⟨hRN, by omega, by omega, by omega, rfl⟩

theorem cutoffIndex_eq : cutoffIndex d m = (4 * (m / 2) + 3) * siteCount d m := by
  unfold cutoffIndex opIndex; rw [rank_site₀, add_zero]

/-- Indices after the cutoff. -/
theorem lt_cutoff_cases (n : ℕ) (h : cutoffIndex d m < n) :
    m / 2 < decodeJ d m n ∨
      (decodeJ d m n = m / 2 ∧ decodeK d m n = 3 ∧ n % siteCount d m ≠ 0) := by
  have hN := siteCount_pos d m
  rw [cutoffIndex_eq] at h
  have h1 := Nat.div_add_mod n (siteCount d m)
  have hq : 4 * (m / 2) + 3 ≤ n / siteCount d m := by
    have := Nat.div_le_div_right (c := siteCount d m) h.le
    rwa [Nat.mul_div_cancel _ hN] at this
  simp only [decodeJ_eq_div, decodeK]
  by_cases hJ : m / 2 < n / siteCount d m / 4
  · exact Or.inl hJ
  · right
    have hq' : n / siteCount d m = 4 * (m / 2) + 3 := by omega
    refine ⟨by omega, by omega, fun h0 => ?_⟩
    rw [hq', h0, add_zero] at h1
    rw [Nat.mul_comm] at h1
    omega

theorem decodeJ_mono {n n' : ℕ} (h : n ≤ n') : decodeJ d m n ≤ decodeJ d m n' := by
  unfold decodeJ; exact Nat.div_le_div_right h

theorem cutDone_succ (P : TilePlan d m) (n : ℕ) (h : cutDone P (n + 1)) :
    cutDone P n ∨ (n = cutoffIndex d m ∧ P.n₀ < m / 2) := by
  rcases h with h | h
  · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inl (Or.inl h)
    · by_cases hn : P.n₀ < m / 2
      · exact Or.inr ⟨h.symm, hn⟩
      · left; right
        have := (decode_opIndex (d := d) (m := m) (m / 2) 3 (site₀ d m) (by norm_num)).1
        rw [show cutoffIndex d m = opIndex d m (m / 2) 3 (site₀ d m) from rfl] at h
        rw [← h, this]; omega
  · exact Or.inl (Or.inr (le_trans (decodeJ_mono (Nat.le_succ n)) h))

theorem finalStart_eq : finalStart d m = (m + 1) * (4 * siteCount d m) := by
  unfold finalStart opIndex; rw [rank_site₀]; ring

theorem lt_finalStart_iff (n : ℕ) : n < finalStart d m ↔ decodeJ d m n ≤ m := by
  rw [finalStart_eq]
  unfold decodeJ
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by have := siteCount_pos d m; omega)]

end Arith


/-! ## Tiles: anchors and processed sites -/

section Tiles
variable (P : TilePlan d m)

theorem siteAt_mem_rb (S : Finset (Torus d m)) {v : ℕ} {i : Torus d m}
    (h : siteAt S v = some i) : i ∈ S := by
  unfold siteAt at h
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  rcases hv : L[v]? with _ | a
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Option.map_some, Option.some.injEq] at h
  obtain ⟨hvl, hva⟩ := List.getElem?_eq_some_iff.mp hv
  have hmem : L[v] ∈ S.map (siteRank d m).toEmbedding :=
    (Finset.mem_sort _).mp (List.getElem_mem hvl)
  rw [hva] at hmem
  obtain ⟨b, hb, hbe⟩ := Finset.mem_map.mp hmem
  rw [← h, ← hbe]; simpa using hb

theorem siteAt_zero_rb (S : Finset (Torus d m)) (hS : S.Nonempty) :
    ∃ i, siteAt S 0 = some i := by
  unfold siteAt
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hlen : L.length = S.card := by rw [hL, Finset.length_sort, Finset.card_map]
  have hv' : 0 < L.length := hlen ▸ Finset.card_pos.mpr hS
  rw [List.getElem?_eq_getElem hv']
  exact ⟨_, rfl⟩

theorem tileAnchor_mem_rb {t : ℝ} (C : StageCover d m t) (T : Fin C.cover.count)
    (h : (tileSites C T).Nonempty) : tileAnchor C T ∈ tileSites C T := by
  obtain ⟨i, hs⟩ := siteAt_zero_rb (tileSites C T) h
  unfold tileAnchor
  rw [hs]
  exact siteAt_mem_rb _ hs

theorem mem_tileSites_iff {t : ℝ} (C : StageCover d m t) (T : Fin C.cover.count)
    (i : Torus d m) : i ∈ tileSites C T ↔ ((i, false) : Port d m) ∈ C.cover.tile T := by
  classical
  unfold tileSites
  simp

/-- A site lies in one tile only. -/
theorem tile_unique_rb {t : ℝ} (C : StageCover d m t) {S S' : Fin C.cover.count} {i : Torus d m}
    (h : i ∈ tileSites C S) (h' : i ∈ tileSites C S') : S = S' := by
  rw [mem_tileSites_iff] at h h'
  obtain ⟨T, -, hT⟩ := C.cover.cover ((i, false) : Port d m)
  exact (hT S h).trans (hT S' h').symm

theorem tileAt_spec (j : ℕ) (y : Torus d m) (T : Fin (P.cover j).cover.count)
    (h : tileAt P j y = some T) :
    (tileSites (P.cover j) T).Nonempty ∧ tileAnchor (P.cover j) T = y := by
  classical
  unfold tileAt at h
  split_ifs at h with hex
  cases h
  exact Classical.choose_spec hex

/-- A nonempty tile anchored at `y` is the tile of `tileAt`. -/
theorem tile_eq_tileAt (j : ℕ) (y : Torus d m) (T S : Fin (P.cover j).cover.count)
    (h : tileAt P j y = some T) (hS : (tileSites (P.cover j) S).Nonempty)
    (hy : tileAnchor (P.cover j) S = y) : S = T := by
  obtain ⟨hT, hTy⟩ := tileAt_spec P j y T h
  have h1 := tileAnchor_mem_rb (P.cover j) S hS
  have h2 := tileAnchor_mem_rb (P.cover j) T hT
  rw [hy] at h1; rw [hTy] at h2
  exact tile_unique_rb (P.cover j) h1 h2

theorem tileAt_none (j : ℕ) (y : Torus d m) (h : tileAt P j y = none)
    (S : Fin (P.cover j).cover.count) (hS : (tileSites (P.cover j) S).Nonempty) :
    tileAnchor (P.cover j) S ≠ y := by
  classical
  intro hy
  unfold tileAt at h
  rw [dite_cond_eq_true (eq_true ⟨S, hS, hy⟩)] at h
  cases h

theorem rank_eq_iff (a b : Torus d m) :
    ((siteRank d m a : ℕ) = siteRank d m b) ↔ a = b := by
  constructor
  · intro h; exact (siteRank d m).injective (Fin.ext h)
  · intro h; rw [h]

theorem processedBy_mono {j r r' : ℕ} (h : r ≤ r') {i : Torus d m} (hp : processedBy P j r i) :
    processedBy P j r' i := by
  obtain ⟨S, hS, hr⟩ := hp
  exact ⟨S, hS, lt_of_lt_of_le hr h⟩

/-- Processing the tile at `y`. -/
theorem processedBy_succ (j : ℕ) (y : Torus d m) (T : Fin (P.cover j).cover.count)
    (h : tileAt P j y = some T) (i : Torus d m) :
    processedBy P j ((siteRank d m y : ℕ) + 1) i ↔
      processedBy P j (siteRank d m y) i ∨ i ∈ tileSites (P.cover j) T := by
  constructor
  · rintro ⟨S, hS, hr⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
    · exact Or.inl ⟨S, hS, hr⟩
    · right
      have hy : tileAnchor (P.cover j) S = y := (rank_eq_iff _ _).mp hr
      rw [← tile_eq_tileAt P j y T S h ⟨i, hS⟩ hy]; exact hS
  · rintro (hp | hi)
    · exact processedBy_mono P (Nat.le_succ _) hp
    · refine ⟨T, hi, ?_⟩
      rw [(tileAt_spec P j y T h).2]; exact Nat.lt_succ_self _

theorem not_processedBy_of_mem (j : ℕ) (y : Torus d m) (T : Fin (P.cover j).cover.count)
    (h : tileAt P j y = some T) (i : Torus d m) (hi : i ∈ tileSites (P.cover j) T) :
    ¬ processedBy P j (siteRank d m y) i := by
  rintro ⟨S, hS, hr⟩
  have := tile_unique_rb (P.cover j) hS hi
  subst this
  rw [(tileAt_spec P j y S h).2] at hr
  exact lt_irrefl _ hr

theorem processedBy_succ_none (j : ℕ) (y : Torus d m) (h : tileAt P j y = none)
    (i : Torus d m) :
    processedBy P j ((siteRank d m y : ℕ) + 1) i ↔ processedBy P j (siteRank d m y) i := by
  constructor
  · rintro ⟨S, hS, hr⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
    · exact ⟨S, hS, hr⟩
    · exact absurd ((rank_eq_iff _ _).mp hr) (tileAt_none P j y h S ⟨i, hS⟩)
  · exact processedBy_mono P (Nat.le_succ _)

theorem processedBy_all (j : ℕ) (i : Torus d m) : processedBy P j (siteCount d m) i := by
  obtain ⟨S, hS, -⟩ := (P.cover j).cover.cover ((i, false) : Port d m)
  exact ⟨S, (mem_tileSites_iff _ _ _).mpr hS, (siteRank d m _).isLt⟩

end Tiles

/-! ## The tile block: reachable states (any answers) -/

section TileReach
variable (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (x : RunRecord d m)

/-- Live ports at the end of the scratch prefix. -/
def liveNow (s : RunRecord d m × TileScratch d m) : Finset (Port d m) :=
  (s.2.seq.state s.2.seq.length).live

/-- Invariant of running states of the tile block entered with `x`. -/
structure TRun (s : RunRecord d m × TileScratch d m) : Prop where
  ep : s.1.endpoint = x.endpoint
  term : s.1.terminal = x.terminal
  pref : s.1.prefixLength = x.prefixLength
  sw : s.1.sweep = x.sweep
  ab : s.1.aborted = false
  pend0 : s.2.attempt = 0 → s.1.pending = x.pending
  pend1 : s.2.attempt ≠ 0 →
    s.1.pending = x.pending ∪ (TS P j T ∩ x.endpoint.active) ∧ ¬ m / 2 < j
  sub : liveNow s ⊆ liveEnd x
  erased : ∀ p ∈ liveEnd x, p ∉ liveNow s → p.1 ∈ TS P j T ∧ p.2 = false
  cons0 : s.2.attempt = 0 → ∀ i, (s.2.consumed i = true ↔
    (((i, false) : Port d m) ∈ liveEnd x ∧ ((i, false) : Port d m) ∉ liveNow s ∧
      i ∉ x.pending))
  cons1 : s.2.attempt ≠ 0 → ∀ i, s.2.consumed i = false
  site : ∀ i, s.2.site = some i → i ∈ TS P j T ∧ ((i, false) : Port d m) ∈ liveNow s
  inst : s.1.installed = x.installed
  ff0 : s.2.attempt = 0 → s.2.firstFail = false

/-- Consumption of the true input at `i` by an accepted first trial (a digit off the final
sweep, the whole suffix at the final sweep, where the site becomes terminal). -/
def ConsCond (x y : RunRecord d m) (i : Torus d m) : Prop :=
  ((i, false) : Port d m) ∈ liveEnd x ∧ ((i, false) : Port d m) ∉ liveEnd y ∧
    i ∉ x.pending

/-- The non-aborted exit of the tile block entered with `x`. -/
structure TExitOK (y : RunRecord d m) : Prop where
  ep : y.endpoint = x.endpoint
  sub : liveEnd y ⊆ liveEnd x
  erased : ∀ p ∈ liveEnd x, p ∉ liveEnd y → p.1 ∈ TS P j T ∧ p.2 = false
  out : (y.pending = x.pending ∧
      (∀ i, ConsCond x y i → ¬ IsFinalSweep m j → y.prefixLength i = x.prefixLength i + 1) ∧
      (∀ i, (¬ ConsCond x y i ∨ IsFinalSweep m j) → y.prefixLength i = x.prefixLength i) ∧
      (∀ i, i ∈ y.terminal ↔ i ∈ x.terminal ∨ (IsFinalSweep m j ∧ ConsCond x y i))) ∨
    (¬ m / 2 < j ∧ y.pending = x.pending ∪ (TS P j T ∩ x.endpoint.active) ∧
      y.prefixLength = x.prefixLength ∧ y.terminal = x.terminal)

/-- Off the final sweep the tile block keeps the terminal set. -/
theorem TExitOK.term_off {y : RunRecord d m} (h : TExitOK P j T x y)
    (hf : ¬ IsFinalSweep m j) : y.terminal = x.terminal := by
  rcases h.out with ⟨-, -, -, ht⟩ | ⟨-, -, -, ht⟩
  · ext i; rw [ht i]; exact ⟨fun h' => h'.elim id (fun h'' => absurd h''.1 hf), Or.inl⟩
  · exact ht

/-- Reachable-state claim. -/
def TClaim (s : RunRecord d m × TileScratch d m) : Prop :=
  (s.2.halted = false → TRun P j T x s) ∧
    (s.2.halted = true → s.1.aborted = false → TExitOK P j T x s.1)

theorem trun_log (s : RunRecord d m × TileScratch d m) (q : Query (Torus d m))
    (h : TRun P j T x s) : TRun P j T x (s.1, logQuery q s.2) :=
  { ep := h.ep, term := h.term, pref := h.pref, sw := h.sw, ab := h.ab, pend0 := h.pend0,
    pend1 := h.pend1, sub := h.sub, erased := h.erased, cons0 := h.cons0, cons1 := h.cons1,
    site := h.site, inst := h.inst, ff0 := h.ff0 }

theorem liveNow_scalar (s : RunRecord d m × TileScratch d m) (t : ℝ) (r : Port d m → ℂ)
    (p : Port d m) (ξ : ℝ) (sc : TileScratch d m)
    (hsc : sc.seq = extendSeq s.2.seq (stepLive t r (s.2.seq.state s.2.seq.length) p ξ) p ξ) :
    liveNow (s.1, sc) = (liveNow s).erase p := by
  simp [liveNow, hsc, extendSeq, stepLive]

/-- A failed trial keeps the claim. -/
theorem tclaim_fail (s : RunRecord d m × TileScratch d m) (hrun : s.2.halted = false)
    (h : TRun P j T x s) : TClaim P j T x (failTrial P j T s) := by
  classical
  unfold failTrial
  dsimp only
  by_cases hlate : m / 2 < j
  · simp only [hlate, if_true]
    refine ⟨fun hh => by simp at hh, fun _ hab => by simp at hab⟩
  · simp only [hlate, if_false]
    set x' := (if s.2.attempt = 0 then
      markTile (TS P j T) ⟨j, BirthType.tile, tileAnchor (P.cover j) T⟩ s.1 else s.1) with hx'
    have hx'f : x'.endpoint = s.1.endpoint ∧ x'.terminal = s.1.terminal ∧
        x'.prefixLength = s.1.prefixLength ∧ x'.sweep = s.1.sweep ∧ x'.aborted = s.1.aborted ∧
        x'.installed = s.1.installed := by
      rw [hx']; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hx'p : x'.pending = x.pending ∪ (TS P j T ∩ x.endpoint.active) := by
      rw [hx']
      split_ifs with h0
      · simp only [markTile]; rw [h.pend0 h0, h.ep]
      · exact (h.pend1 h0).1
    refine ⟨fun _ => ?_, fun hh => by simp [trialScratch, hrun] at hh⟩
    have hlive : liveNow (x', { trialScratch x' s.2 (s.2.attempt + 1) with firstFail := true }) =
        liveEnd x := by
      simp only [liveNow, trialScratch, liveEnd]; rw [hx'f.2.2.2.1, h.sw]
    refine
      { ep := hx'f.1.trans h.ep, term := hx'f.2.1.trans h.term,
        pref := hx'f.2.2.1.trans h.pref, sw := hx'f.2.2.2.1.trans h.sw,
        ab := hx'f.2.2.2.2.1.trans h.ab, pend0 := fun h0 => by simp [trialScratch] at h0,
        pend1 := fun _ => ⟨hx'p, hlate⟩, sub := by rw [hlive],
        erased := fun p hp hn => by rw [hlive] at hn; exact absurd hp hn,
        cons0 := fun h0 => by simp [trialScratch] at h0,
        cons1 := fun _ i => by simp [trialScratch],
        site := fun i hi => by simp [trialScratch] at hi,
        inst := hx'f.2.2.2.2.2.trans h.inst, ff0 := fun h0 => by simp [trialScratch] at h0 }

open Classical in
theorem trun_scalar_ok (s : RunRecord d m × TileScratch d m) (h : TRun P j T x s)
    (i : Torus d m) (hsite : s.2.site = some i) (sc : TileScratch d m)
    (hl : liveNow (s.1, sc) = (liveNow s).erase ((i, false) : Port d m))
    (hatt : sc.attempt = s.2.attempt) (hsite' : sc.site = none) (hff : sc.firstFail = s.2.firstFail)
    (hcons : sc.consumed = Function.update s.2.consumed i
      (decide (usesTrue s i))) :
    TRun P j T x (s.1, sc) := by
  classical
  obtain ⟨hiT, hil⟩ := h.site i hsite
  refine
    { ep := h.ep, term := h.term, pref := h.pref, sw := h.sw, ab := h.ab,
      pend0 := fun h0 => h.pend0 (by rw [← hatt]; exact h0),
      pend1 := fun h0 => h.pend1 (by rw [← hatt]; exact h0), inst := h.inst,
      ff0 := fun h0 => by rw [hff]; exact h.ff0 (by rw [← hatt]; exact h0),
      sub := ?_, erased := ?_, cons0 := ?_, cons1 := ?_, site := ?_ }
  · rw [hl]; exact (Finset.erase_subset _ _).trans h.sub
  · intro p hp hn
    rw [hl] at hn
    by_cases hpi : p = ((i, false) : Port d m)
    · subst hpi; exact ⟨hiT, rfl⟩
    · exact h.erased p hp (fun hm => hn (Finset.mem_erase.mpr ⟨hpi, hm⟩))
  · intro h0 i'
    have h0' : s.2.attempt = 0 := by rw [← hatt]; exact h0
    show sc.consumed i' = true ↔ _
    rw [hcons, hl]
    by_cases hii : i' = i
    · subst hii
      rw [Function.update_self, decide_eq_true_iff]
      constructor
      · intro hd
        exact ⟨h.sub hil, fun hm => (Finset.mem_erase.mp hm).1 rfl,
          by rw [← h.pend0 h0']; exact hd.2⟩
      · rintro ⟨-, -, hp⟩
        exact ⟨h0', by rw [h.pend0 h0']; exact hp⟩
    · rw [Function.update_of_ne hii, h.cons0 h0' i']
      have hne : ((i', false) : Port d m) ≠ ((i, false) : Port d m) := by
        intro he; exact hii (Prod.ext_iff.mp he).1
      have key : ((i', false) : Port d m) ∈ (liveNow s).erase ((i, false) : Port d m) ↔
          ((i', false) : Port d m) ∈ liveNow s :=
        ⟨fun hm => (Finset.mem_erase.mp hm).2, fun hm => Finset.mem_erase.mpr ⟨hne, hm⟩⟩
      rw [key]
  · intro h0 i'
    have h0' : s.2.attempt ≠ 0 := by rw [← hatt]; exact h0
    show sc.consumed i' = false
    rw [hcons]
    by_cases hii : i' = i
    · subst hii
      rw [Function.update_self, decide_eq_false_iff_not]
      exact fun hu => h0' hu.1
    · rw [Function.update_of_ne hii]; exact h.cons1 h0' i'
  · intro i' hi'; rw [hsite'] at hi'; cases hi'

/-- A scalar slot keeps the claim. -/
theorem tclaim_scalar (s : RunRecord d m × TileScratch d m) (hrun : s.2.halted = false)
    (h : TRun P j T x s) (i : Torus d m) (hsite : s.2.site = some i) (ζ : ℝ) :
    TClaim P j T x (scalarStep P j T s i ζ) := by
  classical
  unfold scalarStep
  dsimp only
  split_ifs with hok
  · refine ⟨fun _ => trun_scalar_ok P j T x s h i hsite _
      (by simp [liveNow, extendSeq, stepLive]) rfl rfl rfl rfl, fun hh => by simp [hrun] at hh⟩
  · exact tclaim_fail P j T x s hrun h

theorem exposedSite_spec (s : RunRecord d m × TileScratch d m) (v : Option ℕ) (i : Torus d m)
    (h : exposedSite P j T s v = some i) :
    i ∈ TS P j T ∧ ((i, false) : Port d m) ∈ (s.2.seq.state s.2.seq.length).live := by
  classical
  unfold exposedSite at h
  rcases v with _ | v
  · cases h
  · simp only at h
    rcases hs : siteAt (TS P j T) v with _ | i'
    · rw [hs] at h; cases h
    · rw [hs] at h
      simp only at h
      split_ifs at h with hc
      cases h
      exact ⟨siteAt_mem_rb _ hs, hc.2⟩

/-- One step of the running block keeps the claim. -/
theorem tclaim_step (s : RunRecord d m × TileScratch d m) (hrun : s.2.halted = false)
    (h : TRun P j T x s) (a : Answer (Torus d m)) :
    TClaim P j T x ((tileBlock P j T).update s a) := by
  classical
  rw [tileBlock_update_running P j T s a hrun]
  have h0 := trun_log P j T x s (tileQuery P j T s) h
  generalize tileQuery P j T s = q at h0 ⊢
  have hrun0 : (logQuery q s.2).halted = false := hrun
  have hs0 : (logQuery q s.2).site = s.2.site := rfl
  have hscal : ∀ ζ : ℝ, TClaim P j T x (match (logQuery q s.2).site with
      | none => (s.1, logQuery q s.2)
      | some i => scalarStep P j T (s.1, logQuery q s.2) i ζ) := by
    intro ζ
    rcases hsite : (logQuery q s.2).site with _ | i
    · exact ⟨fun _ => h0, fun hh => by simp [hrun0] at hh⟩
    · exact tclaim_scalar P j T x (s.1, logQuery q s.2) hrun0 h0 i hsite ζ
  rcases q with ⟨i, hh⟩ | k | ⟨i, hh⟩ | o | _
  · exact hscal _
  · exact hscal _
  · exact hscal _
  · refine ⟨fun _ => ?_, fun hh => by simp [tileStep, hrun0] at hh⟩
    refine { h0 with site := ?_ }
    intro i hi
    exact exposedSite_spec P j T (s.1, logQuery (Query.nextOrder o) s.2) a.2 i hi
  · simp only [tileStep]
    rcases hsite : (logQuery Query.decision s.2).site with _ | i
    · refine ⟨fun hh => by simp at hh, fun _ hab => ?_⟩
      set sc := logQuery Query.decision s.2 with hsc
      have hl : liveEnd (commitTrial s.1 sc (decide (IsFinalSweep m j))) =
          liveNow (s.1, sc) := rfl
      refine ⟨h0.ep, ?_, ?_, ?_⟩
      · rw [hl]; exact h0.sub
      · rw [hl]; exact h0.erased
      have hp : s.1.prefixLength = x.prefixLength := h0.pref
      have ht : s.1.terminal = x.terminal := h0.term
      by_cases hat : sc.attempt = 0
      · left
        have hcc : ∀ i, sc.consumed i = true ↔
            ConsCond x (commitTrial s.1 sc (decide (IsFinalSweep m j))) i := by
          intro i; rw [h0.cons0 hat i]; unfold ConsCond; rw [hl]
        refine ⟨h0.pend0 hat, fun i hc hf => ?_, fun i hc => ?_, fun i => ?_⟩
        · have h1 : sc.consumed i = true := (hcc i).mpr hc
          simp [commitTrial, h1, hp, hf]
        · by_cases hf : IsFinalSweep m j
          · simp [commitTrial, hp, hf]
          · have h1 : sc.consumed i = false := by
              rcases hc with hc | hc
              · by_contra hne; exact hc ((hcc i).mp (by simpa using hne))
              · exact absurd hc hf
            simp [commitTrial, h1, hp]
        · rw [← hcc i]
          by_cases hf : IsFinalSweep m j
          · simp [commitTrial, ht, hf]
          · simp [commitTrial, ht, hf]
      · right
        have hc1 : ∀ i, sc.consumed i = false := h0.cons1 hat
        refine ⟨(h0.pend1 hat).2, (h0.pend1 hat).1, ?_, ?_⟩
        · funext i; simp [commitTrial, hc1, hp]
        · simp [commitTrial, hc1, ht]
    · exact ⟨fun _ => { h0 with site := fun i' hi' => by simp at hi' },
        fun hh => by simp [hrun0] at hh⟩

/-- **Reachable states of the tile block** entered with a non-aborted record. -/
theorem tile_reach (hab : x.aborted = false) (s : RunRecord d m × TileScratch d m)
    (hs : BlockReach (tileBlock P j T) x s) : TClaim P j T x s := by
  classical
  induction hs with
  | enter =>
    have he : (tileBlock P j T).enter x = (x, initScratch x) := by simp [tileBlock, hab]
    rw [he]
    refine ⟨fun _ => ?_, fun hh => by simp [initScratch] at hh⟩
    have hl : liveNow (x, initScratch x) = liveEnd x := rfl
    exact
      { ep := rfl, term := rfl, pref := rfl, sw := rfl, ab := hab, pend0 := fun _ => rfl,
        pend1 := fun h0 => absurd rfl h0, sub := by rw [hl], inst := rfl, ff0 := fun _ => rfl,
        erased := fun p hp hn => by rw [hl] at hn; exact absurd hp hn,
        cons0 := fun _ i => by
          rw [hl]; simp only [initScratch, Bool.false_eq_true, false_iff, not_and, not_not]
          intro h1 h2; exact absurd h1 h2,
        cons1 := fun _ _ => rfl, site := fun i hi => by simp [initScratch] at hi }
  | step s a _ hnh ih => exact tclaim_step P j T x s hnh (ih.1 hnh) a

end TileReach

/-! ## Record-level transfer of the phase clauses -/

section Transfer
variable (P : TilePlan d m)

/-- **Tile block, record level.** The non-aborted exit of the tile `T = tileAt P J y` keeps
`SweepProps`, one more anchor rank processed, given completeness of the accepted trial off the
final sweep. -/
theorem sweepProps_tile (J : ℕ) (y : Torus d m) (T : Fin (P.cover J).cover.count)
    (hT : tileAt P J y = some T) (hJ1 : P.n₀ < J) (hJ2 : J ≤ m + 1) (x z : RunRecord d m)
    (hx : SweepProps P J (siteRank d m y) x) (hE : TExitOK P J T x z)
    (hcomp : ¬ IsFinalSweep m J →
      ∀ i ∈ TS P J T, i ∈ x.endpoint.active → ((i, false) : Port d m) ∉ liveEnd z) :
    SweepProps P J ((siteRank d m y : ℕ) + 1) z := by
  classical
  have hact : z.endpoint.active = x.endpoint.active := by rw [hE.ep]
  have hsucc := processedBy_succ P J y T hT
  have hnot := not_processedBy_of_mem P J y T hT
  have hdl : doneLength m P.n₀ J = (if IsFinalSweep m J then J - 1 - P.n₀ else J - 1 - P.n₀ + 1) := by
    unfold doneLength
    by_cases h : J ≤ m
    · rw [if_pos h, if_neg (show ¬ IsFinalSweep m J by unfold IsFinalSweep; omega)]; omega
    · rw [if_neg h, if_pos (show IsFinalSweep m J by unfold IsFinalSweep; omega)]; omega
  refine ⟨fun i => ?_, fun i hi hp => ?_, fun i hi hpend hp => ?_, fun i hi hpend hp => ?_⟩
  · rw [hact]
    constructor
    · intro hl; exact (hx.reserve i).mp (hE.sub hl)
    · intro ha
      by_contra hl
      have := (hE.erased _ ((hx.reserve i).mpr ha) hl).2
      exact Bool.noConfusion this
  · rw [hact] at hi
    have hp' : ¬ processedBy P J (siteRank d m y) i := fun h' => hp ((hsucc i).mpr (Or.inl h'))
    have hiT : i ∉ TS P J T := fun h' => hp ((hsucc i).mpr (Or.inr h'))
    by_contra hl
    exact hiT (hE.erased _ (hx.bit i hi hp') hl).1
  · rw [hact] at hi
    rcases hE.out with ⟨hpe, hp1, hp0, -⟩ | ⟨hlate, hpe, hpre, -⟩
    · rw [hpe] at hpend
      by_cases hiT : i ∈ TS P J T
      · have hu := hx.undone i hi hpend (hnot i hiT)
        rw [hdl]
        by_cases hf : IsFinalSweep m J
        · rw [if_pos hf, hp0 i (Or.inr hf), hu]
        · rw [if_neg hf, hp1 i ⟨hx.bit i hi (hnot i hiT), hcomp hf i hiT hi, hpend⟩ hf, hu]
      · have hp' : processedBy P J (siteRank d m y) i := by
          rcases (hsucc i).mp hp with h' | h'
          · exact h'
          · exact absurd h' hiT
        have hnc : ¬ ConsCond x z i := fun h' => hiT (hE.erased _ h'.1 h'.2.1).1
        rw [hp0 i (Or.inl hnc)]; exact hx.done i hi hpend hp'
    · rw [hpe] at hpend
      have hiT : i ∉ TS P J T := fun h' => hpend (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨h', hi⟩))
      have hpend' : i ∉ x.pending := fun h' => hpend (Finset.mem_union_left _ h')
      have hp' : processedBy P J (siteRank d m y) i := by
        rcases (hsucc i).mp hp with h' | h'
        · exact h'
        · exact absurd h' hiT
      rw [hpre]; exact hx.done i hi hpend' hp'
  · rw [hact] at hi
    have hp' : ¬ processedBy P J (siteRank d m y) i := fun h' => hp ((hsucc i).mpr (Or.inl h'))
    have hiT : i ∉ TS P J T := fun h' => hp ((hsucc i).mpr (Or.inr h'))
    rcases hE.out with ⟨hpe, -, hp0, -⟩ | ⟨hlate, hpe, hpre, -⟩
    · rw [hpe] at hpend
      have hnc : ¬ ConsCond x z i := fun h' => hiT (hE.erased _ h'.1 h'.2.1).1
      rw [hp0 i (Or.inl hnc)]; exact hx.undone i hi hpend hp'
    · rw [hpe] at hpend
      have hpend' : i ∉ x.pending := fun h' => hpend (Finset.mem_union_left _ h')
      rw [hpre]; exact hx.undone i hi hpend' hp'

/-- An empty tile slot (no tile anchored at `y`). -/
theorem sweepProps_tileNone (J : ℕ) (y : Torus d m) (hT : tileAt P J y = none)
    (x : RunRecord d m) (hx : SweepProps P J (siteRank d m y) x) :
    SweepProps P J ((siteRank d m y : ℕ) + 1) x := by
  have h := processedBy_succ_none P J y hT
  exact ⟨hx.reserve, fun i hi hp => hx.bit i hi (fun h' => hp ((h i).mpr h')),
    fun i hi hpend hp => hx.done i hi hpend ((h i).mp hp),
    fun i hi hpend hp => hx.undone i hi hpend (fun h' => hp ((h i).mpr h'))⟩

/-- All tiles processed. -/
theorem postProps_of_all (J : ℕ) (x : RunRecord d m) (hx : SweepProps P J (siteCount d m) x) :
    PostProps P J x :=
  fun i hi hpend => hx.done i hi hpend (processedBy_all P J i)

/-- The reserve ports live at the sweep end are the active sites. -/
theorem sweepEndActive_eq_rb (x : RunRecord d m)
    (h : ∀ i, ((i, true) : Port d m) ∈ liveEnd x ↔ i ∈ x.endpoint.active) :
    sweepEndActive x = x.endpoint.active := by
  classical
  ext i
  unfold sweepEndActive
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h i

/-- **Sweep end (with snapshot at a clearing stage), field level.** -/
theorem endMap_fields (j : ℕ) (x : RunRecord d m) :
    (endMap P j x).endpoint.active = sweepEndActive x ∧ (endMap P j x).terminal = x.terminal ∧
      (endMap P j x).pending = x.pending ∧ (endMap P j x).prefixLength = x.prefixLength ∧
      (endMap P j x).aborted = x.aborted := by
  unfold endMap
  simp only [Function.comp]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Maps keeping the fields of `RunBasics` (the reset maps). -/
def KeepsBasics (f : RunRecord d m → RunRecord d m) : Prop :=
  ∀ x, (f x).endpoint.active = x.endpoint.active ∧ (f x).terminal = x.terminal ∧
    (f x).pending = x.pending ∧ (f x).prefixLength = x.prefixLength ∧
    (f x).aborted = x.aborted

theorem resetMap_keepsBasics (t : ℝ) : KeepsBasics (resetMap (d := d) (m := m) t) :=
  fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The active-block reset of agent-s78phase (used by `stageMap` since lane/agent-s78 f7d1952). -/
theorem resetMapA_keepsBasics (t : ℝ) : KeepsBasics (resetMapA (d := d) (m := m) t) := by
  intro x
  obtain ⟨-, -, -, hpre, hterm, hpend, -, -, hab, hact⟩ := resetMapA_preserves t x
  exact ⟨hact, hterm, hpend, hpre, hab⟩

/-- **Stage operation (reset `f`, cutoff if `c`, stage-start lift), field level.** -/
theorem stageWith_fields (f : RunRecord d m → RunRecord d m) (hf : KeepsBasics f)
    (θ t : ℝ) (c : Prop) [Decidable c] (x : RunRecord d m) :
    let y := sweepStartMap θ t ((if c then cutoffMap else id) (f x))
    y.endpoint.active = x.endpoint.active ∧ y.terminal = x.terminal ∧ y.pending = x.pending ∧
      y.prefixLength = x.prefixLength ∧
      (y.aborted = false → x.aborted = false ∧ (c → x.pending = ∅)) ∧
      (∀ p : Port d m, p ∈ liveEnd y ↔ p.1 ∈ x.endpoint.active) := by
  intro y
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf x
  have hlive : ∀ p : Port d m, p ∈ liveEnd y ↔ p.1 ∈ ((if c then cutoffMap else id) (f x)).endpoint.active := by
    intro p
    simp [y, liveEnd, sweepStartMap, sweepStartLiveState]
  by_cases hc : c
  · simp only [y, hc, if_true] at hlive ⊢
    refine ⟨h1, h2, h3, h4, fun hab => ?_, fun p => by rw [hlive]; exact h1 ▸ Iff.rfl⟩
    simp only [sweepStartMap, cutoffMap, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hab
    rw [h5] at hab
    refine ⟨hab.1, fun _ => ?_⟩
    rw [← h3]; exact Finset.card_eq_zero.mp hab.2
  · simp only [y, hc, if_false, id] at hlive ⊢
    refine ⟨h1, h2, h3, h4, fun hab => ⟨?_, fun h' => h'.elim⟩,
      fun p => by rw [hlive]; exact h1 ▸ Iff.rfl⟩
    simpa [sweepStartMap, h5] using hab

/-- The stage-start lift gives the sweep clauses with nothing processed. -/
theorem sweepProps_stage (J : ℕ) (hJ : J ≤ m) (x y : RunRecord d m) (hx : PostProps P J x)
    (hact : y.endpoint.active = x.endpoint.active) (hpend : y.pending = x.pending)
    (hpre : y.prefixLength = x.prefixLength)
    (hlive : ∀ p : Port d m, p ∈ liveEnd y ↔ p.1 ∈ x.endpoint.active) :
    SweepProps P (J + 1) 0 y := by
  refine ⟨fun i => (hlive (i, true)).trans (by rw [hact]),
    fun i hi _ => (hlive (i, false)).mpr (by show i ∈ x.endpoint.active; rw [← hact]; exact hi),
    fun i _ _ hp => absurd hp (fun ⟨_, _, h⟩ => Nat.not_lt_zero _ h), fun i hi hp _ => ?_⟩
  rw [hact] at hi; rw [hpend] at hp
  rw [hpre, hx i hi hp]
  unfold doneLength; rw [if_pos hJ]; omega

end Transfer

/-! ## The clearing block (DONE / FAIL field updates) -/

section Clearing
variable (n₀ j : ℕ) (u : ℝ) (yy : Torus d m) (x : RunRecord d m)

/-- Reachable states of the clearing block keep the record; the provisional active set lies in
the committed one, and inspected sites have left it unless the attempt failed. -/
theorem clear_reach (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock n₀ j u yy) x s) :
    s.1 = x ∧ s.2.active ⊆ x.endpoint.active ∧
      (s.2.failed = false → ∀ i ∈ s.2.inspected, i ∉ s.2.active) := by
  classical
  induction hs with
  | enter =>
    refine ⟨rfl, ?_, ?_⟩
    · simp [clearingBlock, clearInitScratch]
    · intro _ i hi; simp [clearingBlock, clearInitScratch] at hi
  | step s a _ _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    show (clearingUpdate n₀ j u s a).1 = x ∧
      (clearingUpdate n₀ j u s a).2.active ⊆ x.endpoint.active ∧
      ((clearingUpdate n₀ j u s a).2.failed = false →
        ∀ i ∈ (clearingUpdate n₀ j u s a).2.inspected, i ∉ (clearingUpdate n₀ j u s a).2.active)
    unfold clearingUpdate
    dsimp only
    split
    · exact ⟨h1, h2, h3⟩
    · rename_i hnd
      have hf : s.2.failed = false := by
        cases hfl : s.2.failed
        · rfl
        · exact absurd (Or.inl hfl) hnd
      cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
      | fail po =>
        exact ⟨h1, h2, fun hff => by simp at hff⟩
      | coreReady => exact ⟨h1, h2, h3⟩
      | heat p hg =>
        dsimp only
        have hsub : s.2.active.erase p ⊆ x.endpoint.active := (Finset.erase_subset _ _).trans h2
        have hins : ∀ i ∈ insert p s.2.inspected, i ∉ s.2.active.erase p := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.notMem_erase _ _
          · exact fun hm => h3 hf i hi (Finset.mem_of_mem_erase hm)
        split_ifs <;> exact ⟨h1, hsub, fun _ => hins⟩
      | coreQuery y _ =>
        dsimp only
        refine ⟨h1, (Finset.erase_subset _ _).trans h2, fun _ i hi hm => ?_⟩
        exact h3 hf i hi (Finset.mem_of_mem_erase hm)
      | finish => exact ⟨h1, h2, h3⟩

/-- **Clearing block, record level** (DONE: `terminal ∪= core ∪ inspected`,
`active := sc.active \ core`, `pending \= core ∪ inspected`; FAIL: `pending ∪= core ∪ inspected`;
otherwise the record is restored). -/
theorem clear_exit (s : RunRecord d m × ClearScratch d m)
    (hs : BlockReach (clearingBlock n₀ j u yy) x s) :
    ((clearingBlock n₀ j u yy).exit s).aborted = x.aborted ∧
      ((clearingBlock n₀ j u yy).exit s).prefixLength = x.prefixLength ∧
      ∀ i ∈ ((clearingBlock n₀ j u yy).exit s).endpoint.active, i ∈ x.endpoint.active ∧
        (i ∉ x.terminal → i ∉ ((clearingBlock n₀ j u yy).exit s).terminal) ∧
        (i ∉ ((clearingBlock n₀ j u yy).exit s).pending → i ∉ x.pending) := by
  classical
  obtain ⟨h1, h2, h3⟩ := clear_reach n₀ j u yy x s hs
  obtain ⟨r, sc⟩ := s
  simp only at h1 h2 h3
  subst h1
  have hex : (clearingBlock n₀ j u yy).exit (r, sc) = clearingExit j yy (r, sc) := rfl
  rw [hex]
  unfold clearingExit
  simp only
  split_ifs with ha hsch hcore hfail hdone
  · exact ⟨rfl, rfl, fun i hi => ⟨hi, id, id⟩⟩
  · exact ⟨rfl, rfl, fun i hi => ⟨hi, id, id⟩⟩
  · exact ⟨rfl, rfl, fun i hi => ⟨hi, id, id⟩⟩
  · refine ⟨rfl, rfl, fun i hi => ⟨hi, id, fun hp h' => hp ?_⟩⟩
    simp only [clearingFailExit]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ h')
  · have hf : sc.failed = false := by simpa using hfail
    refine ⟨rfl, rfl, fun i hi => ?_⟩
    simp only [clearingDoneExit, Finset.mem_sdiff] at hi
    have hni : i ∉ sc.inspected := fun h' => h3 hf i h' hi.1
    refine ⟨h2 hi.1, fun ht h' => ?_, fun hp h' => hp ?_⟩
    · simp only [clearingDoneExit, Finset.mem_union] at h'
      rcases h' with (h' | h') | h'
      · exact ht h'
      · exact hi.2 h'
      · exact hni h'
    · simp only [clearingDoneExit, Finset.mem_sdiff, Finset.mem_union]
      exact ⟨h', fun h'' => h''.elim hi.2 hni⟩
  · exact ⟨rfl, rfl, fun i hi => ⟨hi, id, id⟩⟩

end Clearing

/-! ## Phases of consecutive block indices -/

/-- Closes the goals left by splitting `phaseOf` at consecutive indices. -/
macro "phase_tac" : tactic =>
  `(tactic| first | rfl | contradiction | omega | (congr 1 <;> omega) |
    (simp only [and_true, true_and, ne_eq, not_true_eq_false, and_false, false_and, not_and,
      not_false_eq_true] at * <;> omega) |
    (simp only [and_true, true_and, ne_eq, not_true_eq_false, and_false, false_and, not_and,
      not_false_eq_true] at * <;> congr 1 <;> omega))

section RBPhase
variable (P : TilePlan d m)

theorem phaseOf_tile (n : ℕ) (hK : decodeK d m n = 0) (hJ1 : P.n₀ < decodeJ d m n)
    (hJ2 : decodeJ d m n ≤ m + 1) :
    phaseOf P n = .sweep (decodeJ d m n) (n % siteCount d m) ∧
      phaseOf P (n + 1) = .sweep (decodeJ d m n) (n % siteCount d m + 1) := by
  have hn1 : ¬ decodeJ d m n ≤ P.n₀ := by omega
  refine ⟨by simp only [phaseOf] <;> split_ifs <;> phase_tac, ?_⟩
  rcases decode_succ (d := d) (m := m) n with ⟨-, hj, hk, hr⟩ | ⟨hR, -, hj, hk, hr⟩ | ⟨-, hk3, -⟩
  · simp only [phaseOf, hj, hk, hr] <;> split_ifs <;> phase_tac
  · simp only [phaseOf, hj, hk, hr]
    all_goals (split_ifs <;> phase_tac)
  · omega

theorem phaseOf_end (n : ℕ) (hK : decodeK d m n = 1) (hR : n % siteCount d m = 0)
    (hJ1 : P.n₀ < decodeJ d m n) (hJ2 : decodeJ d m n ≤ m + 1) :
    phaseOf P n = .sweep (decodeJ d m n) (siteCount d m) ∧
      phaseOf P (n + 1) = .post (decodeJ d m n) := by
  have hn1 : ¬ decodeJ d m n ≤ P.n₀ := by omega
  refine ⟨by simp only [phaseOf] <;> split_ifs <;> phase_tac, ?_⟩
  rcases decode_succ (d := d) (m := m) n with ⟨-, hj, hk, hr⟩ | ⟨-, -, hj, hk, hr⟩ | ⟨-, hk3, -⟩
  · simp only [phaseOf, hj, hk, hr] <;> split_ifs <;> phase_tac
  · simp only [phaseOf, hj, hk, hr] <;> split_ifs <;> phase_tac
  · omega

theorem phaseOf_clear (n : ℕ) (hK : decodeK d m n = 2)
    (hJ1 : P.n₀ < decodeJ d m n) (hJ2 : decodeJ d m n ≤ m + 1) :
    phaseOf P n = .post (decodeJ d m n) ∧ phaseOf P (n + 1) = .post (decodeJ d m n) := by
  have hn1 : ¬ decodeJ d m n ≤ P.n₀ := by omega
  refine ⟨by simp only [phaseOf] <;> split_ifs <;> phase_tac, ?_⟩
  rcases decode_succ (d := d) (m := m) n with ⟨-, hj, hk, hr⟩ | ⟨-, -, hj, hk, hr⟩ | ⟨-, hk3, -⟩
  · simp only [phaseOf, hj, hk, hr] <;> split_ifs <;> phase_tac
  · simp only [phaseOf, hj, hk, hr] <;> split_ifs <;> phase_tac
  · omega

theorem phaseOf_stage (n : ℕ) (hK : decodeK d m n = 3) (hR : n % siteCount d m = 0)
    (hJ1 : P.n₀ < decodeJ d m n) (hJ2 : decodeJ d m n ≤ m) :
    phaseOf P n = .post (decodeJ d m n) ∧ phaseOf P (n + 1) = .sweep (decodeJ d m n + 1) 0 := by
  have hn1 : ¬ decodeJ d m n ≤ P.n₀ := by omega
  have hJ2' : decodeJ d m n ≤ m + 1 := by omega
  refine ⟨by simp only [phaseOf] <;> split_ifs <;> phase_tac, ?_⟩
  rcases decode_succ (d := d) (m := m) n with ⟨-, hj, hk, hr⟩ | ⟨-, hk3, -⟩ | ⟨-, -, hj, hk, hr⟩
  · simp only [phaseOf, hj, hk, hr] <;> split_ifs <;> phase_tac
  · omega
  · have h1 : ¬ decodeJ d m n + 1 ≤ P.n₀ := by omega
    have h2 : decodeJ d m n + 1 ≤ m + 1 := by omega
    simp only [phaseOf, hj, hk, hr] <;> split_ifs <;> phase_tac

theorem phaseOf_empty (n : ℕ)
    (h : decodeJ d m n ≤ P.n₀ ∨ m + 1 < decodeJ d m n ∨
      (decodeK d m n = 1 ∧ n % siteCount d m ≠ 0) ∨ decodeK d m n = 2 ∨
      (decodeK d m n = 3 ∧ (n % siteCount d m ≠ 0 ∨ m < decodeJ d m n))) :
    phaseOf P (n + 1) = phaseOf P n ∨ phaseOf P (n + 1) = .free := by
  have hK4 := decodeK_lt (d := d) (m := m) n
  rcases decode_succ (d := d) (m := m) n with ⟨-, hj, hk, hr⟩ | ⟨hRN, hK3, hj, hk, hr⟩ |
      ⟨hRN, hK3, hj, hk, hr⟩
  · left
    simp only [phaseOf, hj, hk, hr]
    all_goals (split_ifs <;> phase_tac)
  · left
    simp only [phaseOf, hj, hk, hr]
    all_goals (split_ifs <;> phase_tac)
  · simp only [phaseOf, hj, hk, hr]
    all_goals (split_ifs <;> first | (left; rfl) | (right; rfl) | (left; phase_tac))

end RBPhase

/-! ## Closure under the blocks of the schedule -/

/-- **Completeness of accepted tile trials on real answers** — the body of
`TileCompleteStatement` (agent-s78tphase, TilePhaseRun.lean; `TileOrderSizes` and
`TileAcceptComplete` unfolded), proved there as `tileComplete_proof` (lane/agent-s78tphase
5df2dae). After merging that branch, `fun … => tileComplete_proof …` gives this statement. -/
def RunTileCompleteStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M),
    (∀ a, M (tileOrderIndex j T a) = (tileSites (P.cover j) T).card) → x.aborted = false →
    (∀ i ∈ tileSites (P.cover j) T, i ∈ x.endpoint.active →
      i ∉ x.terminal ∧ ((i, false) : Port d m) ∈ (x.sweep.state x.sweep.length).live) →
    (∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false) →
    (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true →
    ((localState M (tileBlock P j T) x k ω).1.aborted = false →
      ∀ i ∈ TS P j T, i ∈ x.endpoint.active →
        ((i, false) : Port d m) ∉ ((localState M (tileBlock P j T) x k ω).1.sweep.state
          (localState M (tileBlock P j T) x k ω).1.sweep.length).live)

section Close
variable (P : TilePlan d m)

theorem cutoff_decode : decodeJ d m (cutoffIndex d m) = m / 2 ∧
    decodeK d m (cutoffIndex d m) = 3 ∧ cutoffIndex d m % siteCount d m = 0 := by
  obtain ⟨h1, h2, h3⟩ := decode_opIndex (d := d) (m := m) (m / 2) 3 (site₀ d m) (by norm_num)
  refine ⟨h1, h2, ?_⟩
  rw [← rank_decodeY]
  show ((siteRank d m (decodeY d m (opIndex d m (m / 2) 3 (site₀ d m)))) : ℕ) = 0
  rw [h3, rank_site₀]

/-- Empty blocks. -/
theorem basics_empty (n : ℕ)
    (h : decodeJ d m n ≤ P.n₀ ∨ m + 1 < decodeJ d m n ∨
      (decodeK d m n = 1 ∧ n % siteCount d m ≠ 0) ∨ decodeK d m n = 2 ∨
      (decodeK d m n = 3 ∧ (n % siteCount d m ≠ 0 ∨ m < decodeJ d m n)))
    (hcl : decodeK d m n = 2 → m / 2 < decodeJ d m n ∨ decodeJ d m n ≤ P.n₀ ∨
      m + 1 < decodeJ d m n)
    (x : RunRecord d m) (hx : x ∈ RunBasics P n) : x ∈ RunBasics P (n + 1) := by
  intro hab
  obtain ⟨h1, h2, h3⟩ := hx hab
  refine ⟨fun hle => h1 (by omega), fun hc => ?_, ?_⟩
  · rcases cutDone_succ P n hc with hc | ⟨rfl, hn⟩
    · exact h2 hc
    · obtain ⟨c1, c2, c3⟩ := cutoff_decode (d := d) (m := m)
      exfalso
      rw [c1, c2, c3] at h
      omega
  · rcases phaseOf_empty P n h with he | he <;> rw [he]
    · exact h3
    · trivial

theorem aborted_of_exit {x z : RunRecord d m} (hzx : x.aborted = true → z.aborted = true)
    (hz : z.aborted = false) : x.aborted = false := by
  cases h : x.aborted
  · rfl
  · rw [hzx h] at hz; cases hz

/-- Tile blocks. -/
theorem basics_tile (n : ℕ) (hK : decodeK d m n = 0) (hJ1 : P.n₀ < decodeJ d m n)
    (hJ2 : decodeJ d m n ≤ m + 1) (T : Fin (P.cover (decodeJ d m n)).cover.count)
    (hT : tileAt P (decodeJ d m n) (decodeY d m n) = some T) (x z : RunRecord d m)
    (hx : x ∈ RunBasics P n) (hzx : x.aborted = true → z.aborted = true)
    (hE : x.aborted = false → z.aborted = false → TExitOK P (decodeJ d m n) T x z)
    (hcomp : x.aborted = false → (∀ i ∈ TS P (decodeJ d m n) T, i ∈ x.endpoint.active →
        i ∉ x.terminal ∧ ((i, false) : Port d m) ∈ liveEnd x) →
      z.aborted = false → ∀ i ∈ TS P (decodeJ d m n) T, i ∈ x.endpoint.active →
        ((i, false) : Port d m) ∉ liveEnd z) :
    z ∈ RunBasics P (n + 1) := by
  intro hzab
  have hxab := aborted_of_exit hzx hzab
  obtain ⟨h1, h2, h3⟩ := hx hxab
  have hE' := hE hxab hzab
  obtain ⟨hph, hph'⟩ := phaseOf_tile P n hK hJ1 hJ2
  rw [hph] at h3
  have h3' : SweepProps P (decodeJ d m n) (siteRank d m (decodeY d m n)) x := by
    rw [rank_decodeY]; exact h3
  have hlt : ¬ IsFinalSweep m (decodeJ d m n) → n < finalStart d m := fun hf =>
    (lt_finalStart_iff n).mpr (by unfold IsFinalSweep at hf; omega)
  have hc : ¬ IsFinalSweep m (decodeJ d m n) → ∀ i ∈ TS P (decodeJ d m n) T,
      i ∈ x.endpoint.active → ((i, false) : Port d m) ∉ liveEnd z := fun hf =>
    hcomp hxab (fun i hi ha => ⟨h1 (hlt hf).le i ha,
      h3'.bit i ha (not_processedBy_of_mem P _ _ T hT i hi)⟩) hzab
  have sp := sweepProps_tile P _ _ T hT hJ1 hJ2 x z h3' hE' hc
  refine ⟨fun hle i hi => ?_, fun hcd => ?_, ?_⟩
  · have hf : ¬ IsFinalSweep m (decodeJ d m n) := by
      intro hf
      have := (lt_finalStart_iff (d := d) (m := m) n).not.mpr (by unfold IsFinalSweep at hf; omega)
      omega
    rw [hE'.ep] at hi; rw [TExitOK.term_off P _ T x hE' hf]; exact h1 (by omega) i hi
  · obtain ⟨c1, c2, c3⟩ := cutoff_decode (d := d) (m := m)
    rcases cutDone_succ P n hcd with hcd | ⟨rfl, -⟩
    · have hlate : m / 2 < decodeJ d m n := by
        rcases hcd with hcd | hcd
        · rcases lt_cutoff_cases n hcd with h | ⟨-, h, -⟩
          · exact h
          · omega
        · omega
      rcases hE'.out with ⟨hpe, -⟩ | ⟨hno, -⟩
      · rw [hpe]; exact h2 hcd
      · exact absurd hlate hno
    · omega
  · rw [hph']; rw [rank_decodeY] at sp; exact sp

/-- Tile slots with no tile. -/
theorem basics_tileNone (n : ℕ) (hK : decodeK d m n = 0) (hJ1 : P.n₀ < decodeJ d m n)
    (hJ2 : decodeJ d m n ≤ m + 1) (hT : tileAt P (decodeJ d m n) (decodeY d m n) = none)
    (x : RunRecord d m) (hx : x ∈ RunBasics P n) : x ∈ RunBasics P (n + 1) := by
  intro hab
  obtain ⟨h1, h2, h3⟩ := hx hab
  obtain ⟨hph, hph'⟩ := phaseOf_tile P n hK hJ1 hJ2
  rw [hph] at h3
  have h3' : SweepProps P (decodeJ d m n) (siteRank d m (decodeY d m n)) x := by
    rw [rank_decodeY]; exact h3
  have sp := sweepProps_tileNone P _ _ hT x h3'
  refine ⟨fun hle => h1 (by omega), fun hcd => ?_, ?_⟩
  · obtain ⟨c1, c2, c3⟩ := cutoff_decode (d := d) (m := m)
    rcases cutDone_succ P n hcd with hcd | ⟨rfl, -⟩
    · exact h2 hcd
    · omega
  · rw [hph']; rw [rank_decodeY] at sp; exact sp

/-- The sweep-end block. -/
theorem basics_end (n : ℕ) (hK : decodeK d m n = 1) (hR : n % siteCount d m = 0)
    (hJ1 : P.n₀ < decodeJ d m n) (hJ2 : decodeJ d m n ≤ m + 1) (x : RunRecord d m)
    (hx : x ∈ RunBasics P n) : guardMap (endMap P (decodeJ d m n)) x ∈ RunBasics P (n + 1) := by
  intro hzab
  unfold guardMap at hzab ⊢
  split_ifs at hzab ⊢ with hxa
  · rw [hxa] at hzab; cases hzab
  have hxab : x.aborted = false := by simpa using hxa
  obtain ⟨h1, h2, h3⟩ := hx hxab
  obtain ⟨hph, hph'⟩ := phaseOf_end P n hK hR hJ1 hJ2
  rw [hph] at h3
  obtain ⟨f1, f2, f3, f4, -⟩ := endMap_fields P (decodeJ d m n) x
  have hact : (endMap P (decodeJ d m n) x).endpoint.active = x.endpoint.active := by
    rw [f1]; exact sweepEndActive_eq_rb x h3.reserve
  have hpost := postProps_of_all P _ x h3
  refine ⟨fun hle i hi => ?_, fun hcd => ?_, ?_⟩
  · rw [hact] at hi; rw [f2]; exact h1 (by omega) i hi
  · obtain ⟨c1, c2, c3⟩ := cutoff_decode (d := d) (m := m)
    rcases cutDone_succ P n hcd with hcd | ⟨rfl, -⟩
    · rw [f3]; exact h2 hcd
    · omega
  · rw [hph']
    intro i hi hp
    rw [hact] at hi; rw [f3] at hp; rw [f4]; exact hpost i hi hp

/-- Clearing blocks, from the record-level facts of `clear_exit`. -/
theorem basics_clear (n : ℕ) (hK : decodeK d m n = 2) (hJ1 : P.n₀ < decodeJ d m n)
    (hJ2 : decodeJ d m n ≤ m / 2) (x z : RunRecord d m) (hx : x ∈ RunBasics P n)
    (hz : z.aborted = x.aborted ∧ z.prefixLength = x.prefixLength ∧
      ∀ i ∈ z.endpoint.active, i ∈ x.endpoint.active ∧ (i ∉ x.terminal → i ∉ z.terminal) ∧
        (i ∉ z.pending → i ∉ x.pending)) :
    z ∈ RunBasics P (n + 1) := by
  intro hzab
  have hxab : x.aborted = false := by rw [← hz.1]; exact hzab
  obtain ⟨h1, -, h3⟩ := hx hxab
  have hJ2' : decodeJ d m n ≤ m + 1 := by omega
  obtain ⟨hph, hph'⟩ := phaseOf_clear P n hK hJ1 hJ2'
  rw [hph] at h3
  refine ⟨fun hle i hi => (hz.2.2 i hi).2.1 (h1 (by omega) i (hz.2.2 i hi).1), fun hcd => ?_, ?_⟩
  · exfalso
    obtain ⟨c1, c2, c3⟩ := cutoff_decode (d := d) (m := m)
    rcases cutDone_succ P n hcd with hcd | ⟨rfl, -⟩
    · rcases hcd with hcd | hcd
      · rcases lt_cutoff_cases n hcd with h | ⟨-, h, -⟩ <;> omega
      · omega
    · omega
  · rw [hph']
    intro i hi hp
    obtain ⟨ha, -, hpn⟩ := hz.2.2 i hi
    rw [hz.2.1]; exact h3 i ha (hpn hp)

/-- The stage operation `sweepStartMap ∘ (cutoff at ⌊m/2⌋) ∘ f` for a reset map `f` keeping the
fields (`resetMap`; `resetMapA` after the switch to `stageMapA`). -/
theorem basics_stage (f : RunRecord d m → RunRecord d m) (hf : KeepsBasics f) (θ t : ℝ)
    (n : ℕ) (hK : decodeK d m n = 3) (hR : n % siteCount d m = 0)
    (hJ1 : P.n₀ < decodeJ d m n) (hJ2 : decodeJ d m n ≤ m) (x : RunRecord d m)
    (hx : x ∈ RunBasics P n) :
    guardMap (fun x => sweepStartMap θ t
      ((if decodeJ d m n = m / 2 then cutoffMap else id) (f x))) x ∈ RunBasics P (n + 1) := by
  intro hzab
  by_cases hxa : x.aborted = true
  · unfold guardMap at hzab; rw [if_pos hxa, hxa] at hzab; cases hzab
  have hge : guardMap (fun x => sweepStartMap θ t
      ((if decodeJ d m n = m / 2 then cutoffMap else id) (f x))) x =
      sweepStartMap θ t ((if decodeJ d m n = m / 2 then cutoffMap else id) (f x)) := by
    unfold guardMap; rw [if_neg hxa]
  rw [hge] at hzab ⊢
  have hxab : x.aborted = false := by simpa using hxa
  obtain ⟨h1, h2, h3⟩ := hx hxab
  obtain ⟨hph, hph'⟩ := phaseOf_stage P n hK hR hJ1 hJ2
  rw [hph] at h3
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := stageWith_fields f hf θ t (decodeJ d m n = m / 2) x
  refine ⟨fun hle i hi => ?_, fun hcd => ?_, ?_⟩
  · rw [f1] at hi; rw [f2]; exact h1 (by omega) i hi
  · rw [f3]
    rcases cutDone_succ P n hcd with hcd | ⟨rfl, -⟩
    · exact h2 hcd
    · exact (f5 hzab).2 (cutoff_decode (d := d) (m := m)).1
  · rw [hph']
    exact sweepProps_stage P _ hJ2 x _ h3 f1 f3 f4 f6

theorem stageMap_eq (j : ℕ) (x : RunRecord d m) :
    stageMap P j x = sweepStartMap (sweepTheta P.u m (j + 1)) (sweepScale P.u m (j + 1))
      ((if j = m / 2 then cutoffMap else id) (resetMapA (stageScale P.u j m) x)) := rfl

end Close

/-! ## The closure theorem -/

section Main
variable {Sc : Type} [MeasurableSpace Sc]

omit [MeasurableSpace Sc] in
theorem simpleBlock_exit (M : ℕ → ℕ) (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hrun : ∀ k' < k, (simpleBlock sc₀ f).halted (localState M (simpleBlock sc₀ f) x k' ω) = false) :
    (simpleBlock sc₀ f).exit (localState M (simpleBlock sc₀ f) x k ω) = f x := by
  rw [simpleBlock_reach sc₀ f x _ (localState_reach M _ x ω k hrun)]
  rfl

theorem tile_reach_aborted (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (x : RunRecord d m) (hab : x.aborted = true) (s : RunRecord d m × TileScratch d m)
    (hs : BlockReach (tileBlock P j T) x s) : s.1 = x := by
  have key : s = (x, { initScratch x with halted := true }) := by
    induction hs with
    | enter => simp [tileBlock, hab]
    | step s a _ hnh ih => rw [ih] at hnh; simp [tileBlock] at hnh
  rw [key]

end Main

/-- **`RunBasics` is closed under every block of the schedule**, in the `hInv` shape of
`blockRun_of_runOps` (block-local runs along the answers of `ω`), for the clearing block
`clearingBlock n₀ j u y`. The only input is the completeness of accepted tile trials
(`RunTileCompleteStatement`, agent-s78tphase's `tileComplete_proof`). -/
theorem runBasics_closed (hcomp : RunTileCompleteStatement) (P : TilePlan d m) (n₀ : ℕ) (u : ℝ)
    (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (n : ℕ) (x : RunRecord d m) (k : ℕ)
    (ω : RandomSources (Torus d m) (tileOrderSize P)) (hx : x ∈ RunBasics P n)
    (hrun : ∀ k' < k,
      (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n).halted
        (localState (tileOrderSize P)
          (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n) x k' ω) = false)
    (hh : (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n).halted
      (localState (tileOrderSize P)
        (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n) x k ω) = true) :
    (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n).exit
      (localState (tileOrderSize P)
        (scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n) x k ω) ∈
      RunBasics P (n + 1) := by
  classical
  have hK4 := decodeK_lt (d := d) (m := m) n
  have hB : scheduleBlocks (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y)) n =
      runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y) (decodeJ d m n) (decodeK d m n)
        (decodeY d m n) := rfl
  rw [hB] at hrun hh ⊢
  have hsimple : ∀ f : RunRecord d m → RunRecord d m,
      runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y) (decodeJ d m n) (decodeK d m n)
        (decodeY d m n) = simpleBlock (ts₀, cl₀) f →
      (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y) (decodeJ d m n) (decodeK d m n)
        (decodeY d m n)).exit (localState (tileOrderSize P)
          (runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y) (decodeJ d m n) (decodeK d m n)
            (decodeY d m n)) x k ω) = f x := by
    intro f hf
    rw [hf] at hrun ⊢
    exact simpleBlock_exit (tileOrderSize P) (ts₀, cl₀) f x k ω hrun
  by_cases hin : P.n₀ < decodeJ d m n ∧ decodeJ d m n ≤ m + 1
  swap
  · rw [hsimple id (by unfold runOp; rw [if_neg hin])]
    exact basics_empty P n (by omega) (by omega) x hx
  by_cases hk0 : decodeK d m n = 0
  · cases hT : tileAt P (decodeJ d m n) (decodeY d m n) with
    | none =>
      rw [hsimple id (by unfold runOp; rw [if_pos hin, if_pos hk0, hT])]
      exact basics_tileNone P n hk0 hin.1 hin.2 hT x hx
    | some T =>
      have hrB : runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y) (decodeJ d m n)
          (decodeK d m n) (decodeY d m n) =
          (tileBlock P (decodeJ d m n) T).embed (tileEmbed cl₀) tileProj := by
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
      have hreach := localState_reach (tileOrderSize P) _ x ω k hrun'
      refine basics_tile P n hk0 hin.1 hin.2 T hT x _ hx (fun hab => ?_)
        (fun hab hzab => (tile_reach P _ T x hab _ hreach).2 hh' hzab)
        (fun hab hpre hzab => hcomp d m P (decodeJ d m n) T (tileOrderSize P) x k ω
          (tileOrderSize_index P _ T) hab hpre hrun' hh' hzab)
      rw [tile_reach_aborted P _ T x hab _ hreach]; exact hab
  by_cases hk1 : decodeK d m n = 1
  · by_cases hy : decodeY d m n = site₀ d m
    · rw [hsimple (guardMap (endMap P (decodeJ d m n)))
        (by unfold runOp; rw [if_pos hin, if_neg hk0, if_pos hk1, if_pos hy])]
      exact basics_end P n hk1 ((decodeY_eq_site₀_iff n).mp hy) hin.1 hin.2 x hx
    · rw [hsimple id (by unfold runOp; rw [if_pos hin, if_neg hk0, if_pos hk1, if_neg hy])]
      have h' : n % siteCount d m ≠ 0 := fun h0 => hy ((decodeY_eq_site₀_iff n).mpr h0)
      exact basics_empty P n (Or.inr (Or.inr (Or.inl ⟨hk1, h'⟩))) (by omega) x hx
  by_cases hk2 : decodeK d m n = 2
  · by_cases hjc : decodeJ d m n ≤ m / 2
    · have hrB : runOp P ts₀ cl₀ (fun j y => clearingBlock n₀ j u y) (decodeJ d m n)
          (decodeK d m n) (decodeY d m n) =
          (clearingBlock n₀ (decodeJ d m n) u (decodeY d m n)).embed (clearEmbed ts₀)
            clearProj := by
        unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_pos hk2, if_pos hjc]
      rw [hrB] at hrun hh ⊢
      obtain ⟨s, hs, hse⟩ := blockReach_embed (clearingBlock n₀ (decodeJ d m n) u (decodeY d m n))
        (clearEmbed ts₀) clearProj (fun _ => rfl) x _
        (localState_reach (tileOrderSize P) _ x ω k hrun)
      rw [hse]
      exact basics_clear P n hk2 hin.1 hjc x _ hx (clear_exit n₀ _ u _ x s hs)
    · rw [hsimple id (by unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_pos hk2,
        if_neg hjc])]
      exact basics_empty P n (Or.inr (Or.inr (Or.inr (Or.inl hk2)))) (by omega) x hx
  have hk3 : decodeK d m n = 3 := by omega
  by_cases hjy : decodeJ d m n ≤ m ∧ decodeY d m n = site₀ d m
  · rw [hsimple (guardMap (stageMap P (decodeJ d m n)))
      (by unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_neg hk2, if_pos hjy])]
    exact basics_stage P (resetMapA (stageScale P.u (decodeJ d m n) m)) (resetMapA_keepsBasics _)
      (sweepTheta P.u m (decodeJ d m n + 1)) (sweepScale P.u m (decodeJ d m n + 1)) n hk3
      ((decodeY_eq_site₀_iff n).mp hjy.2) hin.1 hjy.1 x hx
  · rw [hsimple id (by unfold runOp; rw [if_pos hin, if_neg hk0, if_neg hk1, if_neg hk2,
      if_neg hjy])]
    have h' : n % siteCount d m ≠ 0 ∨ m < decodeJ d m n := by
      rcases not_and_or.mp hjy with h | h
      · right; omega
      · left; exact fun h0 => h ((decodeY_eq_site₀_iff n).mpr h0)
    exact basics_empty P n (Or.inr (Or.inr (Or.inr (Or.inr ⟨hk3, h'⟩)))) (by omega) x hx

/-! ## Initial record and projections -/

section Proj
variable (P : TilePlan d m)

theorem decodeJ_zero : decodeJ d m 0 = 0 := by unfold decodeJ; exact Nat.zero_div _

/-- `hInv0` for `RunBasics`. -/
theorem runBasics_zero (rec₀ : RunRecord d m)
    (h : rec₀.aborted = false → (∀ i ∈ rec₀.endpoint.active, i ∉ rec₀.terminal) ∧
      rec₀.pending = ∅ ∧ SweepProps P (P.n₀ + 1) 0 rec₀) : rec₀ ∈ RunBasics P 0 := by
  intro hab
  obtain ⟨h1, h2, h3⟩ := h hab
  have hJ : decodeJ d m 0 ≤ P.n₀ := by rw [decodeJ_zero]; exact Nat.zero_le _
  refine ⟨fun _ => h1, fun _ => h2, ?_⟩
  have : phaseOf P 0 = .sweep (P.n₀ + 1) 0 := by simp only [phaseOf, if_pos hJ]
  rw [this]; exact h3

/-- `hInv0` when the initial record is the stage-start lift of a record with no terminal
active site, no pending site and empty prefixes on the active sites. -/
theorem runBasics_zero_of_start (θ t : ℝ) (z : RunRecord d m)
    (hterm : ∀ i ∈ z.endpoint.active, i ∉ z.terminal) (hpend : z.pending = ∅)
    (hpref : ∀ i ∈ z.endpoint.active, z.prefixLength i = 0) :
    sweepStartMap θ t z ∈ RunBasics P 0 := by
  apply runBasics_zero
  intro _
  have hlive : ∀ p : Port d m, p ∈ liveEnd (sweepStartMap θ t z) ↔ p.1 ∈ z.endpoint.active := by
    intro p; simp [liveEnd, sweepStartMap, sweepStartLiveState]
  refine ⟨hterm, hpend, fun i => hlive (i, true), fun i hi _ => (hlive (i, false)).mpr hi,
    fun i _ _ hp => absurd hp (fun ⟨_, _, h⟩ => Nat.not_lt_zero _ h), fun i hi _ _ => ?_⟩
  show z.prefixLength i = P.n₀ + 1 - 1 - P.n₀
  rw [hpref i hi]; omega

/-- **The three projections at a sweep start** (phase `.sweep j 0`): no active site is
terminal; every active non-pending site has consumed `j − 1 − n₀` digits; at the final sweep
(`j = m + 1`, after the cutoff) no active site is pending and all have `m − n₀`. -/
theorem runBasics_sweepStart (j : ℕ) (hj : j ≤ m + 1) (n : ℕ) (hn : phaseOf P n = .sweep j 0)
    (hle : n ≤ finalStart d m)
    (hcut : IsFinalSweep m j → cutDone P n) (x : RunRecord d m) (hx : x ∈ RunBasics P n)
    (hab : x.aborted = false) :
    (∀ i ∈ x.endpoint.active, i ∉ x.terminal) ∧
      (∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i = j - 1 - P.n₀) ∧
      (IsFinalSweep m j → ∀ i ∈ x.endpoint.active, i ∉ x.pending) ∧
      (IsFinalSweep m j → ∀ i ∈ x.endpoint.active, x.prefixLength i = m - P.n₀) := by
  obtain ⟨h1, h2, h3⟩ := hx hab
  rw [hn] at h3
  have hpre : ∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i = j - 1 - P.n₀ :=
    fun i hi hp => h3.undone i hi hp (fun ⟨_, _, h⟩ => Nat.not_lt_zero _ h)
  have hpend : IsFinalSweep m j → ∀ i ∈ x.endpoint.active, i ∉ x.pending := by
    intro hf i _; rw [h2 (hcut hf)]; exact Finset.notMem_empty i
  refine ⟨h1 hle, hpre, hpend, fun hf i hi => ?_⟩
  rw [hpre i hi (hpend hf i hi)]
  unfold IsFinalSweep at hf
  omega

/-- The first tile slot of the sweep into stage `j`. -/
theorem phaseOf_firstTile (j : ℕ) (hj1 : P.n₀ < j) (hj2 : j ≤ m + 1) :
    phaseOf P (opIndex d m j 0 (site₀ d m)) = .sweep j 0 := by
  obtain ⟨e1, e2, e3⟩ := decode_opIndex (d := d) (m := m) j 0 (site₀ d m) (by norm_num)
  have hr : opIndex d m j 0 (site₀ d m) % siteCount d m = 0 := by
    rw [← rank_decodeY, e3, rank_site₀]
  have := (phaseOf_tile P (opIndex d m j 0 (site₀ d m)) e2 (by rw [e1]; exact hj1)
    (by rw [e1]; exact hj2)).1
  rw [this, e1, hr]

theorem cutDone_firstTile (j : ℕ) (hj : m / 2 < j) :
    cutDone P (opIndex d m j 0 (site₀ d m)) := by
  left
  rw [cutoffIndex_eq]
  unfold opIndex
  rw [rank_site₀, add_zero]
  exact Nat.mul_lt_mul_of_pos_right (by omega) (siteCount_pos d m)

/-- **Hypotheses (1)–(3) of `tileSweepInv_start`** for the record `z` whose stage-start lift
enters the first tile slot of the sweep into stage `j` (`n₀ < j ≤ m + 1`). -/
theorem runBasics_sweepStart_pre (θ t : ℝ) (j : ℕ) (hj1 : P.n₀ < j) (hj2 : j ≤ m + 1)
    (z : RunRecord d m) (hz : sweepStartMap θ t z ∈ RunBasics P (opIndex d m j 0 (site₀ d m)))
    (hab : z.aborted = false) :
    (∀ i ∈ z.endpoint.active, i ∉ z.terminal) ∧
      (IsFinalSweep m j → ∀ i ∈ z.endpoint.active, i ∉ z.pending) ∧
      (IsFinalSweep m j → ∀ i ∈ z.endpoint.active, z.prefixLength i = m - P.n₀) := by
  obtain ⟨h1, -, h3, h4⟩ := runBasics_sweepStart P j hj2 _ (phaseOf_firstTile P j hj1 hj2)
    (by rw [finalStart_eq]; unfold opIndex; rw [rank_site₀, add_zero, add_zero]
        rw [show (m + 1) * (4 * siteCount d m) = (4 * (m + 1)) * siteCount d m by ring]
        exact Nat.mul_le_mul_right _ (by omega))
    (fun hf => cutDone_firstTile P j (by unfold IsFinalSweep at hf; omega)) _ hz hab
  exact ⟨h1, h3, h4⟩

/-- The same projections right after the stage operation of stage `j − 1` (index
`opIndex (j − 1) 3 site₀ + 1`), where the exit of that block lies in `RunBasics`. -/
theorem runBasics_afterStage (j : ℕ) (hj1 : P.n₀ + 1 < j) (hj2 : j ≤ m + 1) (x : RunRecord d m)
    (hx : x ∈ RunBasics P (opIndex d m (j - 1) 3 (site₀ d m) + 1)) (hab : x.aborted = false) :
    (∀ i ∈ x.endpoint.active, i ∉ x.terminal) ∧
      (∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i = j - 1 - P.n₀) ∧
      (IsFinalSweep m j → ∀ i ∈ x.endpoint.active, i ∉ x.pending) ∧
      (IsFinalSweep m j → ∀ i ∈ x.endpoint.active, x.prefixLength i = m - P.n₀) := by
  obtain ⟨e1, e2, e3⟩ := decode_opIndex (d := d) (m := m) (j - 1) 3 (site₀ d m) (by norm_num)
  have hr : opIndex d m (j - 1) 3 (site₀ d m) % siteCount d m = 0 := by
    rw [← rank_decodeY, e3, rank_site₀]
  have hph := (phaseOf_stage P _ e2 hr (by rw [e1]; omega) (by rw [e1]; omega)).2
  rw [e1, show j - 1 + 1 = j by omega] at hph
  have hN := siteCount_pos d m
  refine runBasics_sweepStart P j hj2 _ hph ?_ (fun hf => ?_) x hx hab
  · rw [finalStart_eq]; unfold opIndex; rw [rank_site₀, add_zero]
    have h4 : 4 * (j - 1) + 3 + 1 ≤ 4 * (m + 1) := by omega
    calc (4 * (j - 1) + 3) * siteCount d m + 1 ≤ (4 * (j - 1) + 3) * siteCount d m + siteCount d m :=
          by omega
      _ = (4 * (j - 1) + 3 + 1) * siteCount d m := by ring
      _ ≤ (4 * (m + 1)) * siteCount d m := Nat.mul_le_mul_right _ h4
      _ = (m + 1) * (4 * siteCount d m) := by ring
  left
  unfold IsFinalSweep at hf
  rw [cutoffIndex_eq]
  unfold opIndex
  rw [rank_site₀, add_zero]
  have : 4 * (m / 2) + 3 ≤ 4 * (j - 1) + 3 := by omega
  exact Nat.lt_succ_of_le (Nat.mul_le_mul_right _ this)

/-- `runBasics_afterStage` in the hypothesis form of `tileSweepInv_start`, for the record `z`
before the stage-start lift. -/
theorem runBasics_afterStage_pre (θ t : ℝ) (j : ℕ) (hj1 : P.n₀ + 1 < j) (hj2 : j ≤ m + 1)
    (z : RunRecord d m)
    (hz : sweepStartMap θ t z ∈ RunBasics P (opIndex d m (j - 1) 3 (site₀ d m) + 1))
    (hab : z.aborted = false) :
    (∀ i ∈ z.endpoint.active, i ∉ z.terminal) ∧
      (IsFinalSweep m j → ∀ i ∈ z.endpoint.active, i ∉ z.pending) ∧
      (IsFinalSweep m j → ∀ i ∈ z.endpoint.active, z.prefixLength i = m - P.n₀) := by
  obtain ⟨h1, -, h3, h4⟩ := runBasics_afterStage P j hj1 hj2 _ hz hab
  exact ⟨h1, h3, h4⟩

end Proj

end AndersonAC.AgentS78
