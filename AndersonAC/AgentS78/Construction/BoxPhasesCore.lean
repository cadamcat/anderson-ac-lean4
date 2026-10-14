import AndersonAC.AgentS78.Construction.BoxSplit
import AndersonAC.AgentS78.Construction.RunBasics
import AndersonAC.AgentS78.Construction.PathwiseInvariant
import AndersonAC.AgentS78.Construction.RunOpsDisc

/-!
# WP10 construction: the global run invariant, index bookkeeping (agent-s78box)

DISPATCH 2026-10-14 02:58:56 (agent-s78con3). The run invariant of one box at block index `n`
(`n = opIndex j k y`, decoded by `decodeJ/K/Y`) is a run-level set `RB n` (RunBasics) intersected
with the set of the current **phase**:

| index `(j, k, y)`, `r = rank y`, `N = siteCount` | phase |
|---|---|
| `j ≤ n₀` (before the first sweep) | `TS (n₀+1) 0` |
| `k = 0` | `TS j r` (tiles of anchor rank `< r` processed) |
| `k = 1`, `y = site₀` (sweep end) | `TS j N` |
| `j = m + 1`, after the final sweep end | `FG` |
| `k = 3`, `y ≠ site₀`, `j ≤ m` (after the stage operation) | `TS (j+1) 0` |
| otherwise (`k = 1, y ≠ site₀`; `k = 2`; `k = 3, y = site₀`), `j ≤ m` | `CL j` |
| `j > m + 1` | `FG` |

`boxInv_closed`: the invariant `RB n ∩ phase n` is closed along every block (the `hInv` shape of
`BoxInvariantK`) once `RB` is closed and the five non-identity operations map the phase sets as
in the table (`OpKeeps`): tile operations `TS j r → TS j (r+1)`, digit sweep ends
`TS j N → CL j`, the final sweep end `TS (m+1) N → FG`, clearing operations `CL j → CL j`
(`j ≤ ⌊m/2⌋`), stage operations `CL j → TS (j+1) 0`. Every other operation is the identity and
the phase does not change. `boxInvariantK_of_core` then assembles `BoxInvariantK`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-! ## Phases -/

/-- The phase of a block index. -/
inductive BoxPhase
  | tile (j r : ℕ)
  | clear (j r : ℕ)
  | final

/-- The phase as a function of `(n₀, m, N)` and the decoded `(j, k, r)`. -/
def phaseJKR (n₀ m N J K R : ℕ) : BoxPhase :=
  if J ≤ n₀ then .tile (n₀ + 1) 0
  else if J ≤ m + 1 then
    if K = 0 then .tile J R
    else if K = 1 ∧ R = 0 then .tile J N
    else if m < J then .final
    else if K = 3 ∧ R ≠ 0 then .tile (J + 1) 0
    else if K = 2 then .clear J R
    else if K = 3 then .clear J N
    else .clear J 0
  else .final

/-- The phase of block index `n`. -/
def boxPhase (P : TilePlan d m) (n : ℕ) : BoxPhase :=
  phaseJKR P.n₀ m (siteCount d m) (decodeJ d m n) (decodeK d m n) (n % siteCount d m)

/-- The set required by a phase. -/
def BoxPhase.set {R : Type} (TS : ℕ → ℕ → Set R) (CL : ℕ → ℕ → Set R) (FG : Set R) :
    BoxPhase → Set R
  | .tile j r => TS j r
  | .clear j r => CL j r
  | .final => FG

/-- **The global run invariant** of a box. -/
def boxInv (P : TilePlan d m) (RB : ℕ → Set (RunRecord d m)) (TS : ℕ → ℕ → Set (RunRecord d m))
    (CL : ℕ → ℕ → Set (RunRecord d m)) (FG : Set (RunRecord d m)) (n : ℕ) : Set (RunRecord d m) :=
  RB n ∩ (boxPhase P n).set TS CL FG

/-! ## Index arithmetic -/

section Arith

/-- Closes the goals left by splitting `phaseJKR` at consecutive indices. -/
macro "phase_close" : tactic =>
  `(tactic| first
    | rfl
    | (exfalso; omega)
    | (exfalso; simp_all; done)
    | (congr 1 <;> omega)
    | (refine ⟨?_, ?_⟩ <;> first | rfl | (congr 1 <;> omega) | (exfalso; omega)))

/-- The successor of index `n` in decoded form (`decode_succ` with `R = n % N`). -/
theorem boxPhase_succ_cases (P : TilePlan d m) (n : ℕ) :
    ∃ J' K' R', boxPhase P (n + 1) = phaseJKR P.n₀ m (siteCount d m) J' K' R' ∧
      ((n % siteCount d m + 1 < siteCount d m ∧ J' = decodeJ d m n ∧ K' = decodeK d m n ∧
          R' = n % siteCount d m + 1) ∨
        (n % siteCount d m + 1 = siteCount d m ∧ decodeK d m n < 3 ∧ J' = decodeJ d m n ∧
          K' = decodeK d m n + 1 ∧ R' = 0) ∨
        (n % siteCount d m + 1 = siteCount d m ∧ decodeK d m n = 3 ∧
          J' = decodeJ d m n + 1 ∧ K' = 0 ∧ R' = 0)) := by
  refine ⟨decodeJ d m (n + 1), decodeK d m (n + 1), (n + 1) % siteCount d m, rfl, ?_⟩
  rcases decode_succ (d := d) (m := m) n with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h1, h2, h3, h4⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h3, h4, h5⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, h3, h4, h5⟩)

/-- Identity operations of the schedule. -/
def IdIndex (P : TilePlan d m) (n : ℕ) : Prop :=
  ¬ (P.n₀ < decodeJ d m n ∧ decodeJ d m n ≤ m + 1) ∨
    (decodeK d m n = 1 ∧ n % siteCount d m ≠ 0) ∨
    (decodeK d m n = 2 ∧ m < decodeJ d m n) ∨
    (decodeK d m n = 3 ∧ ¬ (decodeJ d m n ≤ m ∧ n % siteCount d m = 0))

theorem decodeK_lt4 (n : ℕ) : decodeK d m n < 4 := decodeK_lt n

set_option maxHeartbeats 2000000 in
/-- **The phase does not change across an identity operation.** -/
theorem boxPhase_succ_id (P : TilePlan d m) (hnm : P.n₀ ≤ m) (n : ℕ) (h : IdIndex P n) :
    boxPhase P (n + 1) = boxPhase P n := by
  obtain ⟨J', K', R', he, hc⟩ := boxPhase_succ_cases P n
  rw [he]
  have hK := decodeK_lt4 (d := d) (m := m) n
  have hRN := Nat.mod_lt n (siteCount_pos d m)
  unfold boxPhase IdIndex at *
  generalize decodeJ d m n = J at *
  generalize decodeK d m n = K at *
  generalize n % siteCount d m = R at *
  generalize siteCount d m = N at *
  unfold phaseJKR
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
    subst_vars <;>
    split_ifs <;> phase_close

set_option maxHeartbeats 2000000 in
theorem boxPhase_tile (P : TilePlan d m) (n : ℕ) (hK : decodeK d m n = 0)
    (h1 : P.n₀ < decodeJ d m n) (h2 : decodeJ d m n ≤ m + 1) :
    boxPhase P n = .tile (decodeJ d m n) (n % siteCount d m) ∧
      boxPhase P (n + 1) = .tile (decodeJ d m n) (n % siteCount d m + 1) := by
  obtain ⟨J', K', R', he, hc⟩ := boxPhase_succ_cases P n
  rw [he]
  unfold boxPhase
  generalize decodeJ d m n = J at *
  generalize decodeK d m n = K at *
  generalize n % siteCount d m = R at *
  generalize siteCount d m = N at *
  unfold phaseJKR
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
    subst_vars <;>
    split_ifs <;> phase_close

set_option maxHeartbeats 2000000 in
theorem boxPhase_end (P : TilePlan d m) (n : ℕ) (hK : decodeK d m n = 1)
    (hR : n % siteCount d m = 0) (h1 : P.n₀ < decodeJ d m n) (h2 : decodeJ d m n ≤ m) :
    boxPhase P n = .tile (decodeJ d m n) (siteCount d m) ∧
      boxPhase P (n + 1) = .clear (decodeJ d m n) 0 := by
  obtain ⟨J', K', R', he, hc⟩ := boxPhase_succ_cases P n
  rw [he]
  unfold boxPhase
  generalize decodeJ d m n = J at *
  generalize decodeK d m n = K at *
  generalize n % siteCount d m = R at *
  generalize siteCount d m = N at *
  unfold phaseJKR
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
    subst_vars <;>
    split_ifs <;> phase_close

set_option maxHeartbeats 2000000 in
theorem boxPhase_finalEnd (P : TilePlan d m) (n : ℕ) (hK : decodeK d m n = 1)
    (hR : n % siteCount d m = 0) (h1 : P.n₀ < decodeJ d m n) (h2 : decodeJ d m n = m + 1) :
    boxPhase P n = .tile (decodeJ d m n) (siteCount d m) ∧ boxPhase P (n + 1) = .final := by
  obtain ⟨J', K', R', he, hc⟩ := boxPhase_succ_cases P n
  rw [he]
  unfold boxPhase
  generalize decodeJ d m n = J at *
  generalize decodeK d m n = K at *
  generalize n % siteCount d m = R at *
  generalize siteCount d m = N at *
  unfold phaseJKR
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
    subst_vars <;>
    split_ifs <;> phase_close

set_option maxHeartbeats 2000000 in
theorem boxPhase_clear (P : TilePlan d m) (n : ℕ) (hK : decodeK d m n = 2)
    (h1 : P.n₀ < decodeJ d m n) (h2 : decodeJ d m n ≤ m) :
    boxPhase P n = .clear (decodeJ d m n) (n % siteCount d m) ∧
      boxPhase P (n + 1) = .clear (decodeJ d m n) (n % siteCount d m + 1) := by
  obtain ⟨J', K', R', he, hc⟩ := boxPhase_succ_cases P n
  rw [he]
  unfold boxPhase
  generalize decodeJ d m n = J at *
  generalize decodeK d m n = K at *
  generalize n % siteCount d m = R at *
  generalize siteCount d m = N at *
  unfold phaseJKR
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
    subst_vars <;>
    split_ifs <;> phase_close

set_option maxHeartbeats 2000000 in
theorem boxPhase_stage (P : TilePlan d m) (n : ℕ) (hK : decodeK d m n = 3)
    (hR : n % siteCount d m = 0) (h1 : P.n₀ < decodeJ d m n) (h2 : decodeJ d m n ≤ m) :
    boxPhase P n = .clear (decodeJ d m n) (siteCount d m) ∧
      boxPhase P (n + 1) = .tile (decodeJ d m n + 1) 0 := by
  obtain ⟨J', K', R', he, hc⟩ := boxPhase_succ_cases P n
  rw [he]
  unfold boxPhase
  generalize decodeJ d m n = J at *
  generalize decodeK d m n = K at *
  generalize n % siteCount d m = R at *
  generalize siteCount d m = N at *
  unfold phaseJKR
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
    subst_vars <;>
    split_ifs <;> phase_close

theorem boxPhase_zero (P : TilePlan d m) : boxPhase P 0 = .tile (P.n₀ + 1) 0 := by
  unfold boxPhase phaseJKR
  rw [if_pos (by rw [decodeJ_zero]; exact Nat.zero_le _)]

/-- The phase at the tile operation `(j, 0, y)`. -/
theorem boxPhase_opTile (P : TilePlan d m) (j : ℕ) (y : Torus d m) (h1 : P.n₀ < j)
    (h2 : j ≤ m + 1) : boxPhase P (opIndex d m j 0 y) = .tile j (siteRank d m y) := by
  obtain ⟨e1, e2, e3⟩ := decode_opIndex (d := d) (m := m) j 0 y (by norm_num)
  have hr : opIndex d m j 0 y % siteCount d m = (siteRank d m y : ℕ) := by
    rw [← rank_decodeY, e3]
  have := (boxPhase_tile P (opIndex d m j 0 y) e2 (by rw [e1]; exact h1) (by rw [e1]; exact h2)).1
  rw [this, e1, hr]

/-- The phase at the clearing operation `(j, 2, y)`. -/
theorem boxPhase_opClear (P : TilePlan d m) (j : ℕ) (y : Torus d m) (h1 : P.n₀ < j)
    (h2 : j ≤ m) : boxPhase P (opIndex d m j 2 y) = .clear j (siteRank d m y) := by
  obtain ⟨e1, e2, e3⟩ := decode_opIndex (d := d) (m := m) j 2 y (by norm_num)
  have hr : opIndex d m j 2 y % siteCount d m = (siteRank d m y : ℕ) := by
    rw [← rank_decodeY, e3]
  have := (boxPhase_clear P (opIndex d m j 2 y) e2 (by rw [e1]; exact h1) (by rw [e1]; exact h2)).1
  rw [this, e1, hr]

/-- The phase at the first block of stage `m + 2` (the final prestate). -/
theorem boxPhase_final (P : TilePlan d m) (hnm : P.n₀ ≤ m) :
    boxPhase P (stageStartIdx d m (m + 2)) = .final := by
  have h := decode_opIndex (d := d) (m := m) (m + 2) 0 (site₀ d m) (by norm_num)
  have he : stageStartIdx d m (m + 2) = opIndex d m (m + 2) 0 (site₀ d m) := by
    unfold stageStartIdx opIndex; rw [rank_site₀]; ring
  rw [he]
  unfold boxPhase phaseJKR
  rw [h.1]
  rw [if_neg (show ¬ (m + 2 ≤ P.n₀) by omega), if_neg (show ¬ (m + 2 ≤ m + 1) by omega)]

end Arith

/-! ## Closure -/

section Closure
variable (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (n₀ : ℕ) (u : ℝ)
  (RB : ℕ → Set (RunRecord d m))

/-- **Operation `(j, k, y)` maps `A` into `A'`** along its block-local runs on the answers of
`ω`, for entering records in `RB` whose exit lies in `RB` again. -/
def OpKeeps (j k : ℕ) (y : Torus d m) (A A' : Set (RunRecord d m)) : Prop :=
  ∀ x k' (ω : RandomSources (Torus d m) (tileOrderSize P)),
    x ∈ RB (opIndex d m j k y) → x ∈ A →
    (∀ k'' < k', (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k'' ω) = false) →
    (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k' ω) = true →
    (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).exit
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k' ω) ∈
        RB (opIndex d m j k y + 1) →
    (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).exit
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k' ω) ∈ A'

/-- `OpKeeps` for entering records in `G ω` only (route R2: `ω ∉ exceptionalSet`, `x ∈ TrueValues ω`). -/
def OpKeepsZ (G : RandomSources (Torus d m) (tileOrderSize P) → Set (RunRecord d m)) (j k : ℕ)
    (y : Torus d m) (A A' : Set (RunRecord d m)) : Prop :=
  ∀ x k' (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ G ω →
    x ∈ RB (opIndex d m j k y) → x ∈ A →
    (∀ k'' < k', (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k'' ω) = false) →
    (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).halted
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k' ω) = true →
    (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).exit
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k' ω) ∈
        RB (opIndex d m j k y + 1) →
    (runOp P ts₀ cl₀ (clrOf n₀ u) j k y).exit
      (localState (tileOrderSize P) (runOp P ts₀ cl₀ (clrOf n₀ u) j k y) x k' ω) ∈ A'

theorem OpKeeps.toZ {j k : ℕ} {y : Torus d m} {A A' : Set (RunRecord d m)}
    (h : OpKeeps P ts₀ cl₀ n₀ u RB j k y A A')
    (G : RandomSources (Torus d m) (tileOrderSize P) → Set (RunRecord d m)) :
    OpKeepsZ P ts₀ cl₀ n₀ u RB G j k y A A' := fun x k' ω _ => h x k' ω

/-- The identity operations of the schedule. -/
theorem runOp_id_of_idIndex (n : ℕ) (h : IdIndex P n) :
    runOp P ts₀ cl₀ (clrOf n₀ u) (decodeJ d m n) (decodeK d m n) (decodeY d m n) =
      simpleBlock (ts₀, cl₀) id := by
  have hy : decodeY d m n = site₀ d m ↔ n % siteCount d m = 0 := decodeY_eq_site₀_iff n
  unfold IdIndex at h
  unfold runOp
  by_cases hin : P.n₀ < decodeJ d m n ∧ decodeJ d m n ≤ m + 1
  · rw [if_pos hin]
    rcases h with h | ⟨hk, hr⟩ | ⟨hk, hj⟩ | ⟨hk, hjr⟩
    · exact absurd hin h
    · rw [if_neg (show ¬ decodeK d m n = 0 by omega), if_pos hk,
        if_neg (fun h' => hr (hy.mp h'))]
    · rw [if_neg (show ¬ decodeK d m n = 0 by omega), if_neg (show ¬ decodeK d m n = 1 by omega),
        if_pos hk, if_neg (show ¬ decodeJ d m n ≤ m / 2 by omega)]
    · rw [if_neg (show ¬ decodeK d m n = 0 by omega), if_neg (show ¬ decodeK d m n = 1 by omega),
        if_neg (show ¬ decodeK d m n = 2 by omega),
        if_neg (fun h' => hjr ⟨h'.1, hy.mp h'.2⟩)]
  · rw [if_neg hin]

/-- The clearing operations of the non-clearing stages are the identity. -/
theorem opKeeps_clearId (j : ℕ) (y : Torus d m) (hjm : m / 2 < j) (A : Set (RunRecord d m)) :
    OpKeeps P ts₀ cl₀ n₀ u RB j 2 y A A := by
  intro x k ω _ hx hrun _ _
  have hop : runOp P ts₀ cl₀ (clrOf n₀ u) j 2 y = simpleBlock (ts₀, cl₀) id := by
    unfold runOp
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [hop] at hrun ⊢
  rw [simpleBlock_exit (tileOrderSize P) (ts₀, cl₀) id x k ω hrun]
  exact hx

variable (TS : ℕ → ℕ → Set (RunRecord d m)) (CL : ℕ → ℕ → Set (RunRecord d m))
  (FG : Set (RunRecord d m))

/-- **The global run invariant is closed along every block** (clearing operations only for
entering records in `G ω`). -/
theorem boxInv_closedZ (G : RandomSources (Torus d m) (tileOrderSize P) → Set (RunRecord d m))
    (hnm : P.n₀ ≤ m)
    (hRB : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      x ∈ boxInv P RB TS CL FG n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
          RB (n + 1))
    (hT : ∀ j y, P.n₀ < j → j ≤ m + 1 →
      OpKeeps P ts₀ cl₀ n₀ u RB j 0 y (TS j (siteRank d m y)) (TS j (siteRank d m y + 1)))
    (hE : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB j 1 y (TS j (siteCount d m)) (CL j 0))
    (hEF : ∀ y, y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB (m + 1) 1 y (TS (m + 1) (siteCount d m)) FG)
    (hC : ∀ j y, P.n₀ < j → j ≤ m → OpKeepsZ P ts₀ cl₀ n₀ u RB G j 2 y (CL j (siteRank d m y))
      (CL j (siteRank d m y + 1)))
    (hS : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB j 3 y (CL j (siteCount d m)) (TS (j + 1) 0)) :
    ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ G ω →
      x ∈ boxInv P RB TS CL FG n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
          boxInv P RB TS CL FG (n + 1) := by
  intro n x k ω hG hx hrun hh
  have hexRB := hRB n x k ω hx hrun hh
  refine ⟨hexRB, ?_⟩
  have hxP := hx.2
  have hnJ : opIndex d m (decodeJ d m n) (decodeK d m n) (decodeY d m n) = n := opIndex_decode n
  have hRY : ((siteRank d m (decodeY d m n) : Fin _) : ℕ) = n % siteCount d m := rank_decodeY n
  have hYs : decodeY d m n = site₀ d m ↔ n % siteCount d m = 0 := decodeY_eq_site₀_iff n
  have hK4 := decodeK_lt4 (d := d) (m := m) n
  -- identity operations
  by_cases hid : IdIndex P n
  · have hop := runOp_id_of_idIndex P ts₀ cl₀ n₀ u n hid
    have hex : (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) =
          x := by
      have hrun' : ∀ k' < k, (simpleBlock (ts₀, cl₀) id).halted
          (localState (tileOrderSize P) (simpleBlock (ts₀, cl₀) id) x k' ω) = false := by
        intro k' hk'
        have := hrun k' hk'
        unfold scheduleBlocks at this
        rwa [hop] at this
      unfold scheduleBlocks
      rw [hop]
      exact simpleBlock_exit (tileOrderSize P) (ts₀, cl₀) id x k ω hrun'
    rw [hex, boxPhase_succ_id P hnm n hid]
    exact hxP
  -- the five non-identity kinds
  unfold IdIndex at hid
  push_neg at hid
  obtain ⟨⟨hJ1, hJ2⟩, hk1, hk2, hk3⟩ := hid
  -- the block is `runOp J K Y`
  have hgen : ∀ (A A' : Set (RunRecord d m)),
      OpKeeps P ts₀ cl₀ n₀ u RB (decodeJ d m n) (decodeK d m n) (decodeY d m n) A A' →
      x ∈ A →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
          A' := by
    intro A A' hA hxA
    refine hA x k ω (by rw [hnJ]; exact hx.1) hxA hrun hh (by rw [hnJ]; exact hexRB)
  by_cases hK0 : decodeK d m n = 0
  · obtain ⟨e1, e2⟩ := boxPhase_tile P n hK0 hJ1 hJ2
    rw [e1] at hxP; rw [e2]
    have hT' := hT (decodeJ d m n) (decodeY d m n) hJ1 hJ2
    rw [hRY, ← hK0] at hT'
    exact hgen _ _ hT' hxP
  by_cases hK1 : decodeK d m n = 1
  · have hR : n % siteCount d m = 0 := hk1 hK1
    by_cases hJm : decodeJ d m n ≤ m
    · obtain ⟨e1, e2⟩ := boxPhase_end P n hK1 hR hJ1 hJm
      rw [e1] at hxP; rw [e2]
      have hE' := hE (decodeJ d m n) (decodeY d m n) hJ1 hJm (hYs.mpr hR)
      rw [← hK1] at hE'
      exact hgen _ _ hE' hxP
    · have hJe : decodeJ d m n = m + 1 := by omega
      obtain ⟨e1, e2⟩ := boxPhase_finalEnd P n hK1 hR hJ1 hJe
      rw [e1] at hxP; rw [e2]
      have hE' := hEF (decodeY d m n) (hYs.mpr hR)
      rw [← hJe] at hE'
      rw [← hK1] at hE'
      exact hgen _ _ hE' hxP
  by_cases hK2 : decodeK d m n = 2
  · have hJm2 : decodeJ d m n ≤ m := hk2 hK2
    obtain ⟨e1, e2⟩ := boxPhase_clear P n hK2 hJ1 hJm2
    rw [e1] at hxP; rw [e2]
    have hC' := hC (decodeJ d m n) (decodeY d m n) hJ1 hJm2
    rw [hRY, ← hK2] at hC'
    exact hC' x k ω hG (by rw [hnJ]; exact hx.1) hxP hrun hh (by rw [hnJ]; exact hexRB)
  have hK3 : decodeK d m n = 3 := by omega
  obtain ⟨hJm, hR⟩ := hk3 hK3
  obtain ⟨e1, e2⟩ := boxPhase_stage P n hK3 hR hJ1 hJm
  rw [e1] at hxP; rw [e2]
  have hS' := hS (decodeJ d m n) (decodeY d m n) hJ1 hJm (hYs.mpr hR)
  rw [← hK3] at hS'
  exact hgen _ _ hS' hxP

/-- **The global run invariant is closed along every block** (pathwise form). -/
theorem boxInv_closed (hnm : P.n₀ ≤ m)
    (hRB : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      x ∈ boxInv P RB TS CL FG n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
          RB (n + 1))
    (hT : ∀ j y, P.n₀ < j → j ≤ m + 1 →
      OpKeeps P ts₀ cl₀ n₀ u RB j 0 y (TS j (siteRank d m y)) (TS j (siteRank d m y + 1)))
    (hE : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB j 1 y (TS j (siteCount d m)) (CL j 0))
    (hEF : ∀ y, y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB (m + 1) 1 y (TS (m + 1) (siteCount d m)) FG)
    (hC : ∀ j y, P.n₀ < j → j ≤ m → OpKeeps P ts₀ cl₀ n₀ u RB j 2 y (CL j (siteRank d m y))
      (CL j (siteRank d m y + 1)))
    (hS : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB j 3 y (CL j (siteCount d m)) (TS (j + 1) 0)) :
    ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ boxInv P RB TS CL FG n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
          boxInv P RB TS CL FG (n + 1) :=
  fun n x k ω hx => boxInv_closedZ P ts₀ cl₀ n₀ u RB TS CL FG (fun _ => Set.univ) hnm hRB hT hE hEF
    (fun j y h1 h2 => (hC j y h1 h2).toZ _ _ _ _ _ _ _) hS n x k ω (Set.mem_univ _) hx

end Closure

/-! ## Assembly of `BoxInvariantK` -/

/-- **`BoxInvariantK` from the global run invariant** (route R2: the clearing operations are
kept off `exceptionalSet` on records with the true installed values). The phase obligations
(`hT … hS`), the initial record, the true-value closure, the goodness inclusions of the phase sets,
the all-terminal final record and the final record. -/
def boxInvariantK_of_core {n₀ : ℕ} {u E Cr cp cg c C : ℝ} (P : TilePlan d m)
    (hnm : P.n₀ ≤ m)
    (ts₀ : TileScratch d m) (cl₀ : ClearScratch d m) (rec₀ : RunRecord d m)
    (hpend₀ : rec₀.pending = ∅) (hrec₀ : rec₀.aborted = false)
    (RB : ℕ → Set (RunRecord d m)) (TS : ℕ → ℕ → Set (RunRecord d m))
    (CL : ℕ → ℕ → Set (RunRecord d m)) (FG : Set (RunRecord d m))
    (hRB : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      x ∈ boxInv P RB TS CL FG n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
          RB (n + 1))
    (hT : ∀ j y, P.n₀ < j → j ≤ m + 1 →
      OpKeeps P ts₀ cl₀ n₀ u RB j 0 y (TS j (siteRank d m y)) (TS j (siteRank d m y + 1)))
    (hE : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB j 1 y (TS j (siteCount d m)) (CL j 0))
    (hEF : ∀ y, y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB (m + 1) 1 y (TS (m + 1) (siteCount d m)) FG)
    (hC : ∀ j y, P.n₀ < j → j ≤ m → OpKeepsZ P ts₀ cl₀ n₀ u RB
      (fun ω => {x | ω ∉ exceptionalSet (d := d) (m := m) n₀ u E (tileOrderSize P) ∧
        x ∈ TrueValues n₀ u ω}) j 2 y (CL j (siteRank d m y)) (CL j (siteRank d m y + 1)))
    (hS : ∀ j y, P.n₀ < j → j ≤ m → y = site₀ d m →
      OpKeeps P ts₀ cl₀ n₀ u RB j 3 y (CL j (siteCount d m)) (TS (j + 1) 0))
    (h0 : rec₀ ∈ RB 0 ∧ rec₀ ∈ TS (P.n₀ + 1) 0)
    (hTV0 : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), rec₀ ∈ TrueValues n₀ u ω)
    (hTVop : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      x ∈ TrueValues n₀ u ω → x ∈ RB n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) =
          false) →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) =
          true →
      (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
          TrueValues n₀ u ω)
    (hAT : ∀ ω : RandomSources (Torus d m) (tileOrderSize P),
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))) rec₀
        (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
      (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))) rec₀
        (stageStartIdx d m (m + 2)) ω).aborted = false →
      ∀ i, i ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)))
        rec₀ (stageStartIdx d m (m + 2)) ω).terminal)
    (hgood : ∀ j (y : Torus d m) (T : Fin (P.cover j).cover.count), P.n₀ < j → j ≤ m + 1 →
      tileAt P j y = some T → ∀ x ∈ TS j (siteRank d m y), x ∈ TileGood C P j T)
    (hclear : ∀ j (y : Torus d m), P.n₀ < j → j ≤ m / 2 → ∀ x ∈ CL j (siteRank d m y),
      sourcesLaw (Torus d m) (tileOrderSize P)
        (localFirstFail (tileOrderSize P) (clearingBlock (d := d) (m := m) n₀ j u y) x) ≤
          ENNReal.ofReal (birthBound c j))
    (hfin : ∀ (ω : RandomSources (Torus d m) (tileOrderSize P)) (x : RunRecord d m), x ∈ FG →
      x.aborted = false →
      (∀ i, x.installed i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)) →
      ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ),
        IsDampedEndpoint s r (OAI.Anderson.scaleHeight m P.u) ∧
        TrueSchurIdentity P.n₀ P.u E (trueConfig ω) s ∧
        Fintype.card (Torus d m) ≤ 2 * s.active.card ∧
        (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧
        (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)) :
    BoxInvariantK d m n₀ u E Cr cp cg c C P where
  ts₀ := ts₀
  cl₀ := cl₀
  rec₀ := rec₀
  hpend₀ := hpend₀
  hrec₀ := hrec₀
  Inv := boxInv P RB TS CL FG
  hInv0 := ⟨h0.1, by rw [boxPhase_zero]; exact h0.2⟩
  hTV0 := hTV0
  hInv := fun n x k ω hω htv hx hrun hh =>
    boxInv_closedZ P ts₀ cl₀ n₀ u RB TS CL FG _ hnm hRB hT hE hEF hC hS n x k ω ⟨hω, htv⟩ hx
      hrun hh
  hTV := fun n x k ω _ htv hx hrun hh => hTVop n x k ω htv hx.1 hrun hh
  hfinal := fun x hx hab ω _ hinst => by
    have h2 := hx.2
    rw [boxPhase_final P hnm] at h2
    exact hfin ω x h2 hab hinst
  hAT := hAT
  hgoodT := fun j y T h1 h2 hT x hx => by
    have h := hx.2
    rw [boxPhase_opTile P j y h1 h2] at h
    exact hgood j y T h1 h2 hT x h
  hboundC := fun j y h1 h2 x hx => by
    have h := hx.2
    rw [boxPhase_opClear P j y h1 (by omega)] at h
    exact hclear j y h1 h2 x h

end AndersonAC.AgentS78
