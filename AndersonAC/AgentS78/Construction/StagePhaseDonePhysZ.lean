import AndersonAC.AgentS78.Construction.ClearingDonePhys
import AndersonAC.AgentS78.Construction.ClearingTrueValues
import AndersonAC.AgentS78.Construction.StagePhaseTrueBlock
import AndersonAC.AgentS78.Construction.StagePhasePkgOps
import AndersonAC.AgentS6Construct.SelectionFacts
import AndersonAC.AgentS6.CapTelescope

/-!
# Regular pivots outside the exceptional set

Along the answers of `ω ∉ exceptionalSet`, from a record `x` with true installed values whose
inactive sites are terminal, every update of the clearing block is a regular elimination step
(`ClrStepRegular`):

* a heat pivot is still active: a heat requires `¬ xReady`, which keeps the ridge positive
  (`RidgeOK`); at a positive ridge and with `¬ xReady` the maximal leverage is positive, and a
  site of positive leverage has a nonzero cross row, so it is active;
* the pivot `Mnum p p + ξ` is nonzero: the Schur invariant identifies it as the Schur
  pivot of the shifted installed values, and the two eliminated blocks involved are principal
  blocks of the true matrix `H_λ(ω) − E` (eliminated sites carry their true values by
  `ClearingTrueValues.CTV`, the new pivot by the true answer), invertible off `exceptionalSet`.

Hence `clearingDonePhys_of_pivots` gives **`clearingDonePhysZ_proof : ClearingDonePhysZ d`**.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Answer)

variable {d m : ℕ}

/-! ## Leverage facts -/

section Lev
variable {R B : Type} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]

/-- `chooseRidge` stays positive while some projection weight exceeds `2 l`. -/
theorem chooseRidge_pos_of_large [Nonempty R] (C : Matrix R B ℂ) (l τ : ℝ) (hl : 0 < l) (hτ : 0 < τ)
    (hlarge : 2 * l < AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C)) :
    0 < AndersonAC.S6.chooseRidge C l τ := by
  by_cases h : AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ) < 2 * l
  · exact (AndersonAC.AgentS6Construct.chooseRidge_bounds C l τ hl hτ (by linarith) hlarge).1
  · unfold AndersonAC.S6.chooseRidge; rw [if_neg h]; exact hτ

/-- At a positive ridge, the maximal leverage is positive while some projection weight exceeds
`2 l > 0`. -/
theorem maxWeight_leverage_pos (C : Matrix R B ℂ) (l τ : ℝ) (hl : 0 < l) (hτ : 0 < τ)
    (hlarge : 2 * l < AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight C)) :
    0 < AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ) := by
  obtain ⟨h0, h1, -⟩ := AndersonAC.S6.ridge_threshold C l hl hlarge
  set τ0 := AndersonAC.S6.ridgeThreshold C l
  have hex : ∃ i, 0 < AndersonAC.S6.leverage C τ0 i := by
    by_contra hn
    push_neg at hn
    have hz : AndersonAC.S6.maxWeight (AndersonAC.S6.leverage C τ0) = 0 := by
      unfold AndersonAC.S6.maxWeight
      have : Finset.univ.sup (fun i => Real.toNNReal (AndersonAC.S6.leverage C τ0 i)) = 0 := by
        refine le_antisymm (Finset.sup_le fun i _ => ?_) zero_le
        rw [Real.toNNReal_of_nonpos (hn i)]
      rw [this]; rfl
    linarith
  obtain ⟨i, hi⟩ := hex
  have hrow : ∃ b, C i b ≠ 0 := by
    by_contra hr
    push_neg at hr
    rw [AndersonAC.AgentS6.leverage_zero_row C τ0 i hr] at hi
    exact lt_irrefl _ hi
  have hsa := (AndersonAC.S6.ridge_continuous_monotone C i).2.2 hrow
  have hlt : AndersonAC.S6.leverage C (2 * τ) i < AndersonAC.S6.leverage C τ i :=
    hsa (Set.mem_Ioi.mpr hτ) (Set.mem_Ioi.mpr (by linarith)) (by linarith)
  have hnn := AndersonAC.AgentS6.leverage_nonneg C (by linarith : (0 : ℝ) ≤ 2 * τ) i
  exact lt_of_lt_of_le (by linarith) (AndersonAC.AgentS6.le_maxWeight _ i)

end Lev

/-- Rows of the cross matrix outside the active set vanish. -/
theorem xCross_row_zero (t : ℝ) (r : Torus d m → ℂ) (A : Finset (Torus d m))
    (Msub : Matrix {i // i ∈ A} {i // i ∈ A} ℝ) (B : Finset (Torus d m)) (i : Torus d m)
    (hi : i ∉ A) (b : {b // b ∈ B}) : xCross t r A Msub B i b = 0 := by
  simp [xCross, hi]

theorem large_of_not_ready {t : ℝ} {r : Torus d m → ℂ} {A : Finset (Torus d m)}
    {Msub : Matrix {i // i ∈ A} {i // i ∈ A} ℝ} {B : Finset (Torus d m)}
    (h : ¬ xReady t r A Msub B) :
    2 * AndersonAC.S6.leverageScale t <
      AndersonAC.S6.maxWeight (AndersonAC.S6.projectionWeight (xCross t r A Msub B)) := by
  unfold xReady at h
  push_neg at h
  obtain ⟨i, hi⟩ := h
  exact lt_of_lt_of_le hi (AndersonAC.AgentS6.le_maxWeight _ i)

/-! ## The heat action -/

/-- **A heat action**: not failed, before the core phase, not ready, at the candidate pivot. -/
theorem actionOf_heat_ready (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc : ClearScratch d m)
    (p : Torus d m) (hg : guardHolds (d := d) (m := m) j sc.core (coupledActive rc) rc.terminal p)
    (h : actionOf (d := d) (m := m) j u rc sc = .heat p hg) :
    sc.failed = false ∧ sc.corePhase = false ∧
      ¬ xReady (stageScale u j m) rc.r sc.active (restrictM sc.active sc.Mnum) sc.core ∧
      candPivot rc.r sc (stageScale u j m) sc.ridge = some p := by
  unfold actionOf at h
  by_cases h1 : sc.failed = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : sc.done = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : sc.core = ∅
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases hc : sc.corePhase = true
  · rw [dif_pos hc] at h
    split at h <;> cases h
  rw [dif_neg hc] at h
  revert h
  dsimp only
  split_ifs with hA hB hS hW hX
  all_goals first
    | (intro h; cases h; done)
    | skip
  split
  · next p' hp' =>
    split_ifs with hg' hpc
    · intro h; cases h
    · intro h; cases h
      exact ⟨by simpa using h1, by simpa using hc, hX, hp'⟩
    · intro h; cases h
  · intro h; cases h

/-- **A heat pivot of a positive-ridge (or ready) state is active.** -/
theorem heat_pivot_active (j : ℕ) (u : ℝ) (hu : 0 < u) (rc : RunRecord d m)
    (sc : ClearScratch d m) (p : Torus d m)
    (hg : guardHolds (d := d) (m := m) j sc.core (coupledActive rc) rc.terminal p)
    (h : actionOf (d := d) (m := m) j u rc sc = .heat p hg)
    (hR : 0 < sc.ridge ∨
      xReady (stageScale u j m) rc.r sc.active (restrictM sc.active sc.Mnum) sc.core) :
    p ∈ sc.active := by
  obtain ⟨-, -, hnr, hcand⟩ := actionOf_heat_ready j u rc sc p hg h
  have ht : 0 < stageScale u j m := by unfold stageScale; positivity
  have hl : 0 < AndersonAC.S6.leverageScale (stageScale u j m) := by
    unfold AndersonAC.S6.leverageScale; exact Real.rpow_pos_of_pos ht _
  have hτ : 0 < sc.ridge := hR.resolve_right hnr
  have hpos := maxWeight_leverage_pos _ _ _ hl hτ (large_of_not_ready hnr)
  unfold candPivot scratchWeights xWeights at hcand
  have hp := ((leastMaximizer_eq_some (siteRank d m) _ p).mp hcand).1
  by_contra hpa
  rw [AndersonAC.AgentS6.leverage_zero_row _ _ p
    (xCross_row_zero _ _ _ _ _ p hpa)] at hp
  linarith

/-! ## The ridge invariant -/

/-- Before the core phase and without failure, the ridge is positive or the state is ready. -/
def RidgeOK (j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m) : Prop :=
  s.2.corePhase = false → s.2.failed = false →
    0 < s.2.ridge ∨
      xReady (stageScale u j m) s.1.r s.2.active (restrictM s.2.active s.2.Mnum) s.2.core

theorem ridgeOK_enter (n₀ j : ℕ) (u : ℝ) (hu : 0 < u) (y : Torus d m) (x : RunRecord d m) :
    RidgeOK j u ((clearingBlock (d := d) (m := m) n₀ j u y).enter x) := by
  intro _ _
  have ht : 0 < stageScale u j m := by unfold stageScale; positivity
  have hl : 0 < AndersonAC.S6.leverageScale (stageScale u j m) := by
    unfold AndersonAC.S6.leverageScale; exact Real.rpow_pos_of_pos ht _
  by_cases hX : xReady (stageScale u j m) x.r x.endpoint.active
    (restrictM x.endpoint.active (fun i k => (x.endpoint.M i k).re))
    (theCore (d := d) (m := m) j u y x)
  · exact Or.inr hX
  · left
    exact chooseRidge_pos_of_large _ _ _ hl (zpow_pos hl _) (large_of_not_ready hX)

theorem ridgeOK_step (n₀ j : ℕ) (u : ℝ) (hu : 0 < u) (s : RunRecord d m × ClearScratch d m)
    (a : Answer (Torus d m)) (hs : RidgeOK j u s) :
    RidgeOK j u (clearingUpdate (d := d) (m := m) n₀ j u s a) := by
  classical
  by_cases hfd : s.2.failed = true ∨ s.2.done = true
  · rw [update_halted_fixed _ _ hfd]; exact hs
  have ht : 0 < stageScale u j m := by unfold stageScale; positivity
  have hl : 0 < AndersonAC.S6.leverageScale (stageScale u j m) := by
    unfold AndersonAC.S6.leverageScale; exact Real.rpow_pos_of_pos ht _
  unfold RidgeOK clearingUpdate
  dsimp only
  rw [if_neg hfd]
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po => intro _ h; simp at h
  | coreReady => intro h; simp at h
  | heat p hg =>
    obtain ⟨hf0, hcp0, hnr, -⟩ := actionOf_heat_ready j u s.1 s.2 p hg hact
    have hτ : 0 < s.2.ridge := (hs hcp0 hf0).resolve_right hnr
    dsimp only
    split_ifs <;> first
      | (intro _ h; simp at h; done)
      | (intro h; simp at h; done)
      | (intro _ _; left
         exact chooseRidge_pos_of_large _ _ _ hl hτ (large_of_not_ready (by assumption)))
  | coreQuery y hc => intro h; simp [hc] at h
  | finish => intro h1 h2; exact hs h1 h2

theorem ridgeOK_all (n₀ j : ℕ) (u : ℝ) (hu : 0 < u) (y : Torus d m) {M : ℕ → ℕ}
    (x : RunRecord d m) (ω : RandomSources (Torus d m) M) (k : ℕ) :
    RidgeOK j u (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω) := by
  induction k with
  | zero => exact ridgeOK_enter n₀ j u hu y x
  | succ k ih =>
    rw [localState_succ]
    exact ridgeOK_step n₀ j u hu _ _ ih

/-! ## Eliminated sites -/

/-- An eliminated site is a heat pivot or a cleared core site. -/
def ElimOK (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m) : Prop :=
  ∀ i ∈ x.endpoint.active, i ∉ s.2.active → i ∈ s.2.inspected ∨ i ∉ s.2.coreLeft

theorem elimOK_step (n₀ j : ℕ) (u : ℝ) (x : RunRecord d m) (s : RunRecord d m × ClearScratch d m)
    (a : Answer (Torus d m)) (ih : ElimOK x s) :
    ElimOK x (clearingUpdate (d := d) (m := m) n₀ j u s a) := by
  classical
  by_cases hfd : s.2.failed = true ∨ s.2.done = true
  · rw [update_halted_fixed _ _ hfd]; exact ih
  have hsh := clearingUpdate_shape_ctv n₀ j u s a hfd
  intro i hi hn
  rcases hsh.cases with ⟨-, ha, hl, hi'⟩ | ⟨-, -, ha, hi', -, hl⟩ |
      ⟨p, -, -, ha, hi', -, -, hl⟩ | ⟨y', -, -, -, ha, hi', -, hl, -⟩ | ⟨-, -, ha, hi', -, hl⟩
  · rw [ha] at hn; rw [hl]
    rcases ih i hi hn with h | h
    · exact Or.inl (hi' h)
    · exact Or.inr h
  · rw [ha] at hn; rw [hl, hi']; exact ih i hi hn
  · rw [ha] at hn; rw [hl, hi']
    by_cases hip : i = p
    · subst hip; exact Or.inl (Finset.mem_insert_self _ _)
    · have : i ∉ s.2.active := fun h' => hn (Finset.mem_erase.mpr ⟨hip, h'⟩)
      rcases ih i hi this with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr h
  · rw [ha] at hn; rw [hl, hi']
    by_cases hiy : i = y'
    · subst hiy; exact Or.inr (Finset.notMem_erase _ _)
    · have : i ∉ s.2.active := fun h' => hn (Finset.mem_erase.mpr ⟨hiy, h'⟩)
      rcases ih i hi this with h | h
      · exact Or.inl h
      · exact Or.inr (fun h' => h (Finset.mem_of_mem_erase h'))
  · rw [ha] at hn; rw [hl, hi']; exact ih i hi hn

theorem elimOK_all (n₀ j : ℕ) (u : ℝ) (y : Torus d m) {M : ℕ → ℕ}
    (x : RunRecord d m) (ω : RandomSources (Torus d m) M) (k : ℕ) :
    ElimOK x (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω) := by
  induction k with
  | zero =>
    intro i hi hn
    exact absurd hi (by simpa [localState_zero, clearingBlock, clearInitScratch] using hn)
  | succ k ih =>
    rw [localState_succ]
    exact elimOK_step n₀ j u x _ _ ih

/-! ## True entries -/

theorem installedShifted_offdiag_true (n₀ : ℕ) (u E : ℝ) {M : ℕ → ℕ}
    (ω : RandomSources (Torus d m) M) (x : RunRecord d m) (i k : Torus d m) (hik : i ≠ k) :
    installedShifted E x i k = trueShifted n₀ u E (trueConfig ω) i k := by
  simp only [installedShifted, trueShifted, Matrix.sub_apply, Matrix.add_apply,
    OAI.Anderson.periodicHamiltonian, Matrix.diagonal_apply]
  simp [hik]

theorem installedShifted_diag_true (n₀ : ℕ) (u E : ℝ) {M : ℕ → ℕ}
    (ω : RandomSources (Torus d m) M) (x : RunRecord d m) (i : Torus d m) (v : ℝ)
    (hv : x.installed i + v = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)) :
    installedShifted E x i i + ((v : ℝ) : ℂ) = trueShifted n₀ u E (trueConfig ω) i i := by
  simp only [installedShifted, trueShifted, Matrix.sub_apply, Matrix.add_apply,
    OAI.Anderson.periodicHamiltonian, Matrix.diagonal_apply]
  have hv' : ((x.installed i : ℝ) : ℂ) + ((v : ℝ) : ℂ) =
      ((OAI.Anderson.scaleCoupling n₀ u : ℝ) : ℂ) * (((trueConfig ω i : ℝ)) : ℂ) := by
    exact_mod_cast hv
  simp only [if_true, Complex.ofReal_zero, zero_mul, add_zero]
  linear_combination hv'

/-- A shifted installed matrix with a real diagonal correction is true off `A` when the corrected
diagonal values are. -/
theorem shifted_true_off (n₀ : ℕ) (u E : ℝ) {M : ℕ → ℕ} (ω : RandomSources (Torus d m) M)
    (x : RunRecord d m) (D : Torus d m → ℝ) (A : Finset (Torus d m))
    (hD : ∀ i, i ∉ A →
      x.installed i + D i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)) :
    ∀ i k, i ∉ A → k ∉ A →
      (installedShifted E x + Matrix.diagonal (fun i => ((D i : ℝ) : ℂ))) i k =
        trueShifted n₀ u E (trueConfig ω) i k := by
  intro i k hi _
  rw [Matrix.add_apply, Matrix.diagonal_apply]
  by_cases hik : i = k
  · subst hik; rw [if_pos rfl]; exact installedShifted_diag_true n₀ u E ω x i (D i) (hD i hi)
  · rw [if_neg hik, add_zero]; exact installedShifted_offdiag_true n₀ u E ω x i k hik

/-- **The entering record's eliminated block is invertible** (inactive sites are terminal). -/
theorem terminalInvertible_of_true (n₀ : ℕ) (u E : ℝ) {M : ℕ → ℕ}
    (ω : RandomSources (Torus d m) M) (hω : ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M)
    (x : RunRecord d m) (hx : x ∈ TrueValues n₀ u ω) (hab : x.aborted = false)
    (hall : ∀ i, i ∈ x.endpoint.active ∨ i ∈ x.terminal) : TerminalInvertible E x := by
  have h := offB_unit_of_true n₀ u E ω hω
    (installedShifted E x + Matrix.diagonal (fun i => (((0 : Torus d m → ℝ) i : ℝ) : ℂ)))
    x.endpoint.active (shifted_true_off n₀ u E ω x 0 _ (fun i hi => by
      simp only [Pi.zero_apply, add_zero]
      exact (hx hab).1 i ((hall i).resolve_left hi)))
  have h0 : installedShifted E x + Matrix.diagonal (fun i => (((0 : Torus d m → ℝ) i : ℝ) : ℂ)) =
      installedShifted E x := by
    ext i k; simp
  rw [h0] at h
  exact h

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Answer Query binaryPrefix)

variable {d m : ℕ}

/-! ## Regular steps off the exceptional set -/

/-- **Every step of the clearing block is regular** along the answers of `ω ∉ exceptionalSet`. -/
theorem clrStepRegular_true (n₀ j : ℕ) (u E : ℝ) (hu : 0 < u) (y : Torus d m) {M : ℕ → ℕ}
    (ω : RandomSources (Torus d m) M) (hω : ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M)
    (x : RunRecord d m) (hx : x ∈ TrueValues n₀ u ω) (hab : x.aborted = false)
    (hall : ∀ i, i ∈ x.endpoint.active ∨ i ∈ x.terminal) (hP : PhysicalIdentity E x)
    (s : RunRecord d m × ClearScratch d m) (hs : ClrRegReach n₀ j u y x s)
    (hctv : CTV n₀ j u y ω x s) (hR : RidgeOK j u s) (hE : ElimOK x s)
    (hh : (clearingBlock (d := d) (m := m) n₀ j u y).halted s = false)
    (L : List (Query (Torus d m))) :
    ClrStepRegular n₀ j u s
      (localAnswer (Torus d m) M L (clearingNext (d := d) (m := m) n₀ j u s) ω) := by
  classical
  have hf : s.2.failed = false := by
    simp only [clearingBlock, clearingHalted, Bool.or_eq_false_iff] at hh; exact hh.1
  have hT := terminalInvertible_of_true n₀ u E ω hω x hx hab hall
  obtain ⟨-, -, hB⟩ := clrRegReach_schur hs hP hT hf
  have hI := schurInv_reach n₀ j u E y x hP hT s hs
  obtain ⟨htv, hcv⟩ := hx hab
  have helim : ∀ i, i ∉ s.2.active →
      x.installed i + (if i ∈ x.endpoint.active \ s.2.active then s.2.resids i else 0) =
        OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ) := by
    intro i hi
    by_cases hia : i ∈ x.endpoint.active
    · rw [if_pos (Finset.mem_sdiff.mpr ⟨hia, hi⟩)]
      rcases hE i hia hi with h | h
      · exact hctv.insp hf i h
      · rcases Finset.mem_union.mp (hctv.gone i hia hi) with hc | hc
        · exact hctv.coreV hf i hc h
        · exact hctv.insp hf i hc
    · rw [if_neg (fun h => hia (Finset.mem_sdiff.mp h).1), add_zero]
      exact htv i ((hall i).resolve_left hia)
  have hpiv : ∀ p ∈ s.2.active, ∀ ξ : ℝ,
      x.installed p + ξ = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω p : ℝ) →
      s.2.Mnum p p + ξ ≠ 0 := by
    intro p hp ξ hξ
    apply clrRegReach_pivot_ne_zero hs hP hT hf hp ξ
    let D : Torus d m → ℝ := fun i =>
      (if i ∈ x.endpoint.active \ s.2.active then s.2.resids i else 0) + (if i = p then ξ else 0)
    have hmat : scratchShifted E x s.2 + Matrix.diagonal (Pi.single p (ξ : ℂ)) =
        installedShifted E x + Matrix.diagonal (fun i => ((D i : ℝ) : ℂ)) := by
      rw [hB]
      ext i k
      simp only [Matrix.add_apply, Matrix.diagonal_apply, Pi.single_apply, D]
      by_cases hik : i = k
      · subst hik
        simp only [if_true]
        split_ifs <;> push_cast <;> ring
      · simp [hik]
    rw [hmat]
    refine offB_unit_of_true n₀ u E ω hω _ _ (shifted_true_off n₀ u E ω x D _ (fun i hi => ?_))
    by_cases hip : i = p
    · subst hip
      have : i ∉ x.endpoint.active \ s.2.active := fun h => (Finset.mem_sdiff.mp h).2 hp
      simp only [D, if_neg this, zero_add]
      exact hξ
    · have hia : i ∉ s.2.active := fun h => hi (Finset.mem_erase.mpr ⟨hip, h⟩)
      simp only [D, if_neg hip, add_zero]
      exact helim i hia
  rcases s with ⟨rc, sc⟩
  have h1 : rc = x := hctv.fst
  subst h1
  unfold ClrStepRegular
  split
  · next p hg hact =>
    have hpa : p ∈ sc.active := heat_pivot_active j u hu rc sc p hg hact
      (hR (actionOf_heat_ready j u rc sc p hg hact).2.1 hf)
    refine ⟨hpa, ?_⟩
    have hn : clearingNext (d := d) (m := m) n₀ j u (rc, sc) =
        Query.trueSuffix p (rc.prefixLength p) := by
      unfold clearingNext; rw [hact]
    rw [hn]
    apply hpiv p hpa
    rw [residOfAnswer_true, hcv p (coupledActive_not_pending rc hg.1) hg.2.1, lamV_eq_ctv,
      AndersonAC.S2.binary_prefix_suffix _ (rc.prefixLength p)]
    rfl
  · next yq hc hact =>
    have hyl := actionOf_coreQuery_mem j u rc sc yq hc hact
    have hya : yq ∈ sc.active := by
      rw [← hI.post hc] at hyl; exact (Finset.mem_inter.mp hyl).2
    have hn : clearingNext (d := d) (m := m) n₀ j u (rc, sc) = Query.trueSuffix yq 0 := by
      unfold clearingNext; rw [hact]
    rw [hn]
    apply hpiv yq hya
    rw [residOfAnswer_true, lamV_eq_ctv, AndersonAC.S2.binary_prefix_suffix _ 0]
    simp [binaryPrefix]; rfl
  · trivial

/-- **Regular reachability along the answers of `ω`.** -/
theorem clrRegReach_local (n₀ j : ℕ) (u E : ℝ) (hu : 0 < u) (y : Torus d m) {M : ℕ → ℕ}
    (ω : RandomSources (Torus d m) M) (hω : ω ∉ exceptionalSet (d := d) (m := m) n₀ u E M)
    (x : RunRecord d m) (hx : x ∈ TrueValues n₀ u ω) (hab : x.aborted = false)
    (hall : ∀ i, i ∈ x.endpoint.active ∨ i ∈ x.terminal) (hP : PhysicalIdentity E x) :
    ∀ k, (∀ k' < k, (clearingBlock (d := d) (m := m) n₀ j u y).halted
        (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k' ω) = false) →
      ClrRegReach n₀ j u y x (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x k ω) := by
  intro k
  induction k with
  | zero => intro _; exact ClrRegReach.enter
  | succ k ih =>
    intro hh
    have hs := ih (fun k' hk' => hh k' (by omega))
    rw [localState_succ]
    exact ClrRegReach.step _ _ hs (hh k (by omega))
      (clrStepRegular_true n₀ j u E hu y ω hω x hx hab hall hP _ hs
        (ctv_all n₀ j u y ω x hx hab k) (ridgeOK_all n₀ j u hu y x ω k) (elimOK_all n₀ j u y x ω k)
        (hh k (by omega)) _)

/-- **The physical identity after a DONE clearing, off the exceptional set.** -/
theorem clearingDonePhysZ_proof (d : ℕ) : ClearingDonePhysZ d := by
  intro m n₀ j u E y M ω x k hu hω hx hab hsch hall hP hh hne hf hdn
  exact (clearingDonePhys_of_pivots d n₀ j u E y x _
    (clrRegReach_local n₀ j u E hu y ω hω x hx hab hall hP k hh) hab hsch hne hf hdn hP
    (terminalInvertible_of_true n₀ u E ω hω x hx hab hall)).1

end AndersonAC.AgentS78
