import AndersonAC.AgentS78.Construction.ClearingFacts
import AndersonAC.AgentS78.Construction.Reached

/-!
# Deterministic halting of the clearing block

Every clearing attempt halts within `heatLimit t_j + |core| + 2` operations, for **every**
answer sequence: each heat increases `step` (FAIL at the heat limit, 06-clearing), the core
phase removes one core site per query, and the remaining actions latch an outcome. Potential:
`Φ = 0` once halted, `|coreLeft| + 1` in the core phase, `(heatLimit − step) + |core| + 2` in the
heat phase. Hence the field `hchalt` of `RunOpsInputs` with the box constant
`clearingHaltBound u m = Σ_{j ≤ m} heatLimit t_j + |Torus d m| + 2`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)

section ClearingHalt
variable {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (y : Torus d m)

/-- The halting potential of a clearing state. -/
def clrPotential (s : RunRecord d m × ClearScratch d m) : ℕ :=
  if s.2.failed = true ∨ s.2.done = true then 0
  else if s.2.corePhase = true then s.2.coreLeft.card + 1
  else (AndersonAC.S6.heatLimit (stageScale u j m) - s.2.step) + s.2.core.card + 2

/-- In the core phase the action is a core query or the finish. -/
theorem actionOf_corePhase (rc : RunRecord d m) (sc : ClearScratch d m)
    (hf : sc.failed = false) (hd : sc.done = false) (hc : sc.corePhase = true) :
    (∃ p h, actionOf (d := d) (m := m) j u rc sc = .coreQuery p h) ∨
      actionOf (d := d) (m := m) j u rc sc = .finish := by
  unfold actionOf
  rw [if_neg (by simp [hf]), if_neg (by simp [hd])]
  by_cases h3 : sc.core = ∅
  · rw [if_pos h3]; exact Or.inr rfl
  rw [if_neg h3, dif_pos hc]
  split
  · exact Or.inl ⟨_, hc, rfl⟩
  · exact Or.inr rfl

theorem clrPotential_pos (s : RunRecord d m × ClearScratch d m)
    (hnh : clearingHalted s = false) : 0 < clrPotential j u s := by
  simp only [clearingHalted, Bool.or_eq_false_iff] at hnh
  unfold clrPotential
  rw [if_neg (by simp [hnh.1, hnh.2])]
  split_ifs <;> omega

/-- **The potential decreases** at every operation of a running clearing state. -/
theorem clrPotential_lt (s : RunRecord d m × ClearScratch d m) (a : Answer (Torus d m))
    (hnh : clearingHalted s = false) (hcl : s.2.coreLeft ⊆ s.2.core) :
    clrPotential j u (clearingUpdate (d := d) (m := m) n₀ j u s a) < clrPotential j u s := by
  have hpos := clrPotential_pos j u s hnh
  simp only [clearingHalted, Bool.or_eq_false_iff] at hnh
  obtain ⟨hf, hd⟩ := hnh
  have hnot : ¬ (s.2.failed = true ∨ s.2.done = true) := by simp [hf, hd]
  have hΦ : clrPotential j u s = if s.2.corePhase = true then s.2.coreLeft.card + 1
      else (AndersonAC.S6.heatLimit (stageScale u j m) - s.2.step) + s.2.core.card + 2 := by
    unfold clrPotential; rw [if_neg hnot]
  have hcard : s.2.coreLeft.card ≤ s.2.core.card := Finset.card_le_card hcl
  unfold clearingUpdate
  dsimp only
  rw [if_neg hnot]
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po =>
    show clrPotential j u (s.1, { s.2 with failed := true, inspected := _ }) < _
    unfold clrPotential; simp only [true_or, if_true]; exact hpos
  | finish =>
    show clrPotential j u (s.1, { s.2 with done := true }) < _
    unfold clrPotential; simp only [or_true, if_true]; exact hpos
  | coreReady =>
    have hcp : s.2.corePhase = false := by
      by_contra hc
      rcases actionOf_corePhase j u s.1 s.2 hf hd (by simpa using hc) with ⟨p, _, hp⟩ | hp <;>
        rw [hact] at hp <;> cases hp
    show clrPotential j u (s.1, { s.2 with corePhase := true }) < _
    rw [hΦ, if_neg (by simp [hcp])]
    unfold clrPotential
    simp only [hf, hd, Bool.false_eq_true, or_self, if_false, if_true]
    omega
  | coreQuery p hcp =>
    have hmem := actionOf_coreQuery_mem j u s.1 s.2 p hcp hact
    rw [hΦ, if_pos hcp]
    unfold clrPotential
    dsimp only
    have := Finset.card_erase_of_mem hmem
    have hpos' : 0 < s.2.coreLeft.card := Finset.card_pos.mpr ⟨p, hmem⟩
    split_ifs <;> omega
  | heat p hg =>
    have hcp : s.2.corePhase = false := by
      by_contra hc
      rcases actionOf_corePhase j u s.1 s.2 hf hd (by simpa using hc) with ⟨q, _, hq⟩ | hq <;>
        rw [hact] at hq <;> cases hq
    rw [hΦ, if_neg (by simp [hcp])]
    dsimp only
    split_ifs with h1 h2 h3 h4
    all_goals (unfold clrPotential; dsimp only)
    all_goals (simp only [hf, hd, hcp, true_or, or_true, if_true, Bool.false_eq_true, or_self,
      if_false] <;> omega)

/-- The box constant of the deterministic clearing halting bound. -/
def clearingHaltBound (d m : ℕ) (u : ℝ) : ℕ :=
  (∑ j' ∈ Finset.range (m + 1), AndersonAC.S6.heatLimit (stageScale u j' m)) +
    Fintype.card (Torus d m) + 2

theorem clrPotential_init_le (x : RunRecord d m) :
    clrPotential j u (x, clearInitScratch (d := d) (m := m) j u y x) ≤ clearingHaltBound d m u := by
  unfold clrPotential clearingHaltBound
  by_cases hsch : clearingScheduled j m
  · have hH : AndersonAC.S6.heatLimit (stageScale u j m) ≤
        ∑ j' ∈ Finset.range (m + 1), AndersonAC.S6.heatLimit (stageScale u j' m) :=
      Finset.single_le_sum (f := fun j' => AndersonAC.S6.heatLimit (stageScale u j' m))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by
          have : j ≤ m / 2 := hsch
          omega))
    have hc : (x, clearInitScratch (d := d) (m := m) j u y x).2.core.card ≤
        Fintype.card (Torus d m) := Finset.card_le_univ _
    have hc' : (x, clearInitScratch (d := d) (m := m) j u y x).2.coreLeft.card ≤
        Fintype.card (Torus d m) := Finset.card_le_univ _
    have hst : (x, clearInitScratch (d := d) (m := m) j u y x).2.step = 0 := rfl
    split_ifs <;> omega
  · have hd : (clearInitScratch (d := d) (m := m) j u y x).done = true :=
      init_done_true (j := j) (u := u) (x := y) x (Or.inr (Or.inl hsch))
    rw [if_pos (Or.inr hd)]
    exact Nat.zero_le _

/-- **Deterministic halting** (`hchalt` of `RunOpsInputs`): from every record and for every
sample, the clearing block has halted by step `clearingHaltBound d m u`. -/
theorem clr_halts (M : ℕ → ℕ) (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M)
    (hk : clearingHaltBound d m u ≤ k) :
    ω ∉ notHalted M (clearingBlock (d := d) (m := m) n₀ j u y) x k := by
  intro hω
  have hrun : ∀ i ≤ k, clearingHalted
      (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω) = false :=
    fun i hi => hω i hi
  have hdec : ∀ i ≤ k,
      clrPotential j u (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω) + i ≤
        clrPotential j u (x, clearInitScratch (d := d) (m := m) j u y x) := by
    intro i
    induction i with
    | zero => intro _; simp; rfl
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have hlt := clrPotential_lt n₀ j u
        (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω)
        (localAnswer (Torus d m) M
          (machineRun (Torus d m) M ((clearingBlock (d := d) (m := m) n₀ j u y).enter x)
            (clearingBlock (d := d) (m := m) n₀ j u y).next
            (clearingBlock (d := d) (m := m) n₀ j u y).update i ω).2
          ((clearingBlock (d := d) (m := m) n₀ j u y).next
            (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω)) ω)
        (hrun i (by omega)) (clr_local_inv n₀ j u y M x ω i).2.2
      have hs : localState M (clearingBlock (d := d) (m := m) n₀ j u y) x (i + 1) ω =
          clearingUpdate (d := d) (m := m) n₀ j u
            (localState M (clearingBlock (d := d) (m := m) n₀ j u y) x i ω) _ :=
        localState_succ M _ x i ω
      rw [hs]
      omega
  have hk' := hdec k le_rfl
  have hinit := clrPotential_init_le j u y x
  have hpos := clrPotential_pos j u _ (hrun k le_rfl)
  omega

end ClearingHalt

end AndersonAC.AgentS78
