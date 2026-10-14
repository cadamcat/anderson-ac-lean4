import AndersonAC.S78.Definitions

/-!
certificate construction: `PendingHistory` from the per-stage status and marking rules (02-state.tex:96–113,
08-history.tex:101–131). The construction only has to supply, stage by stage:

* initially (end of stage `n₀`, and before) no site is pending;
* status rule: a site pending at the end of stage `j+1` either was pending at the end of
  stage `j` with the same latest label, or was marked by a birth at stage `j+1` whose
  anchor lies within the mark radius `C 4^{(8+ν)(j+1)}` (08-history.tex:109–117);
* the clearing-stage dichotomy (08-history.tex:119–125).

The fields `latestOccurred`, `latestNearby` and `persistence` are then derived.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- **PendingHistory from the status/marking rules.** -/
def pendingHistory_of_rules {d m n₀ : ℕ} {Ω : Type}
    (pending : ℕ → Torus d m → Set Ω) (birth : BirthLabel (Torus d m) → Set Ω)
    (latest : ℕ → Torus d m → Ω → BirthLabel (Torus d m)) (C : ℝ)
    (hbefore : ∀ j x, j ≤ n₀ → pending j x = ∅)
    (hstep : ∀ j x ω, n₀ ≤ j → ω ∈ pending (j + 1) x →
      (ω ∈ pending j x ∧ latest (j + 1) x ω = latest j x ω) ∨
      ((latest (j + 1) x ω).scale = j + 1 ∧ ω ∈ birth (latest (j + 1) x ω) ∧
        physicalDistance d m x (latest (j + 1) x ω).anchor ≤
          C * (4 : ℝ) ^ ((8 + nu d) * (((j + 1 : ℕ) : ℝ)))))
    (hdich : ∀ j x ω, n₀ < j → clearingScheduled j m → ω ∈ pending j x →
      ((latest j x ω).scale = j) ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
        stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, ω ∈ pending j y) ∧
        (∀ y ∈ S, physicalDistance d m x y ≤ C * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))) :
    PendingHistory d m n₀ Ω where
  pending := pending
  birth := birth
  latest := latest
  C := C
  initial := fun x => hbefore n₀ x le_rfl
  latestOccurred := by
    intro j
    induction j with
    | zero =>
      intro x ω hω
      rw [hbefore 0 x (Nat.zero_le _)] at hω
      exact absurd hω (Set.notMem_empty ω)
    | succ j ih =>
      intro x ω hω
      by_cases hj : j + 1 ≤ n₀
      · rw [hbefore (j + 1) x hj] at hω; exact absurd hω (Set.notMem_empty ω)
      · have hnj : n₀ ≤ j := by omega
        rcases hstep j x ω hnj hω with ⟨hp, hl⟩ | ⟨hs, hb, -⟩
        · obtain ⟨h1, h2, h3⟩ := ih x ω hp
          rw [hl]; exact ⟨h1, by omega, h3⟩
        · exact ⟨by omega, by omega, hb⟩
  latestNearby := by
    intro j
    induction j with
    | zero =>
      intro x ω hω
      rw [hbefore 0 x (Nat.zero_le _)] at hω
      exact absurd hω (Set.notMem_empty ω)
    | succ j ih =>
      intro x ω hω
      by_cases hj : j + 1 ≤ n₀
      · rw [hbefore (j + 1) x hj] at hω; exact absurd hω (Set.notMem_empty ω)
      · have hnj : n₀ ≤ j := by omega
        rcases hstep j x ω hnj hω with ⟨hp, hl⟩ | ⟨hs, -, hd⟩
        · rw [hl]; exact ih x ω hp
        · rw [hs]; exact hd
  persistence := by
    intro j
    induction j with
    | zero => intro r x ω _ hr; omega
    | succ j ih =>
      intro r x ω hr hrj hω hsc
      have hnj : n₀ ≤ j := by omega
      rcases hstep j x ω hnj hω with ⟨hp, hl⟩ | ⟨hs, -, -⟩
      · rw [hl] at hsc
        by_cases hjr : r = j
        · subst hjr; exact hp
        · exact ih r x ω hr (by omega) hp hsc
      · omega
  dichotomy := hdich

end AndersonAC.AgentS78
