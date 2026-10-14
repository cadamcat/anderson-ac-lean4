import AndersonAC.AgentS78.Construction.StagePhaseOp
import AndersonAC.AgentS78.Construction.StagePhaseRowInput

/-!
# The stage operation, conditional only on the inverse-row sub-contract

`stage_op_boundary_of_row`: `stage_op_boundary` with its per-record inverse-row hypothesis
discharged by `ResetRowStatement` (StagePhaseRowInput.lean).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d : ℕ}

/-- **The stage operation of the schedule produces the next stage boundary** (inverse-row
input as a separate hypothesis). -/
theorem stage_op_boundary_of_row (hd : 3 ≤ d) (hrow : ResetRowStatement d) (CA cA PA : ℝ)
    (hCA : 1 ≤ CA) (hcA : 0 < cA) (hPA : 0 ≤ PA) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C → ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {m : ℕ} (P : TilePlan d m) (E : ℝ) (ρ : ℂ) (j : ℕ) (x : RunRecord d m)
      (D : ClearPhaseData P.n₀ P.u E ρ C CA cA PA j x),
      P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → stageScale P.u (j - 1) m < t₀ →
      Kn D.old (stageScale P.u (j - 1) m) ≤ 1 / 3 → x.aborted = false →
      BoundaryInv P.n₀ P.u E ρ C j (guardMap (stageMapA P j) x) := by
  obtain ⟨CR, tr, htr, hR⟩ := hrow CA cA PA hCA hcA hPA
  obtain ⟨Cmin, hCmin, hmain⟩ := stage_op_boundary hd CA cA PA CR hCA hcA hPA
  refine ⟨Cmin, hCmin, fun C hC => ?_⟩
  obtain ⟨t₀, ht₀, h⟩ := hmain C hC
  refine ⟨min t₀ tr, lt_min ht₀ htr, fun {m} P E ρ j x D hu hj ht hK hab => ?_⟩
  refine h P E ρ j x D hu hj (ht.trans_le (min_le_left _ _)) hK (fun hKn hlag => ?_) hab
  have ht' : stageScale P.u j m < tr :=
    (stageScale_anti hu m (Nat.sub_le j 1)).trans_lt (ht.trans_le (min_le_right _ _))
  obtain ⟨old, rOld, k, I, hist, sweep, hlast, hfrozen, hIC, hIc, hIP⟩ := D
  subst hfrozen
  have := hR k _ _ x.r I hIC hIc hIP ht'
  rw [hlast] at this
  exact this hKn hlag

end AndersonAC.AgentS78
