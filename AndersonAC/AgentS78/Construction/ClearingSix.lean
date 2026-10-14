import AndersonAC.AgentS78.Construction.BoxSplit

/-!
# Clearing-block facts

`clearingFailGuarded_proof`, `clearingCoreRadius_proof`, and `clearingEligibleIntro_proof`
establish the three clearing-block properties used by `BoxAssembly.lean`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem guardedCand_some {j : ℕ} {rec : RunRecord d m} {sc : ClearScratch d m}
    {o : Option (Torus d m)} {p : Torus d m} (h : guardedCand j rec sc o = some p) :
    guardHolds (d := d) (m := m) j sc.core (coupledActive rec) rec.terminal p := by
  unfold guardedCand at h
  cases o with
  | none => cases h
  | some q =>
    simp only [Option.bind_some] at h
    split_ifs at h with hg
    · cases h; exact hg

theorem clearingFailGuarded_proof (d m : ℕ) : ClearingFailGuarded d m := by
  intro j u rc sc p h
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
  split_ifs
  all_goals first
    | (intro h; cases h; done)
    | (intro h; exact guardedCand_some (ClearingAction.fail.inj h))
    | (split <;> (try split_ifs) <;> intro h <;> first
        | (cases h; done)
        | (cases h; assumption))

theorem clearingCoreRadius_proof (d m : ℕ) : ClearingCoreRadius d m := by
  intro j u y x v hv
  obtain ⟨B, _, hel, hvB⟩ := mem_theCore j u y x hv
  exact hel.2.2.2 v hvB

theorem clearingEligibleIntro_proof (d m : ℕ) : ClearingEligibleIntro d m := by
  intro j u y B hy hmin hcard hrad
  exact ⟨hy, ⟨hy, hmin⟩, hcard, hrad⟩

/-- Uniform certificate input from the tile disciplines, clearing-block
measurability, tile-trial bound, and kind-split run-invariant packages. -/
theorem uniformCertificateInput_of_boxInvariantsK' (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (htmark : TileMarkingStatement) (htquery : TileQueryStatement)
    (htpat : TilePatternStatement) (htabort : TileAbortStatement)
    (hthalt : TileHaltPatternStatement)
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hTTB : ∀ C : ℝ, 1 ≤ C → TileTrialBoundStatement d C)
    (hbox : ∀ C : ℝ, 1 ≤ C → ∃ Cg : ℝ, 1 ≤ Cg ∧ ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariantK d m n₀ u E Cr cp cg c Cg P)) :
    UniformCertificateInput d e₂ :=
  uniformCertificateInput_of_boxInvariantsK d hd e₂ htmark htquery htpat htabort hthalt hcmeas
    (fun m => clearingFailGuarded_proof d m) (fun m => clearingCoreRadius_proof d m)
    (fun m => clearingEligibleIntro_proof d m) hTTB hbox

end AndersonAC.AgentS78
