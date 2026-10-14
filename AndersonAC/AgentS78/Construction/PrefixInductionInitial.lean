import AndersonAC.AgentS78.InitialStageFull
import AndersonAC.AgentS78.StageInduction
import AndersonAC.AgentS78.Construction.PrefixInduction
import AndersonAC.AgentS78.Construction.PrefixInductionProof

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Initial-stage bounds propagated through any available history prefix. -/
theorem prefix_stage_bounds_of_initial
    (hLD : AndersonAC.S3.LargeSymbolDecayWStatement) {d : ℕ}
    (hd : 3 ≤ d) (e₂ : ℝ) (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ (N : ℕ) (cP CP cL CL C₀ : ℝ), 0 < cP ∧ cP ≤ CP ∧ 0 < cL ∧ 0 < CL ∧ 0 < C₀ ∧
      ∀ n₀ : ℕ, N ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m → ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      ∃ ρ : ℝ → ℂ, ContinuousOn ρ (OAI.Anderson.energyWindow d e₂) ∧
      ∀ E ∈ OAI.Anderson.energyWindow d e₂,
        IsDampedEndpoint (initialEndpoint d m E (stageScale u n₀ m) (ρ E)) (fun _ => ρ E)
          (stageScale u n₀ m) ∧
        ∀ K : ℕ, K ≤ m → ∀ H : PrefixStageInputs d m n₀ K u C,
          H.state n₀ = initialEndpoint d m E (stageScale u n₀ m) (ρ E) →
          H.r n₀ = (fun _ => ρ E) →
          ∀ n, n₀ ≤ n → n ≤ K →
            StageBounds d m n₀ n u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀
              (H.state n) (H.r n) := by
  obtain ⟨nmin, cP, CP, cL, CL, C₀S, -, hcP, hCP, hcL, hCL, hC0S, hinit⟩ :=
    initial_stage_of_decay hLD hd e₂ he₂
  set C₀ := max C₀S (4 / cP ^ 2 + 1) with hC₀
  obtain ⟨N, hN⟩ := PrefixInduction.prefix_deterministic_induction_ge d hd
    cP CP cL CL C hcP hCP hcL hCL hC C₀ (le_max_right _ _)
  refine ⟨max N nmin, cP, CP, cL, CL, C₀, hcP, hCP, hcL, hCL,
    lt_of_lt_of_le hC0S (le_max_left _ _), ?_⟩
  intro n₀ hn₀ m hm u hu
  obtain ⟨ρ, hρ, hE⟩ := hinit n₀ (le_trans (le_max_right _ _) hn₀) m hm u hu
  refine ⟨ρ, hρ, fun E hEw => ?_⟩
  obtain ⟨hdamp, hSB, hK⟩ := hE E hEw
  refine ⟨hdamp, ?_⟩
  intro K hKm H hstate hr n hn₀n hnK
  refine hN m n₀ K u H (le_trans (le_max_left _ _) hn₀) hm hKm hu ?_ ?_ n hn₀n hnK
  · rw [hstate, hr]
    exact stageBounds_mono_C0 (le_max_left _ _) hSB
  · rw [hstate]
    exact hK

/-- Unconditional prefix stage bounds using the proved §3 decay input. -/
theorem prefix_stage_bounds_of_initial_unconditional {d : ℕ} (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) (C : ℝ) (hC : 1 ≤ C) :
    type_of% (prefix_stage_bounds_of_initial largeSymbolDecayW_proof hd e₂ he₂ C hC) :=
  prefix_stage_bounds_of_initial largeSymbolDecayW_proof hd e₂ he₂ C hC

/-- Certificate construction contract for deterministic induction on history prefixes. -/
theorem prefixStageBounds_proof :
    ∀ (d : ℕ), 3 ≤ d → ∀ (e₂ : ℝ), e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100) →
      ∀ (C : ℝ), 1 ≤ C →
      PrefixStageBoundsStatement d e₂ C := by
  intro d hd e₂ he₂ C hC
  exact prefix_stage_bounds_of_initial_unconditional hd e₂ he₂ C hC

end AndersonAC.AgentS78
