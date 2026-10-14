import AndersonAC.AgentS78.InitialStageBR
import AndersonAC.AgentS78.InductionGe

/-!
WP10: stage invariant along any pathwise stage history started from the §3
initialization. Combines `initial_stage_of_decay` with the induction of
Proposition 7.5 (`InductionGe.deterministic_induction_ge`, the original proof with
`C₀` as an input). What remains for WP10 is the construction of the
`PathwiseStageInputs` themselves (sweeps, clearings, assembly, reset).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem stageBounds_mono_C0 {d m n₀ n : ℕ} {u cP CP cL CL C₀ C₀' : ℝ}
    {s : Endpoint (Torus d m)} {r : Torus d m → ℂ} (h : C₀ ≤ C₀')
    (hs : StageBounds d m n₀ n u cP CP cL CL C₀ s r) :
    StageBounds d m n₀ n u cP CP cL CL C₀' s r := by
  unfold StageBounds at *
  dsimp only at *
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hs
  refine ⟨a1, a2, a3, a4, a5, a6, fun y hy => ?_⟩
  obtain ⟨b1, b2, b3⟩ := a7 y hy
  refine ⟨b1, b2.trans ?_, b3⟩
  have : 0 ≤ ∑ i ∈ s.active, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

/-- **Stage invariant from initialization.** For every stage-history constant `C ≥ 1`
there are uniform constants such that every `PathwiseStageInputs` history starting
at the §3 initial endpoint satisfies `StageBounds` at every stage `n₀ ≤ n ≤ m`.
Conditional only on `S3.LargeSymbolDecayWStatement`. -/
theorem stage_bounds_of_initial (hLD : AndersonAC.S3.LargeSymbolDecayWStatement) {d : ℕ}
    (hd : 3 ≤ d) (e₂ : ℝ) (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) (C : ℝ) (hC : 1 ≤ C) :
    ∃ (N : ℕ) (cP CP cL CL C₀ : ℝ), 0 < cP ∧ cP ≤ CP ∧ 0 < cL ∧ 0 < CL ∧ 0 < C₀ ∧
      ∀ n₀ : ℕ, N ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m → ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      ∃ ρ : ℝ → ℂ, ContinuousOn ρ (OAI.Anderson.energyWindow d e₂) ∧
      ∀ E ∈ OAI.Anderson.energyWindow d e₂,
        IsDampedEndpoint (initialEndpoint d m E (stageScale u n₀ m) (ρ E)) (fun _ => ρ E)
          (stageScale u n₀ m) ∧
        ∀ H : PathwiseStageInputs d m n₀ u C,
          H.state n₀ = initialEndpoint d m E (stageScale u n₀ m) (ρ E) → H.r n₀ = (fun _ => ρ E) →
          ∀ n, n₀ ≤ n → n ≤ m →
            StageBounds d m n₀ n u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀ (H.state n) (H.r n) := by
  obtain ⟨nmin, cP, CP, cL, CL, C₀S, -, hcP, hCP, hcL, hCL, hC0S, hinit⟩ :=
    initial_stage_of_decay hLD hd e₂ he₂
  set C₀ := max C₀S (4 / cP ^ 2 + 1) with hC₀
  obtain ⟨N, hN⟩ := InductionGe.deterministic_induction_ge d hd cP CP cL CL C hcP hCP hcL hCL hC C₀
    (le_max_right _ _)
  refine ⟨max N nmin, cP, CP, cL, CL, C₀, hcP, hCP, hcL, hCL,
    lt_of_lt_of_le hC0S (le_max_left _ _), ?_⟩
  intro n₀ hn₀ m hm u hu
  obtain ⟨ρ, hρ, hE⟩ := hinit n₀ (le_trans (le_max_right _ _) hn₀) m hm u hu
  refine ⟨ρ, hρ, fun E hEw => ?_⟩
  obtain ⟨hdamp, hSB, hK⟩ := hE E hEw
  refine ⟨hdamp, fun H h0 hr0 n hn1 hn2 => ?_⟩
  refine hN m n₀ u H (le_trans (le_max_left _ _) hn₀) hm hu ?_ ?_ n hn1 hn2
  · rw [h0, hr0]; exact stageBounds_mono_C0 (le_max_left _ _) hSB
  · rw [h0]; exact hK

end AndersonAC.AgentS78
