import AndersonAC.AgentS78.Construction.BoundaryExtend
import AndersonAC.AgentS78.Construction.PrefixInductionProof
import AndersonAC.AgentS78.Construction.TrueValues

/-!
# the initial record and stage bounds along the run

* `initialRecord`: the committed record before stage `n₀ + 1` (02-state.tex:96–125): the §3
  initial endpoint with damping `ρ`, the stage-start lift `sweepStartMap θ t` of the first
  sweep, no installed digits, nothing pending, terminal or aborted. It has no pending site,
  is not aborted, and carries `TrueValues` for every sample.
* `boundaryHist_initial`: the one-stage history at `n₀` from the damped endpoint and the
  stage bounds of the initial stage (`initial_stage_unconditional`).
* `stageBounds_of_hist`: every stage history from such an initial endpoint satisfies the
  stage bounds at its last stage (`prefix_deterministic_induction_ge`), with
  the same `ρ` as the initial stage.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources binaryPrefix)

variable {d m : ℕ}

/-- The initial committed record. -/
def initialRecord (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (θ t : ℝ) (lab : BirthLabel (Torus d m)) :
    RunRecord d m :=
  sweepStartMap θ t
    { stage := n₀
      endpoint := initialEndpoint d m E (stageScale u n₀ m) ρ
      r := fun _ => ρ
      sweep := emptyRunSweep
      installed := fun _ => 0
      prefixLength := fun _ => 0
      terminal := ∅
      pending := ∅
      latest := fun _ => lab
      components := ∅
      aborted := false }

theorem initialRecord_pending (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (θ t : ℝ)
    (lab : BirthLabel (Torus d m)) : (initialRecord n₀ u E ρ θ t lab).pending = ∅ := rfl

theorem initialRecord_aborted (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (θ t : ℝ)
    (lab : BirthLabel (Torus d m)) : (initialRecord n₀ u E ρ θ t lab).aborted = false := rfl

theorem initialRecord_trueValues {M : ℕ → ℕ} (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (θ t : ℝ)
    (lab : BirthLabel (Torus d m)) (ω : RandomSources (Torus d m) M) :
    initialRecord n₀ u E ρ θ t lab ∈ TrueValues n₀ u ω := by
  intro _
  refine ⟨fun i hi => absurd hi (Finset.notMem_empty i), fun i _ _ => ?_⟩
  show (0 : ℝ) = binaryPrefix _ 0 _
  simp [binaryPrefix]

/-- The history of length zero at the initial stage. -/
theorem boundaryHist_initial (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C cP CP cL CL C₀ : ℝ)
    (hdamp : IsDampedEndpoint (initialEndpoint d m E (stageScale u n₀ m) ρ) (fun _ => ρ)
      (stageScale u n₀ m))
    (hSB : StageBounds d m n₀ n₀ u cP CP cL CL C₀
      (initialEndpoint d m E (stageScale u n₀ m) ρ) (fun _ => ρ)) :
    BoundaryHist n₀ u E ρ C n₀ (initialEndpoint d m E (stageScale u n₀ m) ρ) (fun _ => ρ) := by
  obtain ⟨hreset, hrows, -, hker, hcount, hmet, -⟩ := hSB
  refine ⟨fun _ => initialEndpoint d m E (stageScale u n₀ m) ρ, fun _ _ => ρ, rfl, rfl, rfl, rfl,
    fun n h1 h2 => absurd h2 (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h1 h2; have : n = n₀ := by omega
    subst this; exact hdamp
  · intro n h1 h2 i hi; have : n = n₀ := by omega
    subst this; exact (hreset i hi).1
  · intro n h1 h2; have : n = n₀ := by omega
    subst this; exact hrows
  · intro n h1 h2; have : n = n₀ := by omega
    subst this; exact hker
  · intro n h1 h2; have : n = n₀ := by omega
    subst this; exact hcount
  · intro n h1 h2; have : n = n₀ := by omega
    subst this; exact hmet

/-- **Stage bounds along every history from a good initial stage.** -/
theorem stageBounds_of_hist (hd : 3 ≤ d) (cP CP cL CL C : ℝ) (hcP : 0 < cP) (hCP : cP ≤ CP)
    (hcL : 0 < cL) (hCL : 0 < CL) (hC : 1 ≤ C) (C₀ : ℝ) (hC₀ : 4 / cP ^ 2 + 1 ≤ C₀) :
    ∃ N : ℕ, ∀ n₀ u E (ρ : ℂ) k (s : Endpoint (Torus d m)) (rk : Torus d m → ℂ),
      N ≤ n₀ → 1 ≤ n₀ → 4 * n₀ ≤ m → k ≤ m → n₀ ≤ k → u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      C * stageScale u n₀ m ^ (0.10 * delta) ≤ 1 / 4 →
      StageBounds d m n₀ n₀ u cP CP cL CL C₀
        (initialEndpoint d m E (stageScale u n₀ m) ρ) (fun _ => ρ) →
      matrixNorm (squareKernel (normalizedInverse (initialEndpoint d m E (stageScale u n₀ m) ρ)
        (stageScale u n₀ m))) ≤ 1 / 4 →
      BoundaryHist n₀ u E ρ C k s rk →
      StageBounds d m n₀ k u (cP / 2) (2 * CP) (cL / 2) (2 * CL) C₀ s rk := by
  obtain ⟨N, hN⟩ := PrefixInduction.prefix_deterministic_induction_ge d hd cP CP cL CL (8 * C + 4)
    hcP hCP hcL hCL (by linarith) C₀ hC₀
  refine ⟨N, fun n₀ u E ρ k s rk hN0 hn₀ hm hkm hk hu hsmall hSB hK hist => ?_⟩
  obtain ⟨state, r, h0, hr0, hk1, hk2, hst, hph, hre, hro, hke, hco, hme⟩ := hist
  have := hN m n₀ k u (prefix_of_steps hu hC hn₀ hkm state r hsmall
    (fun n h1 h2 => (hst n h1 h2).some) hph hre hro hke hco hme) hN0 hm hkm hu
    (by show StageBounds d m n₀ n₀ u cP CP cL CL C₀ (state n₀) (r n₀); rw [h0, hr0]; exact hSB)
    (by show matrixNorm (squareKernel (normalizedInverse (state n₀) (stageScale u n₀ m))) ≤ 1 / 4
        rw [h0]; exact hK) k hk le_rfl
  rw [← hk1, ← hk2]
  exact this

end AndersonAC.AgentS78
