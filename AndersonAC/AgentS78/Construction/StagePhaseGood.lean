import AndersonAC.AgentS78.Construction.StagePhaseStage
import AndersonAC.AgentS78.Construction.ClearingTrialH

/-!
# The clearing-phase invariant with the C4b good set

`ClearPhaseG … j x`: the clearing-phase data (StagePhase.lean) and, on non-aborted records,
the clearing good set `ClearingGood d cP CP qlag geo n₀ u E j` of agent-s78clrtrial
(ClearingTrialH.lean, lane/agent-s78clrtrial 0cfb85f), which is the hypothesis of the clearing
first-trial bound.

`clearPhase_goodAt_analytic`: the analytic clauses `broad`, `fourth` and `lag` of
`ClearingGoodAt` follow from the clearing-phase data (via `S78.committed_assembly` at the last
committed state; 07-assembly.tex:950–1010: "every committed prefix has lag `o(t^{.36δ})`,
fourth-row sums below `.8 t^{1+δ}`"), with `cP = cA`, `CP = CA` and the uniform
`qlag t = C' t^{.06δ − dν} → 0` (`phaseQlag_tendsto`). The record clauses `coupled`,
`separated`, `coreBall` and `geo` are bookkeeping of the run (pending set, components,
prefix lengths) and are kept by the blocks (part (a) of the package).
-/

open Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- **The clearing-phase invariant with the C4b good set.** -/
def ClearPhaseG (cP CP : ℝ) (qlag : ℝ → ℝ) (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m))
    (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C CA cA PA : ℝ) (j : ℕ) (x : RunRecord d m) : Prop :=
  ClearPhase n₀ u E ρ C CA cA PA j x ∧
    (x.aborted = false → x ∈ ClearingGood d cP CP qlag geo n₀ u E j)

/-- The uniform lag function of the clearing phase. -/
def phaseQlag (d : ℕ) (C' : ℝ) (t : ℝ) : ℝ := C' * t ^ (0.06 * delta - (d : ℝ) * nu d)

theorem phaseQlag_tendsto (hd : 3 ≤ d) (C' : ℝ) :
    Tendsto (phaseQlag d C') (𝓝[>] 0) (𝓝 0) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdν : (d : ℝ) * nu d = delta / 100000 := by
    unfold nu; field_simp
  have he : 0 < 0.06 * delta - (d : ℝ) * nu d := by rw [hdν]; norm_num [delta]
  have h0 : Tendsto (fun t : ℝ => t ^ (0.06 * delta - (d : ℝ) * nu d)) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow he.ne'] using (Real.continuous_rpow_const he.le).tendsto 0
  have h1 : Tendsto (fun t : ℝ => t ^ (0.06 * delta - (d : ℝ) * nu d)) (𝓝[>] 0) (𝓝 0) :=
    h0.mono_left nhdsWithin_le_nhds
  have := h1.const_mul C'
  rw [mul_zero] at this
  exact this

/-- **The analytic clauses of the C4b good set** on clearing-phase records. -/
theorem clearPhase_goodAt_analytic (hd : 3 ≤ d) (CA cA PA : ℝ) (hCA : 1 ≤ CA) (hcA : 0 < cA)
    (hPA : 0 ≤ PA) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
    ∀ {m : ℕ} (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (j : ℕ) (x : RunRecord d m)
      (_D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → stageScale u j m < t₀ →
      (∀ i ∈ x.endpoint.active, ‖x.r i‖ ≤ CA ∧ cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA) ∧
      (∀ i : ActiveSite x,
        AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse (stageScale u j m) (trialG0 x)) i ≤
          (4 / 5) * AndersonAC.S6.fourthCap (stageScale u j m)) ∧
      (∀ i ∈ x.endpoint.active, ‖x.endpoint.g i i - x.r i‖ ≤
        phaseQlag d C' (stageScale u j m) * stageScale u j m ^ AndersonAC.S6.betaW) := by
  obtain ⟨C', tA, hC', htA, hCAss⟩ := committed_assembly d hd CA cA PA hCA hcA hPA
  refine ⟨C', tA, hC', htA, ?_⟩
  intro m n₀ u E ρ C j x D hu ht
  obtain ⟨old, rOld, k, I, hist, sweep, hlast, hfrozen, hIC, hIc, hIP⟩ := D
  subst hfrozen
  have hCa := hCAss m k (stageScale u j m) (stageScale u n₀ m * stageScale u j m) x.r I hIC hIc
    hIP ht (Fin.last k)
  rw [hlast] at hCa
  obtain ⟨-, hlag, hrow, -, -, -⟩ := hCa
  have hD : IsDampedEndpoint x.endpoint x.r (stageScale u j m) := hlast ▸ I.physical (Fin.last k)
  refine ⟨fun i _ => ?_, fun i => ?_, fun i hi => ?_⟩
  · have := I.damping i
    rw [hIC, hIc] at this
    exact ⟨this.2.2, this.1, this.2.1⟩
  · have hfg := g_eq_padM_resetInverse x.endpoint x.r (stageScale u j m) hD
    have h8 := (hrow i.val).2
    have he : normalizedInverse x.endpoint (stageScale u j m) =
        (Real.sqrt (stageScale u j m) : ℂ) • padM x.endpoint.active
          (resetInverse (x.endpoint.M.submatrix (fun a : x.endpoint.active => a.val)
            (fun a : x.endpoint.active => a.val)) (fun a => x.r a.val) (stageScale u j m)) := by
      rw [normalizedInverse, hfg]
    rw [he, rowFour_smul_padM x.endpoint.active _ _ i] at h8
    have hg0 : trialG0 x = resetInverse (x.endpoint.M.submatrix (fun a : x.endpoint.active => a.val)
        (fun a : x.endpoint.active => a.val)) (fun a => x.r a.val) (stageScale u j m) := by
      unfold trialG0
      rw [hfg]
      exact padM_submatrix _ _
    rw [hg0]
    unfold AndersonAC.S6.fourthCap
    have hδ6 : AndersonAC.S6.delta = delta := by norm_num [AndersonAC.S6.delta, delta]
    rw [hδ6]
    exact le_of_lt (by simpa [AndersonAC.S6.fourthRow, AndersonAC.S6.scaledInverse, rowFour]
      using h8.trans_le (le_of_eq (by norm_num)))
  · have htp := stageScale_pos' hu j m
    refine (hlag i hi).trans (le_of_eq ?_)
    unfold phaseQlag AndersonAC.S6.betaW
    rw [mul_assoc, ← Real.rpow_add htp]
    have hδ6 : AndersonAC.S6.delta = delta := by norm_num [AndersonAC.S6.delta, delta]
    congr 2
    rw [hδ6]
    ring

end AndersonAC.AgentS78
