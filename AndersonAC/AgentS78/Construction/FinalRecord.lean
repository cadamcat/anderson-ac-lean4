import AndersonAC.AgentS78.Construction.Assembly
import AndersonAC.AgentS78.Construction.PhysicalIdentity

/-!
# WP10 construction, C5d glue: the final record

`hfinal` of `blockRun_of_disciplines` / `blockRun_of_runOps` from two record facts at the
entry of the block after the final residual sweep (`stageStartIdx d m (m + 2)`):
the deterministic final-record invariant `FinalGood` (physical identity 02-state.tex:231–247,
damped endpoint at η, active count, damping bounds, lag; from the run invariant) and the
pathwise fact that every installed value is the true one, `installed = λ V(ω)` (the final
sweep installs the whole remaining true suffix, 02-state.tex:103–106; from the pathwise
invariant, `blockPrestate_mem_pathwise`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources)

variable {d m : ℕ}

/-- The deterministic facts of a final committed record. -/
def FinalGood (u E Cr cp cg : ℝ) : Set (RunRecord d m) :=
  {x | PhysicalIdentity E x ∧ IsDampedEndpoint x.endpoint x.r (OAI.Anderson.scaleHeight m u) ∧
    Fintype.card (Torus d m) ≤ 2 * x.endpoint.active.card ∧
    (∀ i ∈ x.endpoint.active, ‖x.r i‖ ≤ Cr ∧ cp ≤ (x.r i).im) ∧
    (∀ i ∈ x.endpoint.active, ‖x.endpoint.g i i - x.r i‖ ≤ cp - cg)}

/-- **`hfinal` from the final record.** -/
theorem hfinal_of_finalGood (n₀ : ℕ) (u E Cr cp cg : ℝ) {M : ℕ → ℕ} {St : Type}
    (blocks : ℕ → Block (Torus d m) (RunRecord d m) St) (rec₀ : RunRecord d m)
    (h : ∀ ω : RandomSources (Torus d m) M,
      blockStart M blocks rec₀ (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
      (blockPrestate M blocks rec₀ (stageStartIdx d m (m + 2)) ω).aborted = false →
      blockPrestate M blocks rec₀ (stageStartIdx d m (m + 2)) ω ∈ FinalGood u E Cr cp cg ∧
      ∀ i, (blockPrestate M blocks rec₀ (stageStartIdx d m (m + 2)) ω).installed i =
        OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)) :
    ∀ ω : RandomSources (Torus d m) M,
      blockStart M blocks rec₀ (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
      (blockPrestate M blocks rec₀ (stageStartIdx d m (m + 2)) ω).aborted = false →
      ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ),
        IsDampedEndpoint s r (OAI.Anderson.scaleHeight m u) ∧
        TrueSchurIdentity n₀ u E (trueConfig ω) s ∧
        Fintype.card (Torus d m) ≤ 2 * s.active.card ∧
        (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧
        (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg) := by
  intro ω hreach hab
  obtain ⟨⟨hphys, hdamp, hcard, hr, hlag⟩, hinst⟩ := h ω hreach hab
  exact ⟨_, _, hdamp, trueSchurIdentity_of_physical n₀ u E (trueConfig ω) _ hinst hphys, hcard,
    hr, hlag⟩

end AndersonAC.AgentS78
