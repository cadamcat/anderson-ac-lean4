import AndersonAC.AgentS78.Construction.FinalRecord
import AndersonAC.AgentS78.Construction.TransitionDisciplines
import AndersonAC.AgentS78.Construction.TileDisciplines
import AndersonAC.S2.Binary

/-!
# WP10 construction, C5d: installed values along the actual run (pathwise invariant)

02-state.tex:96–110: at a coupled site the installed partial value is exactly the true
revealed prefix (`λ`-coupled binary prefix of the true digits up to `prefixLength`); terminal
sites carry their full true value `λ V`. `TrueValues n₀ u ω` is this invariant for the sample
`ω`; it is propagated along the actual run by `blockPrestate_mem_pathwise`
(PathwiseInvariant.lean). The query-free transitions keep it (`trueValues_of_keeps`). At the
final record every site is terminal, so `installed = λ V(ω)` (`installed_eq_true`), the
pathwise half of `hfinal_of_finalGood`.

Frozen contract for the tile block: `TileTrueValuesStatement` (digit sweeps need the stage
prefix length `j − 1 − n₀` at coupled sites of the tile, a deterministic invariant; the final
sweep needs none).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources binaryPrefix)

variable {d m : ℕ}

/-- The installed values of a committed record are the true ones (02-state.tex:96–110). -/
def TrueValues {M : ℕ → ℕ} (n₀ : ℕ) (u : ℝ) (ω : RandomSources (Torus d m) M) :
    Set (RunRecord d m) :=
  {x | x.aborted = false →
    (∀ i ∈ x.terminal, x.installed i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)) ∧
    (∀ i, i ∉ x.pending → i ∉ x.terminal →
      x.installed i = binaryPrefix (OAI.Anderson.scaleCoupling n₀ u) (x.prefixLength i)
        (trueDigits ω i))}

/-- Maps that keep installed values, prefix lengths, pending and terminal sites and never
clear an abort keep `TrueValues`. -/
theorem trueValues_of_keeps {M : ℕ → ℕ} (n₀ : ℕ) (u : ℝ) (ω : RandomSources (Torus d m) M)
    (f : RunRecord d m → RunRecord d m)
    (hf : ∀ x, (f x).installed = x.installed ∧ (f x).prefixLength = x.prefixLength ∧
      (f x).pending = x.pending ∧ (f x).terminal = x.terminal ∧
      ((f x).aborted = false → x.aborted = false))
    (x : RunRecord d m) (hx : x ∈ TrueValues n₀ u ω) : f x ∈ TrueValues n₀ u ω := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf x
  intro hab
  obtain ⟨ht, hc⟩ := hx (h5 hab)
  refine ⟨fun i hi => ?_, fun i hp hterm => ?_⟩
  · rw [h1]; rw [h4] at hi; exact ht i hi
  · rw [h1, h2]; rw [h3] at hp; rw [h4] at hterm; exact hc i hp hterm

theorem keeps_snapshotMap (j : ℕ) (x : RunRecord d m) :
    (snapshotMap j x).installed = x.installed ∧ (snapshotMap j x).prefixLength = x.prefixLength ∧
      (snapshotMap j x).pending = x.pending ∧ (snapshotMap j x).terminal = x.terminal ∧
      ((snapshotMap j x).aborted = false → x.aborted = false) :=
  ⟨rfl, rfl, rfl, rfl, id⟩

theorem keeps_cutoffMap (x : RunRecord d m) :
    (cutoffMap x).installed = x.installed ∧ (cutoffMap x).prefixLength = x.prefixLength ∧
      (cutoffMap x).pending = x.pending ∧ (cutoffMap x).terminal = x.terminal ∧
      ((cutoffMap x).aborted = false → x.aborted = false) := by
  refine ⟨rfl, rfl, rfl, rfl, fun h => ?_⟩
  simp only [cutoffMap, Bool.or_eq_false_iff] at h
  exact h.1

theorem keeps_sweepEndMapTheta (θ : ℝ) (x : RunRecord d m) :
    (sweepEndMapTheta θ x).installed = x.installed ∧
      (sweepEndMapTheta θ x).prefixLength = x.prefixLength ∧
      (sweepEndMapTheta θ x).pending = x.pending ∧ (sweepEndMapTheta θ x).terminal = x.terminal ∧
      ((sweepEndMapTheta θ x).aborted = false → x.aborted = false) :=
  ⟨rfl, rfl, rfl, rfl, id⟩

theorem keeps_resetMap (t : ℝ) (x : RunRecord d m) :
    (resetMap t x).installed = x.installed ∧ (resetMap t x).prefixLength = x.prefixLength ∧
      (resetMap t x).pending = x.pending ∧ (resetMap t x).terminal = x.terminal ∧
      ((resetMap t x).aborted = false → x.aborted = false) :=
  ⟨rfl, rfl, rfl, rfl, id⟩

theorem keeps_sweepStartMap (θ t : ℝ) (x : RunRecord d m) :
    (sweepStartMap θ t x).installed = x.installed ∧
      (sweepStartMap θ t x).prefixLength = x.prefixLength ∧
      (sweepStartMap θ t x).pending = x.pending ∧ (sweepStartMap θ t x).terminal = x.terminal ∧
      ((sweepStartMap θ t x).aborted = false → x.aborted = false) :=
  ⟨rfl, rfl, rfl, rfl, id⟩

/-- At a non-aborted record whose sites are all terminal, every installed value is true. -/
theorem installed_eq_true {M : ℕ → ℕ} (n₀ : ℕ) (u : ℝ) (ω : RandomSources (Torus d m) M)
    (x : RunRecord d m) (hx : x ∈ TrueValues n₀ u ω) (hab : x.aborted = false)
    (hall : ∀ i, i ∈ x.terminal) :
    ∀ i, x.installed i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ) :=
  fun i => (hx hab).1 i (hall i)

/-- **Tile true-values discipline (frozen contract).** Along the actual run of a tile block
with the answers of `ω`, `TrueValues` is kept, given that at a digit sweep the coupled active
sites of the tile have consumed exactly the digits of the stages before (`j − 1 − n₀`). -/
def TileTrueValuesStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (ω : RandomSources (Torus d m) M) (x : RunRecord d m) (k : ℕ),
    P.n₀ < j → j ≤ m + 1 →
    (¬ IsFinalSweep m j → ∀ i ∈ tileSites (P.cover j) T, i ∈ x.endpoint.active →
      i ∉ x.pending → i ∉ x.terminal → x.prefixLength i = j - 1 - P.n₀) →
    x ∈ TrueValues P.n₀ P.u ω →
    (∀ k' < k, (tileBlock P j T).halted (localState M (tileBlock P j T) x k' ω) = false) →
    (tileBlock P j T).halted (localState M (tileBlock P j T) x k ω) = true →
    (tileBlock P j T).exit (localState M (tileBlock P j T) x k ω) ∈ TrueValues P.n₀ P.u ω

end AndersonAC.AgentS78
