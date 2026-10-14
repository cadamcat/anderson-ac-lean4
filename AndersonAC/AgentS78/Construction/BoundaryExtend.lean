import AndersonAC.AgentS78.Construction.BoundaryInv

/-!
# WP10 construction: extending the stage-boundary invariant by one stage

`BoundaryHist.extend`: if the previous boundary endpoint `old` (with damping `rOld`) ends a
stage history up to `k` (the stage's phase invariants must carry this witness, since the
record's endpoint changes during the stage), and the stage produced a `StageStep` from `(old, rOld)` to the committed
endpoint and damping of the exit record, with the boundary facts at stage `k + 1`, then the
exit record carries `BoundaryInv … (k + 1)`. This is the purely logical part of the stage-end
package; the analytic part is the `StageStep` (`stage_step_of_sections`) and the boundary
facts at the new stage.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem BoundaryHist.extend {n₀ : ℕ} {u E : ℝ} {ρ : ℂ} {C : ℝ} {k : ℕ} (hk : n₀ ≤ k)
    (old new : Endpoint (Torus d m)) (rOld rNew : Torus d m → ℂ)
    (hx : BoundaryHist n₀ u E ρ C k old rOld)
    (hstep : Nonempty (StageStep d m C (stageScale u k m) (stageScale u (k + 1) m)
      old new rOld rNew))
    (hphys : IsDampedEndpoint new rNew (stageScale u (k + 1) m))
    (hreset : ∀ i ∈ new.active, new.g i i = rNew i)
    (hrows : ∀ i, rowFour (normalizedInverse new (stageScale u (k + 1) m)) i ≤
      stageScale u (k + 1) m ^ (1 + delta))
    (hker : constantKernel new.active (endpointEnergy new rNew (stageScale u (k + 1) m)))
    (hcount : Fintype.card (Torus d m) ≤ 2 * new.active.card)
    (hmet : ∀ y z, physicalDistance d m y z / 2 - stageScale u (k + 1) m ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ new.active) y z) :
    BoundaryHist n₀ u E ρ C (k + 1) new rNew := by
  obtain ⟨state, r, h0, hr0, hk1, hk2, hst, hph, hre, hro, hke, hco, hme⟩ := hx
  classical
  let state' : ℕ → Endpoint (Torus d m) := fun n => if n = k + 1 then new else state n
  let r' : ℕ → Torus d m → ℂ := fun n => if n = k + 1 then rNew else r n
  have hs : ∀ n, n ≤ k → state' n = state n := fun n hn => by simp [state', show n ≠ k + 1 by omega]
  have hr : ∀ n, n ≤ k → r' n = r n := fun n hn => by simp [r', show n ≠ k + 1 by omega]
  have hs1 : state' (k + 1) = new := by simp [state']
  have hr1 : r' (k + 1) = rNew := by simp [r']
  refine ⟨state', r', ?_, ?_, hs1, hr1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs n₀ hk]; exact h0
  · rw [hr n₀ hk]; exact hr0
  · intro n h1 h2
    by_cases hn : n < k
    · rw [hs n hn.le, hs (n + 1) hn, hr n hn.le, hr (n + 1) hn]; exact hst n h1 hn
    · have : n = k := by omega
      subst this
      rw [hs n le_rfl, hr n le_rfl, hs1, hr1, hk1, hk2]; exact hstep
  · intro n h1 h2
    rcases Nat.lt_or_ge n (k + 1) with hn | hn
    · rw [hs n (by omega), hr n (by omega)]; exact hph n h1 (by omega)
    · have : n = k + 1 := by omega
      subst this; rw [hs1, hr1]; exact hphys
  · intro n h1 h2
    rcases Nat.lt_or_ge n (k + 1) with hn | hn
    · rw [hs n (by omega), hr n (by omega)]; exact hre n h1 (by omega)
    · have : n = k + 1 := by omega
      subst this; rw [hs1, hr1]; exact hreset
  · intro n h1 h2
    rcases Nat.lt_or_ge n (k + 1) with hn | hn
    · rw [hs n (by omega)]; exact hro n h1 (by omega)
    · have : n = k + 1 := by omega
      subst this; rw [hs1]; exact hrows
  · intro n h1 h2
    rcases Nat.lt_or_ge n (k + 1) with hn | hn
    · rw [hs n (by omega), hr n (by omega)]; exact hke n h1 (by omega)
    · have : n = k + 1 := by omega
      subst this; rw [hs1, hr1]; exact hker
  · intro n h1 h2
    rcases Nat.lt_or_ge n (k + 1) with hn | hn
    · rw [hs n (by omega)]; exact hco n h1 (by omega)
    · have : n = k + 1 := by omega
      subst this; rw [hs1]; exact hcount
  · intro n h1 h2
    rcases Nat.lt_or_ge n (k + 1) with hn | hn
    · rw [hs n (by omega)]; exact hme n h1 (by omega)
    · have : n = k + 1 := by omega
      subst this; rw [hs1]; exact hmet

end AndersonAC.AgentS78
