import AndersonAC.AgentS78.SweepInitial
import AndersonAC.S45.SweepEndpointFinal

/-!
WP10 sweep step from the unconditional `AgentS45.ordinary_sweep_endpoint_proof`
(lane/agent-s45 811ae7d, exact type of `S45.ordinary_sweep_endpoint`): for the S45 states
of the active blocks of `old` and `sw`, the sweep hypotheses of §5 give the
`StageStep` sweep fields and the `AssemblyInput` initial rows and lag.
-/

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S45

theorem sweep_from_S45 (C : ℝ) (hC : 1 ≤ C) : ∃ C' > 0, ∃ t0 > 0,
    ∀ {d m : ℕ} (n : ℕ) (t θ : ℝ) (oldE sw : Endpoint (Torus d m)) (rOld : Torus d m → ℂ)
      (hact : sw.active = oldE.active) (e : Fin n ≃ oldE.active)
      (old new : State (Fin n)) (hold' : old = toS45 oldE rOld e)
      (hnew' : new = toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact]))))
      (q : Sequence (initialPorts (Fin n))),
    IsDampedEndpoint oldE rOld t → IsDampedEndpoint sw rOld (θ * t) →
    0 < t → t < t0 → 1 / 4 ≤ θ → θ ≤ 5 / 8 →
    (∀ i, new.r i = old.r i ∧ ‖old.r i‖ ≤ C ∧ 1 / C ≤ old.p i ∧ old.p i ≤ C) →
    (∀ i, old.g i i = old.r i) → old.g.IsSymm → old.ward t →
    AndersonAC.S45.constantKernel (old.D t) → ‖old.K t‖ ≤ 1 / 3 →
    let r := ((splitPorts (Fin n) θ).liftState old).r
    q.wellFormed t r → (q.state 0).live = Finset.univ →
    (q.state 0).g = ((splitPorts (Fin n) θ).liftState old).g →
    (q.state q.length).live = reserves →
    (∀ i j, (q.state q.length).g (i, true) (j, true) = Real.sqrt θ * new.g i j) →
    (∀ k ≤ q.length, ((q.state k).state r).g.IsSymm ∧ ((q.state k).state r).ward t) →
    (∀ k < q.length, ∀ x : (q.state k).live,
      1 - ((q.state k).state r).K t x x ≠ 0 ∧
      0 < ((q.state k).state r).q x -
        ((q.state k).state r).p x * ((q.state k).state r).F t x x) →
    q.valid t r (((splitPorts (Fin n) θ).liftState old).D t) q.length →
    (∀ i, ((q.state q.length).ambient r).fourthRow t reserves (i, true) ≤
      (θ^2 + C * power t (AndersonAC.S45.delta / 2000)) * rowCap t) →
    ((∀ y, AndersonAC.S78.neutral oldE.active y →
      (1 - C' * t ^ (0.10 * AndersonAC.S78.delta)) * stageTarget oldE rOld t (θ * t) oldE.active y ≤
        Xof sw rOld (θ * t) y ∧
      Xof sw rOld (θ * t) y ≤
        (1 + C' * t ^ (0.10 * AndersonAC.S78.delta)) * stageTarget oldE rOld t (θ * t) oldE.active y) ∧
     Kn sw (θ * t) ≤ Kn oldE t + 1 * t ^ (0.10 * AndersonAC.S78.delta)) ∧
    (∀ i, rowFour (normalizedInverse sw (θ * t)) i ≤ 0.7 * (θ * t) ^ (1 + AndersonAC.S78.delta)) ∧
    (∀ i ∈ sw.active, ‖sw.g i i - rOld i‖ ≤ (4 * C') * (θ * t) ^ (0.42 * AndersonAC.S78.delta)) := by
  obtain ⟨C', hC', t0, ht0, h⟩ := AndersonAC.AgentS45.ordinary_sweep_endpoint_proof C hC
  refine ⟨C', hC', t0, ht0, ?_⟩
  intro d m n t θ oldE sw rOld hact e old new hold' hnew' q hDo hDs ht htt hθ hθ' a1 a2 a3 a4 a5 a6
    r b1 b2 b3 b4 b5 b6 b7 b8 b9
  have H := h n t θ old new q ht htt hθ hθ' a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 b7 b8 b9
  subst hold' hnew'
  obtain ⟨haff, hK, hlag, hrows⟩ := H
  refine ⟨sweep_step oldE sw rOld t θ C' ht (by linarith) hDo hDs hact e haff hK,
    sweep_initial_rows_lag oldE sw rOld t θ C' ht hθ (by linarith) hC'.le hDs.2.1 hact e hlag
      (fun i => (hrows i).2)⟩

end AndersonAC.AgentS78
