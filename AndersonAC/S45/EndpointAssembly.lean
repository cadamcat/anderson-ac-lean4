import AndersonAC.S45.LocalTransferProof
import AndersonAC.S45.RecordsProof
import AndersonAC.S45.FormsProof
import AndersonAC.S45.SweepEndpointProof
import AndersonAC.S45.CumulativeSchurProof
import AndersonAC.S45.StepLProof
import AndersonAC.S45.DuplicationProof

/-! Assembly of the §§4–5 endpoints from the helper proofs. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

theorem scalarRecords_holds : ScalarRecordsStmt :=
  fun P _ _ => @scalar_records_proof P _ _

theorem reserveScaling_holds : ReserveScalingStmt :=
  fun I _ _ => @reserve_scaling_proof I _ _

/-- `reserve_target` follows from the duplication identity for the dual form. -/
theorem reserveTarget_of_dup (hdup : DuplicationStmt) : ReserveTargetStmt := by
  intro I _ _ s t θ hθ hfix hp hkernel y hy
  set v := splitPorts I θ with hv
  have hmass : ∀ i, v.mass i = 1 := by
    intro i
    unfold PortMap.mass
    change (∑ x : I × Bool, _) = 1
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp only [hv, splitPorts, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      rw [quarter_pow_four hθ.1.le, quarter_pow_four (by linarith [hθ.2])]
      ring
    · intro b _ hb; simp [hv, splitPorts, hb]
    · simp
  have hk : ∀ x, 0 < v.weight x := by
    intro x; simp only [hv, splitPorts]
    split_ifs
    · exact quarter_pos hθ.1
    · exact quarter_pos (by linarith [hθ.2])
  obtain ⟨-, -, -, -, -, hX⟩ := hdup (initialPorts I) I v s t hmass hk hfix hkernel hp
  have hy' : neutral (reserveCharge y) := by
    unfold neutral at hy ⊢
    show (∑ x : I × Bool, (if x.2 then y x.1 else 0)) = 0
    rw [Fintype.sum_prod_type]
    simpa using hy
  have h := hX (reserveCharge y) hy'
  have hsum : v.sumCharge (reserveCharge y) = y := by
    funext i
    unfold PortMap.sumCharge
    change (∑ x : I × Bool, _) = y i
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [hv, splitPorts, reserveCharge]
    · intro b _ hb; simp [hv, splitPorts, hb]
    · simp
  have hw4 : ∀ i, v.weight (i, true) ^ 4 = θ := fun i => by
    simp only [hv, splitPorts, if_true]; exact quarter_pow_four hθ.1.le
  have hmid : (∑ x, reserveCharge y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2)) =
      ∑ i, y i ^ 2 / (θ * s.p i ^ 2) := by
    change (∑ x : I × Bool, _) = _
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fintype.sum_bool, reserveCharge, if_true, Bool.false_eq_true, if_false]
    rw [hw4]; simp [hv, splitPorts]
  rw [h, hsum, hmid]
  have hθ0 : θ ≠ 0 := ne_of_gt hθ.1
  have e : θ * ∑ i, y i ^ 2 / (θ * s.p i ^ 2) = ∑ i, y i ^ 2 / s.p i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [mul_sub, mul_add, e]
  ring

theorem cumulativeSchur_holds : CumulativeSchurStmt :=
  fun P _ _ => @cumulative_schur_proof P _ _

/-- `ordinary_sweep_endpoint` from the two remaining form inputs
(`schur_dual_transport`, `duplication`); cumulative Schur, Schur contraction,
reserve scaling and the step Laplacian are proved. -/
theorem ordinary_sweep_endpoint_of_dual_dup (hdual : SchurDualTransportStmt)
    (hdup : DuplicationStmt) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n : ℕ) (t θ : ℝ) (old new : State (Fin n))
    (q : Sequence (initialPorts (Fin n))),
    0 < t → t < t0 → 1 / 4 ≤ θ → θ ≤ 5 / 8 →
    (∀ i, new.r i = old.r i ∧ ‖old.r i‖ ≤ C ∧ 1 / C ≤ old.p i ∧ old.p i ≤ C) →
    (∀ i, old.g i i = old.r i) → old.g.IsSymm → old.ward t →
    constantKernel (old.D t) → ‖old.K t‖ ≤ 1 / 3 →
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
      (θ^2 + C * power t (delta / 2000)) * rowCap t) →
    (∀ y, neutral y →
      (1 - C' * power t (delta / 10)) *
        (θ * old.X t y + (1 - θ) * (∑ i, y i^2 / old.p i^2)) ≤ new.X (θ * t) y ∧
      new.X (θ * t) y ≤ (1 + C' * power t (delta / 10)) *
        (θ * old.X t y + (1 - θ) * (∑ i, y i^2 / old.p i^2))) ∧
    ‖new.K (θ * t)‖ ≤ ‖old.K t‖ + power t (delta / 10) ∧
    (∀ i, ‖new.g i i - old.r i‖ ≤ C' * power t S45.beta) ∧
    (∀ i, new.fourthRow (θ * t) Finset.univ i ≤
      (θ^2 + C' * power t (delta / 2000)) * rowCap t ∧
      new.fourthRow (θ * t) Finset.univ i < (7 / 10 : ℝ) * rowCap (θ * t)) :=
  ordinary_sweep_endpoint_of cumulativeSchur_holds schurContraction_holds hdual hdup
    (reserveTarget_of_dup hdup) reserveScaling_holds stepLLaplacian_proof

theorem duplication_holds : DuplicationStmt :=
  fun P I _ _ _ _ => @duplication_proof P I _ _ _ _

/-- `ordinary_sweep_endpoint` from `schur_dual_transport`. -/
theorem ordinary_sweep_endpoint_of_dual (hdual : SchurDualTransportStmt) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n : ℕ) (t θ : ℝ) (old new : State (Fin n))
    (q : Sequence (initialPorts (Fin n))),
    0 < t → t < t0 → 1 / 4 ≤ θ → θ ≤ 5 / 8 →
    (∀ i, new.r i = old.r i ∧ ‖old.r i‖ ≤ C ∧ 1 / C ≤ old.p i ∧ old.p i ≤ C) →
    (∀ i, old.g i i = old.r i) → old.g.IsSymm → old.ward t →
    constantKernel (old.D t) → ‖old.K t‖ ≤ 1 / 3 →
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
      (θ^2 + C * power t (delta / 2000)) * rowCap t) →
    (∀ y, neutral y →
      (1 - C' * power t (delta / 10)) *
        (θ * old.X t y + (1 - θ) * (∑ i, y i^2 / old.p i^2)) ≤ new.X (θ * t) y ∧
      new.X (θ * t) y ≤ (1 + C' * power t (delta / 10)) *
        (θ * old.X t y + (1 - θ) * (∑ i, y i^2 / old.p i^2))) ∧
    ‖new.K (θ * t)‖ ≤ ‖old.K t‖ + power t (delta / 10) ∧
    (∀ i, ‖new.g i i - old.r i‖ ≤ C' * power t S45.beta) ∧
    (∀ i, new.fourthRow (θ * t) Finset.univ i ≤
      (θ^2 + C' * power t (delta / 2000)) * rowCap t ∧
      new.fourthRow (θ * t) Finset.univ i < (7 / 10 : ℝ) * rowCap (θ * t)) :=
  ordinary_sweep_endpoint_of_dual_dup hdual duplication_holds

end AndersonAC.AgentS45
