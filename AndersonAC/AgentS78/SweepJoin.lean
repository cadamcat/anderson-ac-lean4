import AndersonAC.AgentS78.WardDamped
import AndersonAC.AgentS78.PadNorm
import AndersonAC.AgentS78.StageStep

/-!
certificate construction sweep join: the conclusion of `S45.ordinary_sweep_endpoint` (affine inverse-form
mixture and `K` increment, on `State (Fin n)`) for the active blocks of two damped
S78 endpoints gives the `StageStep` fields `sw_affine` and `sw_K` at `t' = θ t`.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Every damped endpoint carries an S45 state satisfying symmetry and Ward. -/
theorem ward_of_damped {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : Endpoint ι) (r : ι → ℂ) (t : ℝ) (ht : 0 ≤ t) (hD : IsDampedEndpoint s r t)
    (e : κ ≃ s.active) : (toS45 s r e).g.IsSymm ∧ (toS45 s r e).ward t := by
  obtain ⟨hM, -, hBG⟩ := hD
  dsimp only at hBG
  obtain ⟨h1, h2⟩ := hBG
  set B := s.M.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) -
    (t : ℂ) • Matrix.diagonal (fun i : s.active => r i.val) with hB
  set GA := s.g.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) with hGA
  have hBκ : s.M.submatrix (fun i => (e i).val) (fun i => (e i).val) -
      (t : ℂ) • Matrix.diagonal (fun i => r (e i).val) = B.submatrix e e := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hB, Matrix.diagonal_apply]
    · have : e i ≠ e j := fun h => hij (e.injective h)
      simp [hB, Matrix.diagonal_apply, hij, this]
  have hGκ : (toS45 s r e).g = GA.submatrix e e := rfl
  apply ward_of_inverse (s.M.submatrix (fun i => (e i).val) (fun i => (e i).val))
    (fun i j => hM _ _) (fun i => r (e i).val) _ t ht
  · rw [hBκ, hGκ, Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv]
  · rw [hBκ, hGκ, Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_one_equiv]

/-- `K` norm of a damped endpoint equals the S45 `K` norm of its active block. -/
theorem Kn_eq_S45 {d m n : ℕ} (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t : ℝ)
    (hzero : ∀ i j, i ∉ s.active ∨ j ∉ s.active → s.g i j = 0) (e : Fin n ≃ s.active) :
    Kn s t = ‖(toS45 s r e).K t‖ := by
  unfold Kn
  rw [matrixNorm_eq_l2, ← norm_submatrix_of_support (fun i => (e i).val)
    (Subtype.val_injective.comp e.injective)]
  · rfl
  · intro i j h
    have hz : i ∉ s.active ∨ j ∉ s.active := by
      rcases h with h | h
      · left; intro hi; exact h (e.symm ⟨i, hi⟩) (by simp)
      · right; intro hj; exact h (e.symm ⟨j, hj⟩) (by simp)
    simp [squareKernel, normalizedInverse, hzero i j hz]

theorem power_tenth (t : ℝ) : AndersonAC.S45.power t (AndersonAC.S45.delta / 10) =
    t ^ (0.10 * AndersonAC.S78.delta) := by
  unfold AndersonAC.S45.power
  rw [Real.rpow_eq_pow]
  congr 1
  norm_num [AndersonAC.S45.delta, AndersonAC.S78.delta]

/-- **Sweep join.** The two sweep conclusions of `S45.ordinary_sweep_endpoint`, for the
active blocks of the stage-start endpoint `old` (scale `t`) and the post-sweep endpoint
`sw` (scale `θ t`, same frozen `rOld`, same active set), give `StageStep.sw_affine`
and `StageStep.sw_K`. -/
theorem sweep_step {d m n : ℕ} (old sw : Endpoint (Torus d m)) (rOld : Torus d m → ℂ)
    (t θ C' : ℝ) (ht : 0 < t) (hθ : 0 < θ)
    (hold : IsDampedEndpoint old rOld t) (hsw : IsDampedEndpoint sw rOld (θ * t))
    (hact : sw.active = old.active) (e : Fin n ≃ old.active)
    (haff : ∀ y : Fin n → ℝ, AndersonAC.S45.neutral y →
      (1 - C' * AndersonAC.S45.power t (AndersonAC.S45.delta / 10)) *
        (θ * (toS45 old rOld e).X t y +
          (1 - θ) * (∑ i, y i ^ 2 / (toS45 old rOld e).p i ^ 2)) ≤
        (toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).X (θ * t) y ∧
      (toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).X (θ * t) y ≤
        (1 + C' * AndersonAC.S45.power t (AndersonAC.S45.delta / 10)) *
        (θ * (toS45 old rOld e).X t y +
          (1 - θ) * (∑ i, y i ^ 2 / (toS45 old rOld e).p i ^ 2)))
    (hK : ‖(toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).K (θ * t)‖ ≤
      ‖(toS45 old rOld e).K t‖ + AndersonAC.S45.power t (AndersonAC.S45.delta / 10)) :
    (∀ y, neutral old.active y →
      (1 - C' * t ^ (0.10 * delta)) * stageTarget old rOld t (θ * t) old.active y ≤
        Xof sw rOld (θ * t) y ∧
      Xof sw rOld (θ * t) y ≤ (1 + C' * t ^ (0.10 * delta)) * stageTarget old rOld t (θ * t) old.active y) ∧
    Kn sw (θ * t) ≤ Kn old t + 1 * t ^ (0.10 * delta) := by
  set e' : Fin n ≃ sw.active := e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])) with he'
  have he'v : ∀ i, (e' i).val = (e i).val := fun i => rfl
  obtain ⟨hsO, hwO⟩ := ward_of_damped old rOld t ht.le hold e
  obtain ⟨hsS, hwS⟩ := ward_of_damped sw rOld (θ * t) (by positivity) hsw e'
  refine ⟨fun y hy => ?_, ?_⟩
  · have hyS := neutral_to_S45 old.active e y hy
    obtain ⟨a1, a2⟩ := haff (fun i => y (e i).val) hyS
    have hXo : Xof old rOld t y = (toS45 old rOld e).X t (fun i => y (e i).val) :=
      inverseEnergy_eq_S45X old rOld t e hsO hwO y
    have hXs : Xof sw rOld (θ * t) y = (toS45 sw rOld e').X (θ * t) (fun i => y (e i).val) :=
      inverseEnergy_eq_S45X sw rOld (θ * t) e' hsS hwS y
    have hsum : ∑ i ∈ old.active, y i ^ 2 / (rOld i).im ^ 2 =
        ∑ i, (fun i => y (e i).val) i ^ 2 / (toS45 old rOld e).p i ^ 2 :=
      (sum_active_equiv old.active e (fun x => y x ^ 2 / (rOld x).im ^ 2)).symm
    have hT : stageTarget old rOld t (θ * t) old.active y =
        θ * (toS45 old rOld e).X t (fun i => y (e i).val) +
          (1 - θ) * (∑ i, (fun i => y (e i).val) i ^ 2 / (toS45 old rOld e).p i ^ 2) := by
      unfold stageTarget
      rw [hXo, hsum, mul_div_cancel_right₀ θ ht.ne']
    rw [hT, hXs, ← power_tenth]
    exact ⟨a1, a2⟩
  · have hzO : ∀ i j, i ∉ old.active ∨ j ∉ old.active → old.g i j = 0 := hold.2.1
    have hzS : ∀ i j, i ∉ sw.active ∨ j ∉ sw.active → sw.g i j = 0 := hsw.2.1
    rw [Kn_eq_S45 old rOld t hzO e, Kn_eq_S45 sw rOld (θ * t) hzS e', ← power_tenth, one_mul]
    exact hK

end AndersonAC.AgentS78
