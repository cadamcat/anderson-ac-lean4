import AndersonAC.AgentS78.SweepJoin
import AndersonAC.AgentS78.ResetJoin

/-!
WP10: one `StageStep` from the three section results.

* sweep: the two conclusions of `S45.ordinary_sweep_endpoint` for the active blocks of
  the stage-start endpoint `old` and the post-sweep endpoint `sw` (`sweep_step`);
* assembly: an `AssemblyInput I` at the new scale with `I.state 0 = sw` and the
  `a = Fin.last k` instance of the `S78.committed_assembly` conclusion (its K bound,
  constant kernel and inverse comparison components);
* reset: `S78.diagonal_reset`'s `ResetOutput` on the active block of `I.state (last)`,
  with `‖ζ‖ ≤ t'^(.35δ)` (`reset_step`).
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem assembly_nested {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) :
    ∀ a : Fin (k + 1), (I.state a).active ⊆ (I.state 0).active := by
  intro a
  induction a using Fin.induction with
  | zero => exact le_rfl
  | succ a ih => exact (I.nested a).trans ih

theorem norm_padV_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (z : A → ℂ) :
    ‖padV A z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun i => ?_
  unfold padV
  split_ifs with hi
  · exact norm_le_pi_norm z ⟨i, hi⟩
  · simp

/-- **One stage from the section conclusions.** -/
def stage_step_of_sections {d m n k : ℕ} (old sw new : Endpoint (Torus d m)) (rOld : Torus d m → ℂ)
    (t θ b C Csw Cres : ℝ) (ht : 0 < t) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ht1 : t ≤ 1)
    (hC : 1 ≤ C) (hCsw : Csw ≤ C) (hCres0 : 0 ≤ Cres) (hCres : Cres ≤ C)
    (hsmall : C * (θ * t) ^ (0.35 * delta) < 1)
    -- sweep
    (hold : IsDampedEndpoint old rOld t) (hsw : IsDampedEndpoint sw rOld (θ * t))
    (hact : sw.active = old.active) (e : Fin n ≃ old.active)
    (haff : ∀ y : Fin n → ℝ, AndersonAC.S45.neutral y →
      (1 - Csw * AndersonAC.S45.power t (AndersonAC.S45.delta / 10)) *
        (θ * (toS45 old rOld e).X t y +
          (1 - θ) * (∑ i, y i ^ 2 / (toS45 old rOld e).p i ^ 2)) ≤
        (toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).X (θ * t) y ∧
      (toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).X (θ * t) y ≤
        (1 + Csw * AndersonAC.S45.power t (AndersonAC.S45.delta / 10)) *
        (θ * (toS45 old rOld e).X t y +
          (1 - θ) * (∑ i, y i ^ 2 / (toS45 old rOld e).p i ^ 2)))
    (hKsw : ‖(toS45 sw rOld (e.trans (Equiv.subtypeEquivRight (fun x => by rw [hact])))).K (θ * t)‖ ≤
      ‖(toS45 old rOld e).K t‖ + AndersonAC.S45.power t (AndersonAC.S45.delta / 10))
    -- assembly (the a = last instance of committed_assembly)
    (I : AssemblyInput d m k (θ * t) b rOld) (hI0 : I.state 0 = sw)
    (hAK : matrixNorm (squareKernel (normalizedInverse (I.state (Fin.last k)) (θ * t))) ≤
      matrixNorm (squareKernel (normalizedInverse (I.state 0) (θ * t))) + (θ * t) ^ (0.10 * delta))
    (hAker : constantKernel (I.state (Fin.last k)).active
      (endpointEnergy (I.state (Fin.last k)) rOld (θ * t)))
    (hAinv : ∀ y, neutral (I.state (Fin.last k)).active y →
      (1 + (θ * t) ^ (0.10 * delta))⁻¹ *
          inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) rOld (θ * t)) y ≤
        inverseEnergy (I.state (Fin.last k)).active (endpointEnergy (I.state (Fin.last k)) rOld (θ * t)) y ∧
      inverseEnergy (I.state (Fin.last k)).active (endpointEnergy (I.state (Fin.last k)) rOld (θ * t)) y ≤
        (1 - (θ * t) ^ (0.10 * delta))⁻¹ *
          inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) rOld (θ * t)) y)
    -- reset on the active block of the committed endpoint
    (MA : Matrix (I.state (Fin.last k)).active (I.state (Fin.last k)).active ℂ)
    (ζ : (I.state (Fin.last k)).active → ℂ)
    (hfg : (I.state (Fin.last k)).g = padM (I.state (Fin.last k)).active
      (resetInverse MA (fun a => rOld a.val) (θ * t)))
    (hna : new.active = (I.state (Fin.last k)).active)
    (hng : new.g = padM (I.state (Fin.last k)).active
      (resetInverse MA ((fun a => rOld a.val) + ζ) (θ * t)))
    (hR : ResetOutput MA (fun a => rOld a.val) ζ (θ * t) Cres)
    (hζ : ‖ζ‖ ≤ (θ * t) ^ (0.35 * delta))
    (hp : ∀ i ∈ (I.state (Fin.last k)).active, 0 ≤ (rOld i).im) :
    StageStep d m C t (θ * t) old new rOld (rOld + padV (I.state (Fin.last k)).active ζ) where
  sw := sw
  fin := I.state (Fin.last k)
  sw_active := hact
  sw_affine := fun y hy => by
    obtain ⟨h1, h2⟩ := (sweep_step old sw rOld t θ Csw ht hθ hold hsw hact e haff hKsw).1 y hy
    have hT0 : 0 ≤ stageTarget old rOld t (θ * t) old.active y := by
      unfold stageTarget
      have := Xof_nonneg old rOld t y
      have : 0 ≤ ∑ i ∈ old.active, y i ^ 2 / (rOld i).im ^ 2 :=
        Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
      have : (θ * t) / t = θ := mul_div_cancel_right₀ θ ht.ne'
      have : 0 ≤ 1 - θ * t / t := by linarith
      positivity
    have hpw : 0 ≤ t ^ (0.10 * delta) := Real.rpow_nonneg ht.le _
    have hmono : Csw * t ^ (0.10 * delta) ≤ C * t ^ (0.10 * delta) :=
      mul_le_mul_of_nonneg_right hCsw hpw
    constructor
    · refine le_trans ?_ h1
      exact mul_le_mul_of_nonneg_right (by linarith) hT0
    · refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hT0
  sw_K := by
    have h := (sweep_step old sw rOld t θ Csw ht hθ hold hsw hact e haff hKsw).2
    have hpw : 0 ≤ t ^ (0.10 * delta) := Real.rpow_nonneg ht.le _
    nlinarith
  fin_nested := by rw [← hI0]; exact assembly_nested I _
  fin_K := by unfold Kn; rw [← hI0]; exact hAK
  fin_inv := fun y hy => by unfold Xof; rw [← hI0]; exact hAinv y hy
  new_active := hna
  r_close := by
    rw [add_sub_cancel_left]
    exact (norm_padV_le _ ζ).trans hζ
  new_K := by
    have : Cres * ‖ζ‖ ≤ C * (θ * t) ^ (0.35 * delta) :=
      mul_le_mul hCres hζ (norm_nonneg _) (by linarith)
    have h := (reset_step _ MA rOld ζ (θ * t) Cres (I.state (Fin.last k)) new rfl hna hfg hng hR hp
      hCres0 (by linarith) hAker).2.1
    unfold Kn
    linarith
  new_inv := fun y hy => by
    have hεle : Cres * ‖ζ‖ ≤ C * (θ * t) ^ (0.35 * delta) :=
      mul_le_mul hCres hζ (norm_nonneg _) (by linarith)
    have hε0 : 0 ≤ Cres * ‖ζ‖ := mul_nonneg hCres0 (norm_nonneg _)
    obtain ⟨h1, h2⟩ := (reset_step _ MA rOld ζ (θ * t) Cres (I.state (Fin.last k)) new rfl hna hfg hng hR hp
      hCres0 (by linarith) hAker).2.2 y hy
    have hX0 := Xof_nonneg (I.state (Fin.last k)) rOld (θ * t) y
    unfold Xof at hX0 ⊢
    constructor
    · refine le_trans ?_ h1
      apply mul_le_mul_of_nonneg_right _ hX0
      exact inv_anti₀ (by linarith) (by linarith)
    · refine h2.trans ?_
      apply mul_le_mul_of_nonneg_right _ hX0
      exact inv_anti₀ (by linarith) (by linarith)

end AndersonAC.AgentS78
