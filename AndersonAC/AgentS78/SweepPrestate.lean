import AndersonAC.AgentS78.SweepJoin
import AndersonAC.AgentS78.ResetJoin

/-!
WP10: the stage-start hypotheses of `S45.ordinary_sweep_endpoint` on `old : State (Fin n)`
from a damped S78 endpoint satisfying `StageBounds`: bounded diagonal, damping range,
`g_ii = r_i`, symmetry, Ward, the S45 `constantKernel (D t)` and `‖K t‖ ≤ 1/3`.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Extension of a block potential by zero. -/
def extendFun {ι κ : Type} [DecidableEq ι] {A : Finset ι} (e : κ ≃ A) (f : κ → ℝ) : ι → ℝ :=
  fun x => if hx : x ∈ A then f (e.symm ⟨x, hx⟩) else 0

theorem extendFun_comp {ι κ : Type} [DecidableEq ι] {A : Finset ι} (e : κ ≃ A) (f : κ → ℝ) :
    (fun i => extendFun e f (e i).val) = f := by
  funext i; simp [extendFun, (e i).property]

theorem sweep_prestate {d m n n₀ k : ℕ} {u cP CP cL CL C₀ : ℝ} (old : Endpoint (Torus d m))
    (r : Torus d m → ℂ) (hcP : 0 < cP)
    (hD : IsDampedEndpoint old r (stageScale u k m)) (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1)
    (e : Fin n ≃ old.active)
    (hSB : StageBounds d m n₀ k u cP CP cL CL C₀ old r) :
    let oS := toS45 old r e
    (∀ i, ‖oS.r i‖ ≤ max CP (1 / cP) ∧ 1 / max CP (1 / cP) ≤ oS.p i ∧ oS.p i ≤ max CP (1 / cP)) ∧
    (∀ i, oS.g i i = oS.r i) ∧ oS.g.IsSymm ∧ oS.ward (stageScale u k m) ∧
    AndersonAC.S45.constantKernel (oS.D (stageScale u k m)) ∧
    ‖oS.K (stageScale u k m)‖ ≤ 1 / 3 := by
  intro oS
  have ht : 0 < stageScale u k m := stageScale_pos' hu k m
  unfold StageBounds at hSB
  dsimp only at hSB
  obtain ⟨hdiag, -, hK, hker, -, -, -⟩ := hSB
  obtain ⟨hsym, hward⟩ := ward_of_damped old r _ ht.le hD e
  have hCm : CP ≤ max CP (1 / cP) := le_max_left _ _
  have hcm : 1 / max CP (1 / cP) ≤ cP := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) (le_max_right _ _))]
    nlinarith [le_max_right CP (1 / cP), mul_div_cancel₀ (1 : ℝ) hcP.ne']
  refine ⟨fun i => ?_, fun i => (hdiag _ (e i).property).1, hsym, hward, ?_, ?_⟩
  · obtain ⟨-, h1, h2, h3⟩ := hdiag _ (e i).property
    exact ⟨h3.trans hCm, hcm.trans h1, h2.trans hCm⟩
  · -- S45 constant kernel of D from the S78 kernel and Ward
    have hrel : ∀ f : Fin n → ℝ, AndersonAC.S45.qform (oS.D (stageScale u k m)) f =
        endpointEnergy old r (stageScale u k m) (extendFun e f) := by
      intro f
      rw [endpointEnergy_eq_S45 old r _ e hsym hward, extendFun_comp]
    refine ⟨?_, fun f => ?_, fun f => ?_⟩
    · -- symmetry of D
      ext i j
      have hg : ∀ a b, oS.g b a = oS.g a b := by
        intro a b; have := congrFun (congrFun hsym a) b; simpa [Matrix.transpose_apply] using this
      simp only [Matrix.transpose_apply, AndersonAC.S45.State.D, Matrix.sub_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare,
        AndersonAC.S45.State.h, Matrix.smul_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij; rfl
      · simp [hij, Ne.symm hij, hg i j]
        ring
    · rw [hrel]
      unfold endpointEnergy
      exact wardEnergy_nonneg _ _ (fun i hi => (le_trans (by linarith) (hdiag i hi).2.1)) _ _
    · rw [hrel]
      constructor
      · intro h0
        obtain ⟨c, hc⟩ := (hker _).mp h0
        refine ⟨c, fun i => ?_⟩
        have := hc (e i).val (e i).property
        rwa [show extendFun e f (e i).val = f i from congrFun (extendFun_comp e f) i] at this
      · rintro ⟨c, hc⟩
        refine (hker _).mpr ⟨c, fun x hx => ?_⟩
        simp [extendFun, hx, hc]
  · rw [← Kn_eq_S45 old r _ hD.2.1 e]
    exact hK

end AndersonAC.AgentS78
