import AndersonAC.AgentS78.Construction.ClearingTrial
import AndersonAC.S78Moment.Geometry

/-!
# The trial-start matrix of a clearing trial

The §6 trial on the active sites of a committed record `x` starts from `g₀ = x.endpoint.g` on
the active sites. If the record is a damped endpoint at `t` (`g = (M − t diag r)^{-1}` on the
active set, 06-clearing.tex:19–25), the trial's real matrix `M₀` at step 0 is the record's `M`
on the active sites. Also: the nearest-neighbour torus graph has degree at most `2d`.
-/

open scoped BigOperators Matrix
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Geo

open AndersonAC.S78 AndersonAC.S6 AndersonAC.AgentS78

theorem nnGraph_degree_le {d m : ℕ} (u : Torus d m) (S : Finset (Torus d m))
    (hS : ∀ v ∈ S, (nnGraph d m).Adj u v) : S.card ≤ 2 * d := by
  classical
  let f : Fin d × Bool → Torus d m := fun p =>
    if p.2 then u + OAI.Anderson.torusBasisVector p.1 else u - OAI.Anderson.torusBasisVector p.1
  have hsub : S ⊆ Finset.univ.image f := by
    intro v hv
    rcases (AndersonAC.SolS78.nnGraph_adj_iff_proof u v).mp (hS v hv) with ⟨_, i, h | h | h | h⟩
    · exact Finset.mem_image.mpr ⟨(i, true), Finset.mem_univ _, by simp [f, h]⟩
    · exact Finset.mem_image.mpr ⟨(i, false), Finset.mem_univ _, by simp [f, h]⟩
    · refine Finset.mem_image.mpr ⟨(i, false), Finset.mem_univ _, ?_⟩
      simp only [f, Bool.false_eq_true, ↓reduceIte]; rw [h]; abel
    · refine Finset.mem_image.mpr ⟨(i, true), Finset.mem_univ _, ?_⟩
      simp only [f, ↓reduceIte]; rw [h]; abel
  calc _ ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ, Fintype.card_prod, mul_comm]

variable {d m : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- At trial start the trial's real matrix is the record's `M` on the active sites. -/
theorem trial_initial_M (x : RunRecord d m) (t : ℝ)
    (hdamp : IsDampedEndpoint x.endpoint x.r t) {B : Finset (ActiveSite x)} (hB : B.Nonempty)
    {order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x))}
    (q : StoppedTrial (Ω := Ω) B t (fun _ i => x.r i) (fun _ => trialG0 x) order) (ω : Ω)
    (i j : {i // i ∈ (q.state 0 ω).active}) :
    ((q.state 0 ω).M i j : ℂ) = x.endpoint.M i.val.val j.val.val := by
  obtain ⟨_, _, hBG, hGB⟩ := hdamp
  have huniv : (q.state 0 ω).active = Finset.univ := q.initial_active ω
  let e : {i // i ∈ (q.state 0 ω).active} ≃ ActiveSite x :=
    { toFun := fun a => a.val
      invFun := fun b => ⟨b, by rw [huniv]; exact Finset.mem_univ _⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  have he : ∀ a, (e a : ActiveSite x) = a.val := fun a => rfl
  set Bm : Matrix (ActiveSite x) (ActiveSite x) ℂ :=
    x.endpoint.M.submatrix (fun i : ActiveSite x => i.val) (fun i : ActiveSite x => i.val) -
      (t : ℂ) • Matrix.diagonal (fun i : ActiveSite x => x.r i.val)
  set Gm : Matrix (ActiveSite x) (ActiveSite x) ℂ :=
    x.endpoint.g.submatrix (fun i : ActiveSite x => i.val) (fun i : ActiveSite x => i.val)
  have hGB' : Gm * Bm = 1 := hGB
  set D := dampedMatrix (q.state 0 ω).M t (fun a : {i // i ∈ (q.state 0 ω).active} => x.r a.val.val)
  have hDinv : D⁻¹ = Gm.submatrix e e := by
    ext a b
    have := q.initial_inverse ω a b
    exact this
  have hGs : Gm.submatrix e e * Bm.submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv, hGB', Matrix.submatrix_one_equiv]
  have hunitG : IsUnit (Gm.submatrix e e).det :=
    Matrix.isUnit_det_of_right_inverse hGs
  have hunitD : IsUnit D.det := by
    rw [← Matrix.isUnit_nonsing_inv_det_iff, hDinv]; exact hunitG
  have hD : D = Bm.submatrix e e := by
    calc D = D⁻¹⁻¹ := (Matrix.nonsing_inv_nonsing_inv D hunitD).symm
      _ = (Gm.submatrix e e)⁻¹ := by rw [hDinv]
      _ = Bm.submatrix e e := Matrix.inv_eq_right_inv hGs
  have hij := congrFun (congrFun hD i) j
  simp only [D, dampedMatrix, Bm, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Matrix.diagonal_apply, he] at hij
  have hdiag : (if i = j then x.r i.val.val else 0) =
      (if i.val = j.val then x.r i.val.val else 0) := by
    by_cases h : i = j
    · subst h; simp
    · have : i.val ≠ j.val := fun h' => h (Subtype.ext h')
      rw [if_neg h, if_neg this]
  rw [hdiag] at hij
  exact sub_left_injective hij

end AndersonAC.AgentS78Geo
