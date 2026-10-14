import AndersonAC.AgentS78.Construction.PhysicalIdentity

/-!
# Physical identity after installing sweep increments

When an accepted trial installs increments `v` supported on the active set and records them in
both `installed` and `endpoint.M`, the physical identity (02-state.tex:231–247) is kept, since
the Schur complement onto the active set commutes with adding a diagonal supported on it.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem activeSchur_add_diagonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (A : Finset ι) (v : ι → ℂ) (hv : ∀ i, i ∉ A → v i = 0) :
    SolS78.activeSchur (B + Matrix.diagonal v) A =
      SolS78.activeSchur B A + Matrix.diagonal (fun i : A => v i.val) := by
  have h1 : (B + Matrix.diagonal v).submatrix (fun i : A => i.val) (fun i : {i // i ∉ A} => i.val)
      = B.submatrix (fun i : A => i.val) (fun i : {i // i ∉ A} => i.val) := by
    ext i k
    have : (i : ι) ≠ k.val := fun h => k.2 (h ▸ i.2)
    simp [Matrix.diagonal_apply_ne _ this]
  have h2 : (B + Matrix.diagonal v).submatrix (fun i : {i // i ∉ A} => i.val) (fun i : A => i.val)
      = B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : A => i.val) := by
    ext i k
    have : (i : ι) ≠ k.val := fun h => i.2 (h ▸ k.2)
    simp [Matrix.diagonal_apply_ne _ this]
  have h3 : (B + Matrix.diagonal v).submatrix (fun i : {i // i ∉ A} => i.val)
      (fun i : {i // i ∉ A} => i.val) =
      B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val) := by
    ext i k
    by_cases hik : (i : ι) = k.val
    · simp [hik, hv k.val k.2]
    · simp [Matrix.diagonal_apply_ne _ hik]
  have h4 : (B + Matrix.diagonal v).submatrix (fun i : A => i.val) (fun i : A => i.val) =
      B.submatrix (fun i : A => i.val) (fun i : A => i.val) +
        Matrix.diagonal (fun i : A => v i.val) := by
    ext i k
    by_cases hik : i = k
    · subst hik; simp
    · have : (i : ι) ≠ k.val := fun h => hik (Subtype.ext h)
      simp [Matrix.diagonal_apply_ne _ this, Matrix.diagonal_apply_ne _ hik]
  unfold SolS78.activeSchur
  rw [h1, h2, h3, h4]
  abel

/-- **The physical identity is kept by installing increments supported on the active set and
recording them in `endpoint.M`.** -/
theorem physicalIdentity_add {d m : ℕ} (E : ℝ) (x y : RunRecord d m) (v : Torus d m → ℝ)
    (hx : PhysicalIdentity E x) (hact : y.endpoint.active = x.endpoint.active)
    (hM : y.endpoint.M = x.endpoint.M + Matrix.diagonal (fun i => ((v i : ℝ) : ℂ)))
    (hinst : y.installed = fun i => x.installed i + v i)
    (hv : ∀ i, i ∉ x.endpoint.active → v i = 0) : PhysicalIdentity E y := by
  unfold PhysicalIdentity at hx ⊢
  have hshift : installedShifted E y =
      installedShifted E x + Matrix.diagonal (fun i => ((v i : ℝ) : ℂ)) := by
    unfold installedShifted
    rw [hinst]
    ext i k
    by_cases hik : i = k
    · subst hik; simp; ring
    · simp [Matrix.diagonal_apply_ne _ hik]
  rw [hshift, hact, activeSchur_add_diagonal _ _ _ (fun i hi => by simp [hv i hi]), ← hx, hM]
  ext i k
  by_cases hik : i = k
  · subst hik; simp
  · have : (i : Torus d m) ≠ k.val := fun h => hik (Subtype.ext h)
    simp [Matrix.diagonal_apply_ne _ this, Matrix.diagonal_apply_ne _ hik]

end AndersonAC.AgentS78
