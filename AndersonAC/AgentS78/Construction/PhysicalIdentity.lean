import AndersonAC.AgentS78.Construction.FinalCertificate

/-!
# WP10 construction, C5b/C5d: the physical identity of a committed record

02-state.tex:231–247: the committed matrix is the Schur complement, onto the active set,
of `H − E` with the *installed* potential values (partial on active sites, exact true values
on terminal sites). `PhysicalIdentity E x` is this record invariant, to be maintained by
every block. Once the final residual sweep has installed the true potentials everywhere
(`installed = λ · V`), it is the `TrueSchurIdentity` used by `certificate_of_final_record`
(`trueSchurIdentity_of_physical`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The zero configuration (only used to extract the hopping part). -/
def zeroConfig (d m : ℕ) : OAI.Anderson.TorusConfiguration d m :=
  fun _ => ⟨0, by norm_num, by norm_num⟩

/-- `H − E` with the installed potential values of the record. -/
def installedShifted (E : ℝ) (x : RunRecord d m) : Matrix (Torus d m) (Torus d m) ℂ :=
  OAI.Anderson.periodicHamiltonian 0 (zeroConfig d m) +
    Matrix.diagonal (fun i => ((x.installed i : ℝ) : ℂ)) - (E : ℂ) • 1

/-- **Physical identity** of a committed record (02-state.tex:231–247). -/
def PhysicalIdentity (E : ℝ) (x : RunRecord d m) : Prop :=
  x.endpoint.M.submatrix (fun i : x.endpoint.active => i.val)
      (fun i : x.endpoint.active => i.val) =
    SolS78.activeSchur (installedShifted E x) x.endpoint.active

theorem installedShifted_eq_true (n₀ : ℕ) (u E : ℝ) (ω : OAI.Anderson.TorusConfiguration d m)
    (x : RunRecord d m)
    (hinst : ∀ i, x.installed i = OAI.Anderson.scaleCoupling n₀ u * (ω i : ℝ)) :
    installedShifted E x = trueShifted n₀ u E ω := by
  ext i j
  simp only [installedShifted, trueShifted, Matrix.sub_apply, Matrix.add_apply,
    OAI.Anderson.periodicHamiltonian, Matrix.diagonal_apply, hinst]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- After the final residual sweep the physical identity is the true Schur identity. -/
theorem trueSchurIdentity_of_physical (n₀ : ℕ) (u E : ℝ) (ω : OAI.Anderson.TorusConfiguration d m)
    (x : RunRecord d m)
    (hinst : ∀ i, x.installed i = OAI.Anderson.scaleCoupling n₀ u * (ω i : ℝ))
    (hphys : PhysicalIdentity E x) : TrueSchurIdentity n₀ u E ω x.endpoint := by
  unfold TrueSchurIdentity
  rw [hphys, installedShifted_eq_true n₀ u E ω x hinst]

end AndersonAC.AgentS78
