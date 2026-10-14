import AndersonAC.S78.PhysicalCertificate
import AndersonAC.AgentS78.Construction.Record

/-!
# WP10 construction, C5d glue: the certificate from the final record

08-history.tex:370–394. After the final residual sweep the active potentials are the true
ones, so the committed matrix is the Schur complement of the true `H_m − E` onto the active
set (`TrueSchurIdentity`), its inverse is the damped endpoint at the final damping
`η = scaleHeight m u`, and the terminal block is invertible off a null set.
`certificate_of_final_record` gives membership in the bounded certificate event, through
sol-s78's `bounded_certificate_of_final_endpoint`: the damping term `η diag_A r` only
changes the active block, so the active Schur complement of the certificate matrix is the
committed matrix minus `η diag r`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The undamped true matrix `H_m − E` at coupling `scaleCoupling n₀ u`. -/
def trueShifted (n₀ : ℕ) (u E : ℝ) (ω : OAI.Anderson.TorusConfiguration d m) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  OAI.Anderson.periodicHamiltonian (OAI.Anderson.scaleCoupling n₀ u) ω - (E : ℂ) • 1

/-- The committed active matrix is the Schur complement of the true `H_m − E`. -/
def TrueSchurIdentity (n₀ : ℕ) (u E : ℝ) (ω : OAI.Anderson.TorusConfiguration d m)
    (s : Endpoint (Torus d m)) : Prop :=
  s.M.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) =
    SolS78.activeSchur (trueShifted n₀ u E ω) s.active

theorem certificateMatrix_eq (n₀ : ℕ) (u E : ℝ) (ω : OAI.Anderson.TorusConfiguration d m)
    (A : Finset (Torus d m)) (r : Torus d m → ℂ) :
    OAI.Anderson.certificateMatrix n₀ m u E ω A r =
      trueShifted n₀ u E ω - (OAI.Anderson.scaleHeight m u : ℂ) • OAI.Anderson.diagonalOn A r := rfl

/-- **The certificate from the final record.** -/
theorem certificate_of_final_record (n₀ : ℕ) (u E Cr cp cg : ℝ)
    (ω : OAI.Anderson.TorusConfiguration d m) (s : Endpoint (Torus d m)) (r : Torus d m → ℂ)
    (hs : IsDampedEndpoint s r (OAI.Anderson.scaleHeight m u))
    (hphys : TrueSchurIdentity n₀ u E ω s)
    (hcard : Fintype.card (Torus d m) ≤ 2 * s.active.card)
    (hr : ∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im)
    (hlag : ∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)
    (hT : IsUnit ((trueShifted n₀ u E ω).submatrix
      (fun i : {i // i ∉ s.active} => i.val) (fun i : {i // i ∉ s.active} => i.val)).det) :
    ω ∈ boundedCertificateEvent d n₀ m u E Cr cp cg := by
  classical
  set A := s.active
  set B := trueShifted n₀ u E ω
  set C := OAI.Anderson.certificateMatrix n₀ m u E ω A r
  set η : ℂ := (OAI.Anderson.scaleHeight m u : ℂ)
  have hC : ∀ i j, C i j = B i j - η * (if i = j then (if i ∈ A then r i else 0) else 0) := by
    intro i j
    simp only [C, B, η, certificateMatrix_eq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      OAI.Anderson.diagonalOn, Matrix.diagonal_apply]
  have hTT : C.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val) =
      B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val) := by
    ext i j
    simp only [Matrix.submatrix_apply, hC, if_neg i.property]
    simp
  have hAT : C.submatrix (fun i : A => i.val) (fun i : {i // i ∉ A} => i.val) =
      B.submatrix (fun i : A => i.val) (fun i : {i // i ∉ A} => i.val) := by
    ext i j
    have : i.val ≠ j.val := fun h => j.property (h ▸ i.property)
    simp only [Matrix.submatrix_apply, hC, if_neg this]
    simp
  have hTA : C.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : A => i.val) =
      B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : A => i.val) := by
    ext i j
    have : i.val ≠ j.val := fun h => i.property (h ▸ j.property)
    simp only [Matrix.submatrix_apply, hC, if_neg this]
    simp
  have hAA : C.submatrix (fun i : A => i.val) (fun i : A => i.val) =
      B.submatrix (fun i : A => i.val) (fun i : A => i.val) -
        η • Matrix.diagonal (fun i : A => r i.val) := by
    ext i j
    simp only [Matrix.submatrix_apply, hC, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [i.property]
    · have : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [hij, this]
  refine SolS78.bounded_certificate_of_final_endpoint d n₀ m u E Cr cp cg
    (OAI.Anderson.scaleHeight m u) ω s r hs hcard hr hlag (by rw [hTT]; exact hT) ?_
  have hphys' := hphys
  unfold TrueSchurIdentity at hphys'
  unfold SolS78.activeSchur at hphys' ⊢
  rw [hTT, hAT, hTA, hAA, hphys']
  abel

end AndersonAC.AgentS78
